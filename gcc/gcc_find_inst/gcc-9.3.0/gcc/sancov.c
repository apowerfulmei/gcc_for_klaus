/* Code coverage instrumentation for fuzzing.
   Copyright (C) 2015-2019 Free Software Foundation, Inc.
   Contributed by Dmitry Vyukov <dvyukov@google.com> and
   Wish Wu <wishwu007@gmail.com>

This file is part of GCC.

GCC is free software; you can redistribute it and/or modify it under
the terms of the GNU General Public License as published by the Free
Software Foundation; either version 3, or (at your option) any later
version.

GCC is distributed in the hope that it will be useful, but WITHOUT ANY
WARRANTY; without even the implied warranty of MERCHANTABILITY or
FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
for more details.

You should have received a copy of the GNU General Public License
along with GCC; see the file COPYING3.  If not see
<http://www.gnu.org/licenses/>.  */

#include "config.h"
#include "system.h"
#include "coretypes.h"
#include "backend.h"
#include "tree.h"
#include "gimple.h"
#include "basic-block.h"
#include "options.h"
#include "flags.h"
#include "memmodel.h"
#include "tm_p.h"
#include "stmt.h"
#include "gimple-iterator.h"
#include "gimple-builder.h"
#include "gimple-walk.h"
#include "gimple-pretty-print.h"
#include "print-tree.h"
#include "tree-cfg.h"
#include "tree-pass.h"
#include "tree-iterator.h"
#include "fold-const.h"
#include "stringpool.h"
#include "attribs.h"
#include "output.h"
#include "cgraph.h"
#include "asan.h"
#include "unistd.h"
#include <assert.h>
#include <dirent.h>
#include <sys/types.h>


namespace {

#define MAX_STRUCT_NAME 0x100
#define MAX_FILE_NAME   0x300
#define MAP_BLOCK       0x10
// #define DEBUG
//#define DEBUG 1
#ifdef DEBUG
#define gcc_log(fmt, ...) fprintf(stderr, fmt, ##__VA_ARGS__)
#else
#define gcc_log(fmt, ...) (0)
#endif

struct st {
  struct st *next;
  int field;
  char name[];
};

enum INST_STATE {
  PRE_INST,
  POST_INST,
  PROP_INST,
  VAL_INST,
  COND_INST,
};

struct tree_cb {
  struct walk_stmt_info info;
  unsigned int flag;
  unsigned long long data;
};

struct cond {
  struct cond *next;
  char *funcname;
  char *filename;
  int line;
  unsigned idx;
  struct st st;
};

struct prop_list {
  struct prop_list *next;
  char *funcname;
  char *filename;
  int line;
  unsigned idx;
  struct st *pre;
  struct st *post;
};

struct distance_list{
  struct distance_list * next;
  char * filename;
  struct func_list * funcs;

};

struct func_list{
  struct func_list *next;
  char * funcname;
  int maxIdx;
  unsigned int dis[10000];
};

struct cond *cond_list = NULL;
struct prop_list *p_list = NULL;
struct distance_list* d_list=NULL;
static unsigned prop_idx = 1;



//查找对应的file
static struct distance_list *lookup_file(const char *filename) {
  struct distance_list *cur = d_list;
  while (cur!=NULL) {
    if (!strcmp(cur->filename, filename)) {
      return cur;
    }
    cur = cur->next;
  }
  return cur;
}

//查找对应func的BB距离列表
static struct func_list *lookup_distance(struct func_list *funcs,const char *funcname) {
  struct func_list *cur = funcs;
  while (cur!=NULL) {
    if (!strcmp(cur->funcname,funcname)) {
      return cur;
    }
    cur = cur->next;
  }
  return cur;
}

static struct cond *lookup_cond(struct cond *c, const char *name, int field) {
  struct cond *cond = c ? c : cond_list;
  while (cond) {
    if (!strcmp(cond->st.name, name) && cond->st.field == field) {
      return cond;
    }
    cond = cond->next;
  }
  return cond;
}

static struct st *lookup_struct(struct st * s, const char *name, int field) {
  struct st *cur = s;
  while (cur) {
    if (!strcmp(name, cur->name) && cur->field == field) {
      return cur;
    }
    cur = cur->next;
  }
  return cur;
}

static unsigned lookup_prop_st(const char *name, int field) {
  struct prop_list *p = p_list;
  while (p) {
    if (lookup_struct(p->pre, name, field)) {
      return (p->idx << 8 | 1);
    }
    if (lookup_struct(p->post, name, field)) {
      return (p->idx << 8 | 2);
    }
    p = p->next;
  }
  return 0;
}

static prop_list* lookup_prop(const char *file, int line) {
  if (file == NULL) return 0;

  struct prop_list *p = p_list;
  while (p) {
    if (!strcmp(p->filename, file) && p->line == line) {
      return p;
    }
    p = p->next;
  }
  return NULL;
}

/* Instrument one comparison operation, which compares lhs and rhs.
   Call the instrumentation function with the comparison operand.
   For integral comparisons if exactly one of the comparison operands is
   constant, call __sanitizer_cov_trace_const_cmp* instead of
   __sanitizer_cov_trace_cmp*.  */

static void
instrument_comparison (gimple_stmt_iterator *gsi, tree lhs, tree rhs)
{
  tree type = TREE_TYPE (lhs);
  enum built_in_function fncode = END_BUILTINS;
  tree to_type = NULL_TREE;
  bool c = false;

  if (INTEGRAL_TYPE_P (type))
    {
      c = (is_gimple_min_invariant (lhs)
	   ^ is_gimple_min_invariant (rhs));
      switch (int_size_in_bytes (type))
	{
	case 1:
      	  fncode = c ? BUILT_IN_SANITIZER_COV_TRACE_CONST_CMP1
		     : BUILT_IN_SANITIZER_COV_TRACE_CMP1;
	  to_type = unsigned_char_type_node;
	  break;
	case 2:
      	  fncode = c ? BUILT_IN_SANITIZER_COV_TRACE_CONST_CMP2
		     : BUILT_IN_SANITIZER_COV_TRACE_CMP2;
	  to_type = uint16_type_node;
	  break;
	case 4:
      	  fncode = c ? BUILT_IN_SANITIZER_COV_TRACE_CONST_CMP4
		     : BUILT_IN_SANITIZER_COV_TRACE_CMP4;
	  to_type = uint32_type_node;
	  break;
	default:
      	  fncode = c ? BUILT_IN_SANITIZER_COV_TRACE_CONST_CMP8
		     : BUILT_IN_SANITIZER_COV_TRACE_CMP8;
	  to_type = uint64_type_node;
	  break;
	}
    }
  else if (SCALAR_FLOAT_TYPE_P (type))
    {
      if (TYPE_MODE (type) == TYPE_MODE (float_type_node))
	{
      	  fncode = BUILT_IN_SANITIZER_COV_TRACE_CMPF;
	  to_type = float_type_node;
	}
      else if (TYPE_MODE (type) == TYPE_MODE (double_type_node))
	{
      	  fncode = BUILT_IN_SANITIZER_COV_TRACE_CMPD;
	  to_type = double_type_node;
	}
    }

  if (to_type != NULL_TREE)
    {
      gimple_seq seq = NULL;

      if (!useless_type_conversion_p (to_type, type))
	{
	  if (TREE_CODE (lhs) == INTEGER_CST)
	    lhs = fold_convert (to_type, lhs);
	  else
	    {
	      gimple_seq_add_stmt (&seq, build_type_cast (to_type, lhs));
	      lhs = gimple_assign_lhs (gimple_seq_last_stmt (seq));
	    }

	  if (TREE_CODE (rhs) == INTEGER_CST)
	    rhs = fold_convert (to_type, rhs);
	  else
	    {
	      gimple_seq_add_stmt (&seq, build_type_cast (to_type, rhs));
	      rhs = gimple_assign_lhs (gimple_seq_last_stmt (seq));
	    }
	}

      if (c && !is_gimple_min_invariant (lhs))
	std::swap (lhs, rhs);

      tree fndecl = builtin_decl_implicit (fncode);
      gimple *gcall = gimple_build_call (fndecl, 2, lhs, rhs);
      gimple_seq_add_stmt (&seq, gcall);

      gimple_seq_set_location (seq, gimple_location (gsi_stmt (*gsi)));
      gsi_insert_seq_before (gsi, seq, GSI_SAME_STMT);
    }
}

/* Instrument switch statement.  Call __sanitizer_cov_trace_switch with
   the value of the index and array that contains number of case values,
   the bitsize of the index and the case values converted to uint64_t.  */

static void
instrument_switch (gimple_stmt_iterator *gsi, gimple *stmt, function *fun)
{
  gswitch *switch_stmt = as_a<gswitch *> (stmt);
  tree index = gimple_switch_index (switch_stmt);
  HOST_WIDE_INT size_in_bytes = int_size_in_bytes (TREE_TYPE (index));
  if (size_in_bytes == -1 || size_in_bytes > 8)
    return;

  location_t loc = gimple_location (stmt);
  unsigned i, n = gimple_switch_num_labels (switch_stmt), num = 0;
  for (i = 1; i < n; ++i)
    {
      tree label = gimple_switch_label (switch_stmt, i);

      tree low_case = CASE_LOW (label);
      if (low_case != NULL_TREE)
	num++;

      tree high_case = CASE_HIGH (label);
      if (high_case != NULL_TREE)
	num++;
    }

  tree case_array_type
   = build_array_type (build_type_variant (uint64_type_node, 1, 0),
		       build_index_type (size_int (num + 2 - 1)));

  char name[64];
  static size_t case_array_count = 0;
  ASM_GENERATE_INTERNAL_LABEL (name, "LCASEARRAY", case_array_count++);
  tree case_array_var = build_decl (loc, VAR_DECL, get_identifier (name),
				    case_array_type);
  TREE_STATIC (case_array_var) = 1;
  TREE_PUBLIC (case_array_var) = 0;
  TREE_CONSTANT (case_array_var) = 1;
  TREE_READONLY (case_array_var) = 1;
  DECL_EXTERNAL (case_array_var) = 0;
  DECL_ARTIFICIAL (case_array_var) = 1;
  DECL_IGNORED_P (case_array_var) = 1;

  vec <constructor_elt, va_gc> *v = NULL;
  vec_alloc (v, num + 2);
  CONSTRUCTOR_APPEND_ELT (v, NULL_TREE,
			  build_int_cst (uint64_type_node, num));
  CONSTRUCTOR_APPEND_ELT (v, NULL_TREE,
			  build_int_cst (uint64_type_node,
					 size_in_bytes * BITS_PER_UNIT));
  for (i = 1; i < n; ++i)
    {
      tree label = gimple_switch_label (switch_stmt, i);

      tree low_case = CASE_LOW (label);
      if (low_case != NULL_TREE)
	CONSTRUCTOR_APPEND_ELT (v, NULL_TREE,
				fold_convert (uint64_type_node, low_case));

      tree high_case = CASE_HIGH (label);
      if (high_case != NULL_TREE)
	CONSTRUCTOR_APPEND_ELT (v, NULL_TREE,
				fold_convert (uint64_type_node, high_case));
    }
  tree ctor = build_constructor (case_array_type, v);
  TREE_STATIC (ctor) = 1;
  TREE_PUBLIC (ctor) = 0;
  TREE_CONSTANT (ctor) = 1;
  TREE_READONLY (ctor) = 1;
  DECL_INITIAL (case_array_var) = ctor;
  varpool_node::finalize_decl (case_array_var);
  add_local_decl (fun, case_array_var);

  gimple_seq seq = NULL;

  if (!useless_type_conversion_p (uint64_type_node, TREE_TYPE (index)))
    {
      if (TREE_CODE (index) == INTEGER_CST)
	index = fold_convert (uint64_type_node, index);
      else
	{
	  gimple_seq_add_stmt (&seq, build_type_cast (uint64_type_node, index));
	  index = gimple_assign_lhs (gimple_seq_last_stmt (seq));
	}
    }

  tree fndecl = builtin_decl_implicit (BUILT_IN_SANITIZER_COV_TRACE_SWITCH);
  gimple *gcall = gimple_build_call (fndecl, 2, index,
				     build_fold_addr_expr (case_array_var));
  gimple_seq_add_stmt (&seq, gcall);

  gimple_seq_set_location (seq, loc);
  gsi_insert_seq_before (gsi, seq, GSI_SAME_STMT);
}
void replace_char(char * filename)
{
  int len=strlen(filename);
  int i=0;
  for(i=0;i<len-5;i++)
  {
    if(filename[i]=='-')
      filename[i]='/';
  }
  filename[i]='\0';
  return;
}
void load_distance()
{
  //gcc_log("=========load distance message=========\n");
  //加载distance信息
  char *dist_dir = getenv("DIST_DIR");
  if(dist_dir)
  {
    struct dirent *entry;
    DIR *dp = opendir(dist_dir);  
    if(dp==NULL)
    {
      printf("Cannot open $DIST_DIR");
      assert (false);
    }  
    //遍历dist_dir下的所有文件
    char filename[MAX_FILE_NAME] = {};
    char funcname[MAX_FILE_NAME] = {};
    char pathname[800] = {};
    int blockIdx;
    unsigned int distance;
    int oldIdx;
    while ((entry = readdir(dp)) != NULL) {
        //获取filename
        strcpy(filename,entry->d_name);
        sprintf(pathname,"%s/%s",dist_dir,filename);

        // Skip "." and ".." entries
        if (strcmp(entry->d_name, ".") == 0 || strcmp(entry->d_name, "..") == 0)
            continue;
        FILE * fp=fopen(pathname,"r");
        if(fp==NULL)
        {
        printf("File not exist\n");
        assert (false);
        }  
        //对filename做处理，将文件名中的-替换为/,同时去掉.dist后缀
        replace_char(filename);
        //查看file是否已保存在distance_list中
        struct distance_list * dist=lookup_file(filename);
        //printf("find dist %s\n",dist->filename);
        if(!dist)
        {
          
          dist= (struct distance_list *)xmalloc(sizeof(*dist));
          dist->filename = xstrdup(filename);
          dist->funcs = NULL;
          dist->next=d_list;
          d_list=dist;
        }
        while (1)
        {
          oldIdx=blockIdx+1;
          fscanf(fp, "%s %d %u\n", funcname, &blockIdx, &distance);
          if (strlen(funcname) == 0)
            break;
          //查看func是否已保存
          struct func_list*func=lookup_distance(dist->funcs,funcname);
          if(!func){
            //如果函数信息未保存
            struct func_list *f=(struct func_list *)xmalloc(sizeof(*f));
            f->funcname = xstrdup(funcname);
            //将空白区间的距离变为-1
            while(oldIdx<blockIdx)
            {
              f->dis[blockIdx]=-1;
              oldIdx++;
            }
            f->dis[blockIdx]=distance;
            f->maxIdx=blockIdx;
            f->next=dist->funcs;
            dist->funcs=f;
          

          }else{
            func->maxIdx=blockIdx;
            func->dis[blockIdx]=distance;
          }


          memset(funcname, 0, sizeof(func));

        }
        fclose(fp);
        memset(filename,0,sizeof(filename));
        memset(pathname,0,sizeof(pathname));
    }

    closedir(dp);
  }
}

void init_structs()
{
  char *cond_file = getenv("COND_FILE");
  char *prop_file = getenv("PROP_FILE");
  if (cond_file && prop_file)
  {
    FILE *fp = fopen(cond_file, "r");
    if (fp == NULL) {
      printf("Cannot open $OBJ_FILE");
      assert (false);
    }

    char buf[MAX_STRUCT_NAME] = {};
    char filename[MAX_FILE_NAME] = {};
    char func[MAX_FILE_NAME] = {};
    int field = -1, line = 0;
    while (1)
    {
      fscanf(fp, "%s %d %s %d %s\n", buf, &field, filename, &line, func);
      if (strlen(buf) == 0 || strlen(func) == 0)
        break;

      gcc_log("init the pair %s %d %s\n", buf, field, func);

      if (!lookup_cond(NULL, buf, field)) {
        gcc_log("adding object %s:%d at %s:%d\n", buf, field, filename, line);
        // insert the pair
        struct cond *c = (struct cond *)xmalloc(sizeof(*c) + strlen(buf)+1);
        static unsigned cond_idx = 1;
        c->funcname = xstrdup(func);
        c->filename = xstrdup(filename);
        c->line = line;
        c->idx = cond_idx++;
        c->st.field = field;
        strcpy(c->st.name, buf);
        c->next = cond_list;
        cond_list = c;
      }

      field = 0;
      line = 0;
      memset(buf, 0, sizeof(buf));
      memset(func, 0, sizeof(func));
      memset(filename, 0, sizeof(filename));
    }
    fclose(fp);

    gcc_log("loading prop file\n");

    fp = fopen(prop_file, "r");
    if (fp == NULL) {
      printf("Cannot open %s\n", prop_file);
      assert(false);
    }

    while (1) {
      memset(filename, 0, sizeof(filename));
      memset(func, 0, sizeof(func));
      fscanf(fp, "%s %d %s", filename, &line, func);
      if (strlen(filename) == 0 && strlen(func) == 0)
        break;

      gcc_log("adding new set %s %d %s\n", filename, line, func);
      struct prop_list *p = lookup_prop(filename, line);
      //id就是set的编号
      if (!p) {
        p = (struct prop_list *)xmalloc(sizeof(*p));
        p->funcname = xstrdup(func);
        p->filename = xstrdup(filename);
        p->line = line;
        p->idx = prop_idx++;
        p->pre = p->post = NULL;
        p->next = p_list;
        p_list = p;
      }

      // load pre
      while (1) {
        memset(buf, 0, sizeof(buf));
        fscanf(fp, "%s %d", buf, &field);
	      // a struct name never starts with -
        if (strlen(buf) == 0 || buf[0] == '-')
          break;

        gcc_log("loading pre %s %d\n", buf, field);
        if (!lookup_struct(p->pre, buf, field)) {
          struct st *s = (struct st *)xmalloc(sizeof(*s) + strlen(buf)+1);
          s->field = field;
          strcpy(s->name, buf);
          s->next = p->pre;
          p->pre = s;
        }
      }
      // load post
      while (1) {
        memset(buf, 0, sizeof(buf));
        fscanf(fp, "%s %d\n", buf, &field);
        if (strlen(buf) == 0 || buf[0] == '-')
          break;

        gcc_log("loading post %s %d\n", buf, field);
        if (!lookup_struct(p->post, buf, field)) {
          struct st *s = (struct st *)xmalloc(sizeof(*s) + strlen(buf)+1);
          s->field = field;
          strcpy(s->name, buf);
          s->next = p->post;
          p->post = s;
        }
      }
    }
    gcc_log("done with load prop\n\n");
    fclose(fp);
  }
}

tree process_tree(tree t, void *cb)
{
  if (t == NULL_TREE)
    return NULL;

#ifdef DEBUG
  static int id = 0;
  gcc_log("\n\nid : %d ", id++);
  debug_tree(t);
#endif
  
  if (TREE_CODE(t) == COMPONENT_REF) {
    tree op0 = TREE_OPERAND(t, 0);
    tree op1 = TREE_OPERAND(t, 1);

    bool mem_ref = false;
    if (TREE_CODE(op0) == MEM_REF) {
      mem_ref = true;
    } else if (TREE_CODE(op0) == VAR_DECL) {
      
    } else if (TREE_CODE(op0) == COMPONENT_REF) {

    } else {
      // fprintf(stderr, "Unknown tree code %d", TREE_CODE(op0));
      // assert(false);
    }

    const char *type_name, *field_name;
    int field_offset = -1;
    tree type = TREE_TYPE(op0);
    struct tree_cb *tree_cb = (struct tree_cb*)(cb);
    struct cond *cond;
    if (TREE_CODE(type) != RECORD_TYPE) {
	goto out;
    }
    assert(TREE_CODE(type) == RECORD_TYPE);
    type_name = field_name = NULL;

    if (TYPE_IDENTIFIER(type) != NULL_TREE) {
      type_name = IDENTIFIER_POINTER(TYPE_IDENTIFIER(type));
      gcc_log("got typename: %s\n", type_name);
    }

    if (type_name == NULL) {
      goto out;
    }

    assert(TREE_CODE(op1) == FIELD_DECL);
    if (DECL_FIELD_OFFSET(op1)) {
      gcc_log("offset 1 %d offset 2 %d\n", TREE_INT_CST_LOW(DECL_FIELD_OFFSET(op1)), TREE_INT_CST_LOW(DECL_FIELD_BIT_OFFSET (op1)));
      field_offset = TREE_INT_CST_LOW(DECL_FIELD_OFFSET(op1));
      field_offset += TREE_INT_CST_LOW(DECL_FIELD_BIT_OFFSET (op1))/8;
    }

    cond = lookup_cond(NULL, type_name, field_offset);
    if (cond == NULL) {
      // check if pre or post inst
      gcc_log("didn't found cond, looking for prop %s %d\n", type_name, field_offset);
      unsigned res = lookup_prop_st(type_name, field_offset);
      gcc_log("got res %d\n", res);
      if (res) {
        tree_cb->flag = PROP_INST;
        tree_cb->data = (unsigned long long)res;
        return t;
      }
    } else {
      gcc_log("found cond pair: %s:%d\n", type_name, field_offset);
      tree_cb->flag = COND_INST;

      if (INTEGRAL_TYPE_P(TREE_TYPE(op1))) {
        gcc_log("this is integer at %s %d\n", EXPR_FILENAME(t), EXPR_LINENO(t));
        gcc_log("cond location : %s:%d\n", cond->filename, cond->line);
        if (EXPR_FILENAME(t) != NULL && !strcmp(cond->filename, EXPR_FILENAME(t))
            && cond->line == EXPR_LINENO(t)) {
          gcc_log("got value feedback point\n");
          tree_cb->flag = VAL_INST;
          tree_cb->data = (unsigned long long)cond->idx;
        }
      }
      return t;
    }
  }

out:
  return process_tree(TREE_TYPE(t), cb);
}

tree find_st(tree *t, int *walk_subtrees, void *cb_data)
{
  *walk_subtrees = 1;
  if (!cond_list && !p_list) {
	  gcc_log("cond list or p list is not inited\n");
	  return NULL;
  }
  return process_tree(*t, cb_data);
}

unsigned
sancov_pass (function *fun)
{
  const char* funcname = "unknown";
  const char* filename = "unknown";
  tree fndecl = cfun->decl;
  if (DECL_NAME(fndecl)) {
    funcname = IDENTIFIER_POINTER(DECL_NAME(fndecl));
    filename = DECL_SOURCE_FILE(fndecl);
  }
  initialize_sanitizer_builtins ();
  // get output file name from env
  char *output_file = getenv("OUTPUT_FILE");
  char cwd[256];
  /* Insert callback into beginning of every BB. */
  //   FILE *fp = fopen(output_file, "a");
  // if (fp == NULL) {
  //   fprintf(stderr, "Cannot open %s\n", output_file);
  //   assert(false);
  // }
  // fprintf(fp, "DISTANCE:%s %s\n", filename, funcname);
  //     struct distance_list *d=d_list;

  //   while(d)
  //   {
  //       struct func_list *f=d->funcs;
  //       printf("filename %s",d->filename);
  //       while(f)
  //       {
  //           fprintf(fp,"record:%s %s\n",d->filename,f->funcname);
  //           f=f->next;
  //       }
  //       d=d->next;
  //   }
  // fclose(fp);
  if (flag_sanitize_coverage & SANITIZE_COV_TRACE_PC)
    {
      basic_block bb;
      tree raw_fndecl = builtin_decl_implicit (BUILT_IN_SANITIZER_COV_TRACE_PC);
      tree obj_fndecl = builtin_decl_implicit (BUILT_IN_SANITIZER_OBJ_COV_TRACE_PC);
      tree fndecl;
     
      //插入distance相关逻辑
      //distance不存在时，插入距离-1
      struct distance_list *dist=lookup_file(filename);
      struct func_list *func;
      if(dist!=NULL){
        func=lookup_distance(dist->funcs,funcname);
      }else{
        func=NULL;
      }
      int blockIdx=0;
      FOR_EACH_BB_FN (bb,fun)
      {
        unsigned int distance=-1;
        if(func!=NULL && func->maxIdx>=blockIdx)
          distance = func->dis[blockIdx];

        gimple_stmt_iterator gsi = gsi_start_nondebug_after_labels_bb (bb);
        if (gsi_end_p (gsi))
          continue;
        gimple *stmt = gsi_stmt (gsi);
        tree fndecl_dist = builtin_decl_implicit(BUILT_IN_SANITIZER_DIST_TRACE);
        tree dist_tree = build_int_cstu(unsigned_type_node, distance);
        //创建调用，声明，变量数量，变量值
        gimple *gcall_dist = gimple_build_call(fndecl_dist, 1, dist_tree);
        gimple_set_location (gcall_dist, gimple_location (stmt));
        gsi_insert_before (&gsi, gcall_dist, GSI_SAME_STMT);
        gcc_log("Insert distance %s% s %d %d\n",filename,funcname,blockIdx,distance);
        blockIdx++;
      }


      FOR_EACH_BB_FN (bb, fun)
	{
	  gimple_stmt_iterator gsi = gsi_start_nondebug_after_labels_bb (bb);
	  if (gsi_end_p (gsi))
	    continue;
	  gimple *stmt = gsi_stmt (gsi);

    gimple_stmt_iterator gsi_end = gsi_last_nondebug_bb(bb);
    gimple *stmt_end = gsi_stmt(gsi_end);
    if (stmt_end == NULL)
      continue;

	  fndecl = raw_fndecl;
    bool insert_cond_inst = false;
    
    for (gimple_stmt_iterator gsi_ = gsi_start_bb (bb); !gsi_end_p (gsi_); gsi_next (&gsi_)) {
      gimple * stmt_ = gsi_stmt(gsi_);
#ifdef DEBUG
      static int ii = 0;
      fprintf(stderr, "stmt %d\n", ii++);
      debug(stmt_);
      gcc_log("file %s:%d\n", gimple_filename(stmt_), gimple_lineno(stmt_));
      fprintf(stderr, "stmt debug done\n");
#endif
      
      struct tree_cb cb;
      memset(&cb, 0, sizeof(cb));
      tree field_tree = walk_gimple_op(stmt_, find_st, (struct walk_stmt_info*)&cb);
      if (field_tree != NULL) {
        switch (cb.flag) {
          case COND_INST: {
            if (!insert_cond_inst) {
              gcc_log("building feedback for cond inst\n");
              insert_cond_inst = true;
            }
            break;
          }
          case VAL_INST: {
          
            unsigned idx = (unsigned)cb.data;
            //build call for val feedback
            tree fndecl_val_inst = builtin_decl_implicit(BUILT_IN_SANITIZER_COV_TRACE_INT8);
            tree id_tree = build_int_cstu(unsigned_type_node, idx);
            gimple *gcall_val = gimple_build_call(fndecl_val_inst, 2, id_tree, field_tree);
            gcc_log("building feedback for val feedback\n");
            gimple_set_location (gcall_val, gimple_location (stmt_));
            gsi_insert_before (&gsi_, gcall_val, GSI_SAME_STMT);
            break;
            
            // get current line number, file name, and save it to a txt file
            // line number:
            // int lineno = gimple_lineno(stmt_);
            // // file name:
            // const char *filename = gimple_filename(stmt_);
            // memset(cwd, 0, sizeof(cwd));
            // getcwd(cwd, 256);
            // // append to file
            // FILE *fp = fopen(output_file, "a");
            // if (fp == NULL) {
            //   fprintf(stderr, "Cannot open %s\n", output_file);
            //   assert(false);
            // }
            // fprintf(fp, "VAL_INST:%s/%s:%s:%d\n", cwd, filename, funcname, lineno);
            // fclose(fp);
            // break;
            
          }
          //prop pre post
          case PROP_INST: {
            unsigned res = (unsigned)cb.data;
            
            unsigned idx = (unsigned)cb.data>>8;
            enum built_in_function fncode = BUILT_IN_SANITIZER_PRE_TRACE;
            if ((unsigned)cb.data & 0xff == 1) {
              // pre
            } else {
              // post
              fncode = BUILT_IN_SANITIZER_POST_TRACE;
            }

            gcc_log("inserting prop inst\n");
            tree fndecl_trace = builtin_decl_implicit(fncode);
            tree id_tree = build_int_cstu(long_long_unsigned_type_node, idx);
            gimple *gcall = gimple_build_call(fndecl_trace, 1, id_tree);
            gimple_set_location (gcall, gimple_location (stmt));
            gsi_insert_before (&gsi, gcall, GSI_SAME_STMT);
            gcc_log("building feedback for prop inst\n");
            break;
            // int lineno = gimple_lineno(stmt_);
            // const char *filename = gimple_filename(stmt_);
            // memset(cwd, 0, sizeof(cwd));
            // getcwd(cwd, 256);
            // FILE *fp = fopen(output_file, "a");
            // if (fp == NULL) {
            //   fprintf(stderr, "Cannot open %s\n", output_file);
            //   assert(false);
            // }
            // fprintf(fp, "PROP_INST:%s/%s:%s:%d\n", cwd, filename, funcname, lineno);
            // fclose(fp);
            // break;

          }
        }
      }

      struct prop_list *p = lookup_prop(gimple_filename(stmt_), gimple_lineno(stmt_));
      if (p && p->idx) {
        unsigned idx = p->idx;
        // build call to enable post of this point
        // enable_point(id, mask);
        //id is the id, where mask is the size of map
        gcc_log("building feedback for enable point\n");
        
        tree fndecl_enable = builtin_decl_implicit(BUILT_IN_SANITIZER_ENABLE_TRACE);
        tree id_tree = build_int_cstu(unsigned_type_node, idx);
        tree mask_tree = build_int_cstu(unsigned_type_node, prop_idx);
        gimple *gcall_enable = gimple_build_call(fndecl_enable, 2, id_tree, mask_tree);
        gimple_set_location (gcall_enable, gimple_location (stmt));
        gsi_insert_before (&gsi, gcall_enable, GSI_SAME_STMT);
        break;
        
      //  int lineno = gimple_lineno(stmt_);
      //   const char *filename = gimple_filename(stmt_);
      //   memset(cwd, 0, sizeof(cwd));
      //   getcwd(cwd, 256);
      //   FILE *fp = fopen(output_file, "a");
      //   if (fp == NULL) {
      //     fprintf(stderr, "Cannot open %s\n", output_file);
      //     assert(false);
      //   }
      //   fprintf(fp, "ENABLE_POINT:%s/%s:%s:%d\n", cwd, filename, funcname, lineno);
      //   fclose(fp);

      }
    }

    // if (insert_cond_inst){
    //   int lineno = gimple_lineno(stmt);
    //   memset(cwd, 0, sizeof(cwd));
    //   getcwd(cwd, 256);
    //   const char *filename = gimple_filename(stmt);
    //   FILE *fp = fopen(output_file, "a");
    //   if (fp == NULL) {
    //     fprintf(stderr, "Cannot open %s\n", output_file);
    //     assert(false);
    //   }

    //   fprintf(fp, "COND_INST:%s/%s:%s:%d\n", cwd, filename, funcname, lineno);
    //   fclose(fp);
    // }
    
      fndecl = obj_fndecl;
      gimple *gcall = gimple_build_call (fndecl, 0);
	    gimple_set_location (gcall, gimple_location (stmt));
	    gsi_insert_before (&gsi, gcall, GSI_SAME_STMT);
      
      
	}
    }

  /* Insert callback into every comparison related operation.  */
  if (flag_sanitize_coverage & SANITIZE_COV_TRACE_CMP)
    {
      basic_block bb;
      FOR_EACH_BB_FN (bb, fun)
	{
	  gimple_stmt_iterator gsi;
	  for (gsi = gsi_start_bb (bb); !gsi_end_p (gsi); gsi_next (&gsi))
	    {
	      gimple *stmt = gsi_stmt (gsi);
	      enum tree_code rhs_code;
	      switch (gimple_code (stmt))
		{
		case GIMPLE_ASSIGN:
		  rhs_code = gimple_assign_rhs_code (stmt);
		  if (TREE_CODE_CLASS (rhs_code) == tcc_comparison)
		    instrument_comparison (&gsi,
					   gimple_assign_rhs1 (stmt),
					   gimple_assign_rhs2 (stmt));
		  else if (rhs_code == COND_EXPR
			   && COMPARISON_CLASS_P (gimple_assign_rhs1 (stmt)))
		    {
		      tree cond = gimple_assign_rhs1 (stmt);
		      instrument_comparison (&gsi, TREE_OPERAND (cond, 0),
					     TREE_OPERAND (cond, 1));
		    }
		  break;
		case GIMPLE_COND:
		  instrument_comparison (&gsi,
					 gimple_cond_lhs (stmt),
					 gimple_cond_rhs (stmt));
		  break;

		case GIMPLE_SWITCH:
		  instrument_switch (&gsi, stmt, fun);
		  break;

		default:
		  break;
		}
	    }
	}
    }
  return 0;
}

template <bool O0> class pass_sancov : public gimple_opt_pass
{
public:
  pass_sancov (gcc::context *ctxt) : gimple_opt_pass (data, ctxt) {
    init_structs();
    load_distance();
  }

  static const pass_data data;
  struct st *cond_list = NULL;
  struct prop_list *p_list = NULL;
  struct distance_list *d_list = NULL;

  opt_pass *
  clone ()
  {
    return new pass_sancov<O0> (m_ctxt);
  }
  virtual bool
  gate (function *)
  {
    return flag_sanitize_coverage && (!O0 || !optimize);
  }
  virtual unsigned int
  execute (function *fun)
  {
    return sancov_pass (fun);
  }
}; // class pass_sancov

template <bool O0>
const pass_data pass_sancov<O0>::data = {
  GIMPLE_PASS,		       /* type */
  O0 ? "sancov_O0" : "sancov", /* name */
  OPTGROUP_NONE,	       /* optinfo_flags */
  TV_NONE,		       /* tv_id */
  (PROP_cfg),		       /* properties_required */
  0,			       /* properties_provided */
  0,			       /* properties_destroyed */
  0,			       /* todo_flags_start */
  TODO_update_ssa,	     /* todo_flags_finish */
};

} // anon namespace

gimple_opt_pass *
make_pass_sancov (gcc::context *ctxt)
{
  return new pass_sancov<false> (ctxt);
}

gimple_opt_pass *
make_pass_sancov_O0 (gcc::context *ctxt)
{
  return new pass_sancov<true> (ctxt);
}
