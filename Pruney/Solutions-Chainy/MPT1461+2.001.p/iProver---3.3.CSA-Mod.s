%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:18:59 EST 2020

% Result     : CounterSatisfiable 3.36s
% Output     : Model 3.83s
% Verified   : 
% Statistics : -

% Comments   : 
%------------------------------------------------------------------------------
%----WARNING: Could not form TPTP format derivation
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:42:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.36/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.36/1.00  
% 3.36/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.36/1.00  
% 3.36/1.00  ------  iProver source info
% 3.36/1.00  
% 3.36/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.36/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.36/1.00  git: non_committed_changes: false
% 3.36/1.00  git: last_make_outside_of_git: false
% 3.36/1.00  
% 3.36/1.00  ------ 
% 3.36/1.00  ------ Parsing...
% 3.36/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.36/1.00  
% 3.36/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 3.36/1.00  
% 3.36/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.36/1.00  
% 3.36/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.36/1.00  ------ Proving...
% 3.36/1.00  ------ Problem Properties 
% 3.36/1.00  
% 3.36/1.00  
% 3.36/1.00  clauses                                 24
% 3.36/1.00  conjectures                             8
% 3.36/1.00  EPR                                     10
% 3.36/1.00  Horn                                    10
% 3.36/1.00  unary                                   7
% 3.36/1.00  binary                                  2
% 3.36/1.00  lits                                    96
% 3.36/1.00  lits eq                                 6
% 3.36/1.00  fd_pure                                 0
% 3.36/1.00  fd_pseudo                               0
% 3.36/1.00  fd_cond                                 0
% 3.36/1.00  fd_pseudo_cond                          0
% 3.36/1.00  AC symbols                              0
% 3.36/1.00  
% 3.36/1.00  ------ Input Options Time Limit: Unbounded
% 3.36/1.00  
% 3.36/1.00  
% 3.36/1.00  
% 3.36/1.00  
% 3.36/1.00  ------ Preprocessing...
% 3.36/1.00  
% 3.36/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e ------ 
% 3.36/1.00  Current options:
% 3.36/1.00  ------ 
% 3.36/1.00  
% 3.36/1.00  
% 3.36/1.00  
% 3.36/1.00  
% 3.36/1.00  ------ Proving...
% 3.36/1.00  
% 3.36/1.00  
% 3.36/1.00  ------ Preprocessing...
% 3.36/1.00  
% 3.36/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.36/1.00  
% 3.36/1.00  ------ Proving...
% 3.36/1.00  
% 3.36/1.00  
% 3.36/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.36/1.00  
% 3.36/1.00  ------ Proving...
% 3.36/1.00  
% 3.36/1.00  
% 3.36/1.00  % SZS status CounterSatisfiable for theBenchmark.p
% 3.36/1.00  
% 3.36/1.00  ------ Building Model...Done
% 3.36/1.00  
% 3.36/1.00  %------ The model is defined over ground terms (initial term algebra).
% 3.36/1.00  %------ Predicates are defined as (\forall x_1,..,x_n  ((~)P(x_1,..,x_n) <=> (\phi(x_1,..,x_n)))) 
% 3.36/1.00  %------ where \phi is a formula over the term algebra.
% 3.36/1.00  %------ If we have equality in the problem then it is also defined as a predicate above, 
% 3.36/1.00  %------ with "=" on the right-hand-side of the definition interpreted over the term algebra term_algebra_type
% 3.36/1.00  %------ See help for --sat_out_model for different model outputs.
% 3.36/1.00  %------ equality_sorted(X0,X1,X2) can be used in the place of usual "="
% 3.36/1.00  %------ where the first argument stands for the sort ($i in the unsorted case)
% 3.36/1.00  % SZS output start Model for theBenchmark.p
% 3.36/1.00  
% 3.36/1.00  %------ Positive definition of equality_sorted 
% 3.36/1.00  fof(lit_def,axiom,
% 3.36/1.00      (! [X0_0,X0_2,X1_2] : 
% 3.36/1.00        ( equality_sorted(X0_0,X0_2,X1_2) <=>
% 3.36/1.00             (
% 3.36/1.00                (
% 3.36/1.00                  ( X0_0=$o & X1_2=X0_2 )
% 3.36/1.00                )
% 3.36/1.00  
% 3.36/1.00               | 
% 3.36/1.00                (
% 3.36/1.00                  ( X0_0=iProver_k4_filter_0_2_$i )
% 3.36/1.00                 &
% 3.36/1.00                  ( X0_51!=arAF0_k4_filter_0_0 )
% 3.36/1.00                 &
% 3.36/1.00                  ( X1_51!=arAF0_k4_filter_0_0 )
% 3.36/1.00                )
% 3.36/1.00  
% 3.36/1.00               | 
% 3.36/1.00                (
% 3.36/1.00                  ( X0_0=iProver_k4_filter_0_2_$i & X0_51=arAF0_k1_lattices_0 )
% 3.36/1.00                 &
% 3.36/1.00                  ( X1_51!=arAF0_k4_filter_0_0 )
% 3.36/1.00                )
% 3.36/1.00  
% 3.36/1.00               | 
% 3.36/1.00                (
% 3.36/1.00                  ( X0_0=iProver_k4_filter_0_2_$i & X0_51=arAF0_k1_lattices_0 & X1_51=arAF0_k3_lattices_0 )
% 3.36/1.00                )
% 3.36/1.00  
% 3.36/1.00               | 
% 3.36/1.00                (
% 3.36/1.00                  ( X0_0=iProver_k4_filter_0_2_$i & X1_51=X0_51 )
% 3.36/1.00                )
% 3.36/1.00  
% 3.36/1.00             )
% 3.36/1.00        )
% 3.36/1.00      )
% 3.36/1.00     ).
% 3.36/1.00  
% 3.36/1.00  %------ Positive definition of v9_lattices 
% 3.36/1.00  fof(lit_def,axiom,
% 3.36/1.00      (! [X0_50] : 
% 3.36/1.00        ( v9_lattices(X0_50) <=>
% 3.36/1.00            $true
% 3.36/1.00        )
% 3.36/1.00      )
% 3.36/1.00     ).
% 3.36/1.00  
% 3.36/1.00  %------ Negative definition of v10_lattices 
% 3.36/1.00  fof(lit_def,axiom,
% 3.36/1.00      (! [X0_50] : 
% 3.36/1.00        ( ~(v10_lattices(X0_50)) <=>
% 3.36/1.00            $false
% 3.36/1.00        )
% 3.36/1.00      )
% 3.36/1.00     ).
% 3.36/1.00  
% 3.36/1.00  %------ Positive definition of v2_struct_0 
% 3.36/1.00  fof(lit_def,axiom,
% 3.36/1.00      (! [X0_50] : 
% 3.36/1.00        ( v2_struct_0(X0_50) <=>
% 3.36/1.00            $false
% 3.36/1.00        )
% 3.36/1.00      )
% 3.36/1.00     ).
% 3.36/1.00  
% 3.36/1.00  %------ Negative definition of l3_lattices 
% 3.36/1.00  fof(lit_def,axiom,
% 3.36/1.00      (! [X0_50] : 
% 3.36/1.00        ( ~(l3_lattices(X0_50)) <=>
% 3.36/1.00            $false
% 3.36/1.00        )
% 3.36/1.00      )
% 3.36/1.00     ).
% 3.36/1.00  
% 3.36/1.00  %------ Positive definition of v8_lattices 
% 3.36/1.00  fof(lit_def,axiom,
% 3.36/1.00      (! [X0_50] : 
% 3.36/1.00        ( v8_lattices(X0_50) <=>
% 3.36/1.00            $true
% 3.36/1.00        )
% 3.36/1.00      )
% 3.36/1.00     ).
% 3.36/1.00  
% 3.36/1.00  %------ Positive definition of v6_lattices 
% 3.36/1.00  fof(lit_def,axiom,
% 3.36/1.00      (! [X0_50] : 
% 3.36/1.00        ( v6_lattices(X0_50) <=>
% 3.36/1.00            $true
% 3.36/1.00        )
% 3.36/1.00      )
% 3.36/1.00     ).
% 3.36/1.00  
% 3.36/1.00  %------ Positive definition of m1_subset_1 
% 3.36/1.00  fof(lit_def,axiom,
% 3.36/1.00      (! [X0_51,X0_52] : 
% 3.36/1.00        ( m1_subset_1(X0_51,X0_52) <=>
% 3.36/1.00             (
% 3.36/1.00                (
% 3.36/1.00                  ( X0_51=sK1 & X0_52=arAF0_u1_struct_0_0 )
% 3.36/1.00                )
% 3.36/1.00  
% 3.36/1.00               | 
% 3.36/1.00                (
% 3.36/1.00                  ( X0_51=sK2 & X0_52=arAF0_u1_struct_0_0 )
% 3.36/1.00                )
% 3.36/1.00  
% 3.36/1.00               | 
% 3.36/1.00                (
% 3.36/1.00                  ( X0_51=sK3 & X0_52=arAF0_u1_struct_0_0 )
% 3.36/1.00                )
% 3.36/1.00  
% 3.36/1.00               | 
% 3.36/1.00                (
% 3.36/1.00                  ( X0_51=arAF0_k3_lattices_0 & X0_52=arAF0_u1_struct_0_0 )
% 3.36/1.00                )
% 3.36/1.00  
% 3.36/1.00               | 
% 3.36/1.00                (
% 3.36/1.00                  ( X0_51=arAF0_k4_lattices_0 & X0_52=arAF0_u1_struct_0_0 )
% 3.36/1.00                )
% 3.36/1.00  
% 3.36/1.00               | 
% 3.36/1.00                (
% 3.36/1.00                  ( X0_52=arAF0_u1_struct_0_0 )
% 3.36/1.00                 &
% 3.36/1.00                  ( X0_51!=arAF0_k4_filter_0_0 )
% 3.36/1.00                )
% 3.36/1.00  
% 3.36/1.00             )
% 3.36/1.00        )
% 3.36/1.00      )
% 3.36/1.00     ).
% 3.36/1.00  
% 3.36/1.00  %------ Positive definition of arAF0_v3_filter_0_0 
% 3.83/1.00  fof(lit_def,axiom,
% 3.83/1.00        ( arAF0_v3_filter_0_0 <=>
% 3.83/1.00            $true
% 3.83/1.00        )
% 3.83/1.00     ).
% 3.83/1.00  
% 3.83/1.00  %------ Positive definition of arAF0_r1_lattices_0 
% 3.83/1.00  fof(lit_def,axiom,
% 3.83/1.00        ( arAF0_r1_lattices_0 <=>
% 3.83/1.00            $true
% 3.83/1.00        )
% 3.83/1.00     ).
% 3.83/1.00  
% 3.83/1.00  %------ Positive definition of arAF0_l2_lattices_0 
% 3.83/1.00  fof(lit_def,axiom,
% 3.83/1.00        ( arAF0_l2_lattices_0 <=>
% 3.83/1.00            $true
% 3.83/1.00        )
% 3.83/1.00     ).
% 3.83/1.00  
% 3.83/1.00  %------ Positive definition of arAF0_v4_lattices_0 
% 3.83/1.00  fof(lit_def,axiom,
% 3.83/1.00        ( arAF0_v4_lattices_0 <=>
% 3.83/1.00            $true
% 3.83/1.00        )
% 3.83/1.00     ).
% 3.83/1.00  
% 3.83/1.00  %------ Positive definition of arAF0_l1_lattices_0 
% 3.83/1.00  fof(lit_def,axiom,
% 3.83/1.00        ( arAF0_l1_lattices_0 <=>
% 3.83/1.00            $true
% 3.83/1.00        )
% 3.83/1.00     ).
% 3.83/1.00  
% 3.83/1.00  %------ Negative definition of arAF0_r3_lattices_0_1_2 
% 3.83/1.00  fof(lit_def,axiom,
% 3.83/1.00      (! [X0_50,X0_51] : 
% 3.83/1.00        ( ~(arAF0_r3_lattices_0_1_2(X0_50,X0_51)) <=>
% 3.83/1.00             (
% 3.83/1.00                (
% 3.83/1.00                  ( X0_50=sK0 & X0_51=arAF0_k4_filter_0_0 )
% 3.83/1.00                )
% 3.83/1.00  
% 3.83/1.00             )
% 3.83/1.00        )
% 3.83/1.00      )
% 3.83/1.00     ).
% 3.83/1.00  % SZS output end Model for theBenchmark.p
% 3.83/1.00  ------                               Statistics
% 3.83/1.00  
% 3.83/1.00  ------ Selected
% 3.83/1.00  
% 3.83/1.00  total_time:                             0.094
% 3.83/1.00  
%------------------------------------------------------------------------------
