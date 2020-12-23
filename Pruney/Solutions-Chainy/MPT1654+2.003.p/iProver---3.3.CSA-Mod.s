%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:20:57 EST 2020

% Result     : CounterSatisfiable 3.46s
% Output     : Model 3.46s
% Verified   : 
% Statistics : -

% Comments   : 
%------------------------------------------------------------------------------
%----WARNING: Could not form TPTP format derivation
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:23:55 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.46/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.46/0.98  
% 3.46/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.46/0.98  
% 3.46/0.98  ------  iProver source info
% 3.46/0.98  
% 3.46/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.46/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.46/0.98  git: non_committed_changes: false
% 3.46/0.98  git: last_make_outside_of_git: false
% 3.46/0.98  
% 3.46/0.98  ------ 
% 3.46/0.98  ------ Parsing...
% 3.46/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.46/0.98  
% 3.46/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.46/0.98  
% 3.46/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.46/0.98  
% 3.46/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.46/0.98  ------ Proving...
% 3.46/0.98  ------ Problem Properties 
% 3.46/0.98  
% 3.46/0.98  
% 3.46/0.98  clauses                                 19
% 3.46/0.98  conjectures                             6
% 3.46/0.98  EPR                                     7
% 3.46/0.98  Horn                                    13
% 3.46/0.98  unary                                   5
% 3.46/0.98  binary                                  8
% 3.46/0.98  lits                                    48
% 3.46/0.98  lits eq                                 4
% 3.46/0.98  fd_pure                                 0
% 3.46/0.98  fd_pseudo                               0
% 3.46/0.98  fd_cond                                 0
% 3.46/0.98  fd_pseudo_cond                          0
% 3.46/0.98  AC symbols                              0
% 3.46/0.98  
% 3.46/0.98  ------ Input Options Time Limit: Unbounded
% 3.46/0.98  
% 3.46/0.98  
% 3.46/0.98  
% 3.46/0.98  
% 3.46/0.98  ------ Preprocessing...
% 3.46/0.98  
% 3.46/0.98  ------ Preprocessing... sf_s  rm: 8 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 3.46/0.98  Current options:
% 3.46/0.98  ------ 
% 3.46/0.98  
% 3.46/0.98  
% 3.46/0.98  
% 3.46/0.98  
% 3.46/0.98  ------ Proving...
% 3.46/0.98  
% 3.46/0.98  
% 3.46/0.98  ------ Preprocessing...
% 3.46/0.98  
% 3.46/0.98  ------ Preprocessing... sf_s  rm: 8 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.46/0.98  
% 3.46/0.98  ------ Proving...
% 3.46/0.98  
% 3.46/0.98  
% 3.46/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.46/0.98  
% 3.46/0.98  ------ Proving...
% 3.46/0.98  
% 3.46/0.98  
% 3.46/0.98  % SZS status CounterSatisfiable for theBenchmark.p
% 3.46/0.98  
% 3.46/0.98  ------ Building Model...Done
% 3.46/0.98  
% 3.46/0.98  %------ The model is defined over ground terms (initial term algebra).
% 3.46/0.98  %------ Predicates are defined as (\forall x_1,..,x_n  ((~)P(x_1,..,x_n) <=> (\phi(x_1,..,x_n)))) 
% 3.46/0.98  %------ where \phi is a formula over the term algebra.
% 3.46/0.98  %------ If we have equality in the problem then it is also defined as a predicate above, 
% 3.46/0.98  %------ with "=" on the right-hand-side of the definition interpreted over the term algebra term_algebra_type
% 3.46/0.98  %------ See help for --sat_out_model for different model outputs.
% 3.46/0.98  %------ equality_sorted(X0,X1,X2) can be used in the place of usual "="
% 3.46/0.98  %------ where the first argument stands for the sort ($i in the unsorted case)
% 3.46/0.98  % SZS output start Model for theBenchmark.p
% 3.46/0.98  
% 3.46/0.98  %------ Positive definition of equality_sorted 
% 3.46/0.98  fof(lit_def,axiom,
% 3.46/0.98      (! [X0_0,X0_2,X1_2] : 
% 3.46/0.98        ( equality_sorted(X0_0,X0_2,X1_2) <=>
% 3.46/0.98             (
% 3.46/0.98                (
% 3.46/0.98                  ( X0_0=$o & X1_2=X0_2 )
% 3.46/0.98                )
% 3.46/0.98  
% 3.46/0.98               | 
% 3.46/0.98                (
% 3.46/0.98                  ( X0_0=iProver_m1_subset_1_1_$i )
% 3.46/0.98                 &
% 3.46/0.98                  ( X0_49!=arAF0_k1_enumset1_0 )
% 3.46/0.98                 &
% 3.46/0.98                  ( X0_49!=arAF0_k1_enumset1_0 | X1_49!=sK2 )
% 3.46/0.98                 &
% 3.46/0.98                  ( X0_49!=arAF0_k6_domain_1_0 )
% 3.46/0.98                 &
% 3.46/0.98                  ( X0_49!=arAF0_k6_domain_1_0 | X1_49!=sK2 )
% 3.46/0.98                 &
% 3.46/0.98                  ( X1_49!=arAF0_k1_enumset1_0 )
% 3.46/0.98                 &
% 3.46/0.98                  ( X1_49!=arAF0_k6_domain_1_0 )
% 3.46/0.98                )
% 3.46/0.98  
% 3.46/0.98               | 
% 3.46/0.98                (
% 3.46/0.98                  ( X0_0=iProver_m1_subset_1_1_$i & X0_49=arAF0_k2_yellow_0_0 )
% 3.46/0.98                 &
% 3.46/0.98                  ( X1_49!=arAF0_k1_enumset1_0 )
% 3.46/0.98                 &
% 3.46/0.98                  ( X1_49!=arAF0_k6_domain_1_0 )
% 3.46/0.98                )
% 3.46/0.98  
% 3.46/0.98               | 
% 3.46/0.98                (
% 3.46/0.98                  ( X0_0=iProver_m1_subset_1_1_$i & X0_49=arAF0_k1_enumset1_0 & X1_49=arAF0_k6_domain_1_0 )
% 3.46/0.98                )
% 3.46/0.98  
% 3.46/0.98               | 
% 3.46/0.98                (
% 3.46/0.98                  ( X0_0=iProver_m1_subset_1_1_$i & X0_49=arAF0_k6_domain_1_0 & X1_49=arAF0_k1_enumset1_0 )
% 3.46/0.98                )
% 3.46/0.98  
% 3.46/0.98               | 
% 3.46/0.98              ? [X0_48] : 
% 3.46/0.98                (
% 3.46/0.98                  ( X0_0=iProver_m1_subset_1_1_$i & X0_49=k1_yellow_0(X0_48,arAF0_k6_domain_1_0) )
% 3.46/0.98                 &
% 3.46/0.98                  ( X1_49!=arAF0_k1_enumset1_0 )
% 3.46/0.98                 &
% 3.46/0.98                  ( X1_49!=arAF0_k6_domain_1_0 )
% 3.46/0.98                )
% 3.46/0.98  
% 3.46/0.98               | 
% 3.46/0.98              ? [X0_48,X2_49,X3_49] : 
% 3.46/0.98                (
% 3.46/0.98                  ( X0_0=iProver_m1_subset_1_1_$i & X0_49=k1_yellow_0(X0_48,X2_49) & X1_49=k1_yellow_0(X0_48,X3_49) )
% 3.46/0.98                )
% 3.46/0.98  
% 3.46/0.98               | 
% 3.46/0.98                (
% 3.46/0.98                  ( X0_0=iProver_m1_subset_1_1_$i & X1_49=X0_49 )
% 3.46/0.98                )
% 3.46/0.98  
% 3.46/0.98             )
% 3.46/0.98        )
% 3.46/0.98      )
% 3.46/0.98     ).
% 3.46/0.98  
% 3.46/0.98  %------ Positive definition of m1_subset_1 
% 3.46/0.98  fof(lit_def,axiom,
% 3.46/0.98      (! [X0_49,X0_50] : 
% 3.46/0.98        ( m1_subset_1(X0_49,X0_50) <=>
% 3.46/0.98             (
% 3.46/0.98                (
% 3.46/0.98                  ( X0_49=sK2 & X0_50=arAF0_u1_struct_0_0 )
% 3.46/0.98                )
% 3.46/0.98  
% 3.46/0.98               | 
% 3.46/0.98                (
% 3.46/0.98                  ( X0_50=arAF0_u1_struct_0_0 )
% 3.46/0.98                 &
% 3.46/0.98                  ( X0_49!=arAF0_k1_enumset1_0 )
% 3.46/0.98                 &
% 3.46/0.98                  ( X0_49!=arAF0_k6_domain_1_0 )
% 3.46/0.98                )
% 3.46/0.98  
% 3.46/0.98               | 
% 3.46/0.98                (
% 3.46/0.98                  ( X0_50=arAF0_k1_zfmisc_1_0 )
% 3.46/0.98                )
% 3.46/0.98  
% 3.46/0.98             )
% 3.46/0.98        )
% 3.46/0.98      )
% 3.46/0.98     ).
% 3.46/0.98  
% 3.46/0.98  %------ Positive definition of v2_struct_0 
% 3.46/0.98  fof(lit_def,axiom,
% 3.46/0.98      (! [X0_48] : 
% 3.46/0.98        ( v2_struct_0(X0_48) <=>
% 3.46/0.98            $false
% 3.46/0.98        )
% 3.46/0.98      )
% 3.46/0.98     ).
% 3.46/0.98  
% 3.46/0.98  %------ Negative definition of l1_orders_2 
% 3.46/0.98  fof(lit_def,axiom,
% 3.46/0.98      (! [X0_48] : 
% 3.46/0.98        ( ~(l1_orders_2(X0_48)) <=>
% 3.46/0.98            $false
% 3.46/0.98        )
% 3.46/0.98      )
% 3.46/0.98     ).
% 3.46/0.98  
% 3.46/0.98  %------ Positive definition of r1_yellow_0 
% 3.46/0.98  fof(lit_def,axiom,
% 3.46/0.98      (! [X0_48,X0_49] : 
% 3.46/0.98        ( r1_yellow_0(X0_48,X0_49) <=>
% 3.46/0.98             (
% 3.46/0.98                (
% 3.46/0.98                  ( X0_49=arAF0_k1_enumset1_0 )
% 3.46/0.98                )
% 3.46/0.98  
% 3.46/0.98               | 
% 3.46/0.98                (
% 3.46/0.98                  ( X0_49=arAF0_k6_domain_1_0 )
% 3.46/0.98                )
% 3.46/0.98  
% 3.46/0.98             )
% 3.46/0.98        )
% 3.46/0.98      )
% 3.46/0.98     ).
% 3.46/0.98  
% 3.46/0.98  %------ Negative definition of v5_orders_2 
% 3.46/0.98  fof(lit_def,axiom,
% 3.46/0.98      (! [X0_48] : 
% 3.46/0.98        ( ~(v5_orders_2(X0_48)) <=>
% 3.46/0.98            $false
% 3.46/0.98        )
% 3.46/0.98      )
% 3.46/0.98     ).
% 3.46/0.98  
% 3.46/0.98  %------ Negative definition of v3_orders_2 
% 3.46/0.98  fof(lit_def,axiom,
% 3.46/0.98      (! [X0_48] : 
% 3.46/0.98        ( ~(v3_orders_2(X0_48)) <=>
% 3.46/0.98            $false
% 3.46/0.98        )
% 3.46/0.98      )
% 3.46/0.98     ).
% 3.46/0.98  
% 3.46/0.98  %------ Positive definition of arAF0_v1_xboole_0_0 
% 3.46/0.98  fof(lit_def,axiom,
% 3.46/0.98        ( arAF0_v1_xboole_0_0 <=>
% 3.46/0.98            $false
% 3.46/0.98        )
% 3.46/0.98     ).
% 3.46/0.98  
% 3.46/0.98  %------ Positive definition of arAF0_l1_struct_0_0 
% 3.46/0.98  fof(lit_def,axiom,
% 3.46/0.98        ( arAF0_l1_struct_0_0 <=>
% 3.46/0.98            $true
% 3.46/0.98        )
% 3.46/0.98     ).
% 3.46/0.98  
% 3.46/0.98  %------ Positive definition of arAF0_r1_tarski_0 
% 3.46/0.98  fof(lit_def,axiom,
% 3.46/0.98        ( arAF0_r1_tarski_0 <=>
% 3.46/0.98            $true
% 3.46/0.98        )
% 3.46/0.98     ).
% 3.46/0.98  
% 3.46/0.98  %------ Positive definition of arAF0_r2_hidden_0 
% 3.46/0.98  fof(lit_def,axiom,
% 3.46/0.98        ( arAF0_r2_hidden_0 <=>
% 3.46/0.98            $true
% 3.46/0.98        )
% 3.46/0.98     ).
% 3.46/0.98  % SZS output end Model for theBenchmark.p
% 3.46/0.98  ------                               Statistics
% 3.46/0.98  
% 3.46/0.98  ------ Selected
% 3.46/0.98  
% 3.46/0.98  total_time:                             0.092
% 3.46/0.98  
%------------------------------------------------------------------------------
