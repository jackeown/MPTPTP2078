%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:23:48 EST 2020

% Result     : CounterSatisfiable 2.29s
% Output     : Model 2.29s
% Verified   : 
% Statistics : -

% Comments   : 
%------------------------------------------------------------------------------
%----WARNING: Could not form TPTP format derivation
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:38:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.29/1.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.29/1.02  
% 2.29/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.29/1.02  
% 2.29/1.02  ------  iProver source info
% 2.29/1.02  
% 2.29/1.02  git: date: 2020-06-30 10:37:57 +0100
% 2.29/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.29/1.02  git: non_committed_changes: false
% 2.29/1.02  git: last_make_outside_of_git: false
% 2.29/1.02  
% 2.29/1.02  ------ 
% 2.29/1.02  ------ Parsing...
% 2.29/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.29/1.02  
% 2.29/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.29/1.02  
% 2.29/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.29/1.02  
% 2.29/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.29/1.02  ------ Proving...
% 2.29/1.02  ------ Problem Properties 
% 2.29/1.02  
% 2.29/1.02  
% 2.29/1.02  clauses                                 21
% 2.29/1.02  conjectures                             6
% 2.29/1.02  EPR                                     7
% 2.29/1.02  Horn                                    8
% 2.29/1.02  unary                                   5
% 2.29/1.02  binary                                  1
% 2.29/1.02  lits                                    136
% 2.29/1.02  lits eq                                 3
% 2.29/1.02  fd_pure                                 0
% 2.29/1.02  fd_pseudo                               0
% 2.29/1.02  fd_cond                                 0
% 2.29/1.02  fd_pseudo_cond                          0
% 2.29/1.02  AC symbols                              0
% 2.29/1.02  
% 2.29/1.02  ------ Input Options Time Limit: Unbounded
% 2.29/1.02  
% 2.29/1.02  
% 2.29/1.02  ------ 
% 2.29/1.02  Current options:
% 2.29/1.02  ------ 
% 2.29/1.02  
% 2.29/1.02  
% 2.29/1.02  
% 2.29/1.02  
% 2.29/1.02  ------ Proving...
% 2.29/1.02  
% 2.29/1.02  
% 2.29/1.02  % SZS status CounterSatisfiable for theBenchmark.p
% 2.29/1.02  
% 2.29/1.02  ------ Building Model...Done
% 2.29/1.02  
% 2.29/1.02  %------ The model is defined over ground terms (initial term algebra).
% 2.29/1.02  %------ Predicates are defined as (\forall x_1,..,x_n  ((~)P(x_1,..,x_n) <=> (\phi(x_1,..,x_n)))) 
% 2.29/1.02  %------ where \phi is a formula over the term algebra.
% 2.29/1.02  %------ If we have equality in the problem then it is also defined as a predicate above, 
% 2.29/1.02  %------ with "=" on the right-hand-side of the definition interpreted over the term algebra term_algebra_type
% 2.29/1.02  %------ See help for --sat_out_model for different model outputs.
% 2.29/1.02  %------ equality_sorted(X0,X1,X2) can be used in the place of usual "="
% 2.29/1.02  %------ where the first argument stands for the sort ($i in the unsorted case)
% 2.29/1.02  % SZS output start Model for theBenchmark.p
% 2.29/1.02  
% 2.29/1.02  %------ Positive definition of equality_sorted 
% 2.29/1.02  fof(lit_def,axiom,
% 2.29/1.02      (! [X0_0,X0_2,X1_2] : 
% 2.29/1.02        ( equality_sorted(X0_0,X0_2,X1_2) <=>
% 2.29/1.02             (
% 2.29/1.02                (
% 2.29/1.02                  ( X0_0=$o & X1_2=X0_2 )
% 2.29/1.02                )
% 2.29/1.02  
% 2.29/1.02               | 
% 2.29/1.02                (
% 2.29/1.02                  ( X0_0=iProver_v5_pre_topc_1_$i )
% 2.29/1.02                 &
% 2.29/1.02                  ! [X0_46] : ( X0_47!=k3_struct_0(X0_46) )
% 2.29/1.02                 &
% 2.29/1.02                  ! [X1_46] : ( X0_47!=k4_tmap_1(X0_46,X1_46) )
% 2.29/1.02                 &
% 2.29/1.02                  ( X0_47!=k2_tmap_1(X0_46,X0_46,k3_struct_0(X0_46),X1_46) )
% 2.29/1.02                 &
% 2.29/1.02                  ( X1_47!=k3_struct_0(X0_46) )
% 2.29/1.02                 &
% 2.29/1.02                  ( X1_47!=k4_tmap_1(X0_46,X1_46) )
% 2.29/1.02                 &
% 2.29/1.02                  ( X1_47!=k2_tmap_1(X0_46,X0_46,k3_struct_0(X0_46),X1_46) )
% 2.29/1.02                )
% 2.29/1.02  
% 2.29/1.02               | 
% 2.29/1.02              ? [X0_46] : 
% 2.29/1.02                (
% 2.29/1.02                  ( X0_0=iProver_v5_pre_topc_1_$i & X0_47=k3_struct_0(X0_46) & X1_47=k3_struct_0(X0_46) )
% 2.29/1.02                )
% 2.29/1.02  
% 2.29/1.02               | 
% 2.29/1.02              ? [X0_46,X1_46] : 
% 2.29/1.02                (
% 2.29/1.02                  ( X0_0=iProver_v5_pre_topc_1_$i & X0_47=k4_tmap_1(X0_46,X1_46) & X1_47=k4_tmap_1(X0_46,X1_46) )
% 2.29/1.02                )
% 2.29/1.02  
% 2.29/1.02               | 
% 2.29/1.02              ? [X0_46,X1_46] : 
% 2.29/1.02                (
% 2.29/1.02                  ( X0_0=iProver_v5_pre_topc_1_$i & X0_47=k4_tmap_1(X0_46,X1_46) & X1_47=k2_tmap_1(X0_46,X0_46,k3_struct_0(X0_46),X1_46) )
% 2.29/1.02                )
% 2.29/1.02  
% 2.29/1.02               | 
% 2.29/1.02              ? [X0_46,X1_46] : 
% 2.29/1.02                (
% 2.29/1.02                  ( X0_0=iProver_v5_pre_topc_1_$i & X0_47=k2_tmap_1(X0_46,X0_46,k3_struct_0(X0_46),X1_46) & X1_47=k4_tmap_1(X0_46,X1_46) )
% 2.29/1.02                )
% 2.29/1.02  
% 2.29/1.02               | 
% 2.29/1.02              ? [X0_46,X1_46] : 
% 2.29/1.02                (
% 2.29/1.02                  ( X0_0=iProver_v5_pre_topc_1_$i & X0_47=k2_tmap_1(X0_46,X0_46,k3_struct_0(X0_46),X1_46) & X1_47=k2_tmap_1(X0_46,X0_46,k3_struct_0(X0_46),X1_46) )
% 2.29/1.02                )
% 2.29/1.02  
% 2.29/1.02               | 
% 2.29/1.02              ? [X0_46,X1_46,X2_46] : 
% 2.29/1.02                (
% 2.29/1.02                  ( X0_0=iProver_v5_pre_topc_1_$i & X0_47=k2_partfun1(u1_struct_0(X0_46),u1_struct_0(X1_46),k4_tmap_1(X1_46,X0_46),u1_struct_0(X2_46)) & X1_47=k2_tmap_1(X0_46,X1_46,k4_tmap_1(X1_46,X0_46),X2_46) )
% 2.29/1.02                )
% 2.29/1.02  
% 2.29/1.02               | 
% 2.29/1.02              ? [X0_46,X1_46,X2_46,X3_46] : 
% 2.29/1.02                (
% 2.29/1.02                  ( X0_0=iProver_v5_pre_topc_1_$i & X0_47=k2_partfun1(u1_struct_0(X0_46),u1_struct_0(X1_46),k4_tmap_1(X1_46,X0_46),u1_struct_0(X2_46)) & X1_47=k3_tmap_1(X3_46,X1_46,X0_46,X2_46,k4_tmap_1(X1_46,X0_46)) )
% 2.29/1.02                )
% 2.29/1.02  
% 2.29/1.02               | 
% 2.29/1.02              ? [X0_46,X1_46,X2_46] : 
% 2.29/1.02                (
% 2.29/1.02                  ( X0_0=iProver_v5_pre_topc_1_$i & X0_47=k2_partfun1(u1_struct_0(X0_46),u1_struct_0(X1_46),k2_tmap_1(X1_46,X1_46,k3_struct_0(X1_46),X0_46),u1_struct_0(X2_46)) & X1_47=k2_tmap_1(X0_46,X1_46,k2_tmap_1(X1_46,X1_46,k3_struct_0(X1_46),X0_46),X2_46) )
% 2.29/1.02                )
% 2.29/1.02  
% 2.29/1.02               | 
% 2.29/1.02              ? [X0_46,X1_46,X2_46,X3_46] : 
% 2.29/1.02                (
% 2.29/1.02                  ( X0_0=iProver_v5_pre_topc_1_$i & X0_47=k2_partfun1(u1_struct_0(X0_46),u1_struct_0(X1_46),k2_tmap_1(X1_46,X1_46,k3_struct_0(X1_46),X0_46),u1_struct_0(X2_46)) & X1_47=k3_tmap_1(X3_46,X1_46,X0_46,X2_46,k2_tmap_1(X1_46,X1_46,k3_struct_0(X1_46),X0_46)) )
% 2.29/1.02                )
% 2.29/1.02  
% 2.29/1.02               | 
% 2.29/1.02              ? [X0_46,X1_46,X2_47,X2_46,X3_47] : 
% 2.29/1.02                (
% 2.29/1.02                  ( X0_0=iProver_v5_pre_topc_1_$i & X0_47=k2_tmap_1(X0_46,X1_46,X2_47,X2_46) & X1_47=k2_tmap_1(X0_46,X1_46,X3_47,X2_46) )
% 2.29/1.02                 &
% 2.29/1.02                  ( X0_46!=X0_46 | X1_46!=X0_46 | X2_47!=k3_struct_0(X0_46) )
% 2.29/1.02                 &
% 2.29/1.02                  ( X0_46!=X0_46 | X1_46!=X0_46 | X3_47!=k3_struct_0(X0_46) )
% 2.29/1.02                )
% 2.29/1.02  
% 2.29/1.02               | 
% 2.29/1.02                (
% 2.29/1.02                  ( X0_0=iProver_v5_pre_topc_1_$i & X1_47=X0_47 )
% 2.29/1.02                 &
% 2.29/1.02                  ! [X0_46] : ( X0_47!=k3_struct_0(X0_46) )
% 2.29/1.02                 &
% 2.29/1.02                  ! [X1_46] : ( X0_47!=k4_tmap_1(X0_46,X1_46) )
% 2.29/1.02                 &
% 2.29/1.02                  ( X0_47!=k2_tmap_1(X0_46,X0_46,k3_struct_0(X0_46),X1_46) )
% 2.29/1.02                )
% 2.29/1.02  
% 2.29/1.02             )
% 2.29/1.02        )
% 2.29/1.02      )
% 2.29/1.02     ).
% 2.29/1.02  
% 2.29/1.02  %------ Positive definition of m1_pre_topc 
% 2.29/1.02  fof(lit_def,axiom,
% 2.29/1.02      (! [X0_46,X1_46] : 
% 2.29/1.02        ( m1_pre_topc(X0_46,X1_46) <=>
% 2.29/1.02            $true
% 2.29/1.02        )
% 2.29/1.02      )
% 2.29/1.02     ).
% 2.29/1.02  
% 2.29/1.02  %------ Positive definition of m1_subset_1 
% 2.29/1.02  fof(lit_def,axiom,
% 2.29/1.02      (! [X0_47,X0_49] : 
% 2.29/1.02        ( m1_subset_1(X0_47,X0_49) <=>
% 2.29/1.02             (
% 2.29/1.02              ? [X0_46,X1_46] : 
% 2.29/1.02                (
% 2.29/1.02                  ( X0_47=k4_tmap_1(X0_46,X1_46) & X0_49=k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_46),u1_struct_0(X0_46))) )
% 2.29/1.02                )
% 2.29/1.02  
% 2.29/1.02               | 
% 2.29/1.02              ? [X0_46,X1_46] : 
% 2.29/1.02                (
% 2.29/1.02                  ( X0_47=k2_tmap_1(X0_46,X0_46,k3_struct_0(X0_46),X1_46) & X0_49=k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_46),u1_struct_0(X0_46))) )
% 2.29/1.02                )
% 2.29/1.02  
% 2.29/1.02             )
% 2.29/1.02        )
% 2.29/1.02      )
% 2.29/1.02     ).
% 2.29/1.02  
% 2.29/1.02  %------ Positive definition of v1_funct_2 
% 2.29/1.02  fof(lit_def,axiom,
% 2.29/1.02      (! [X0_47,X0_48,X1_48] : 
% 2.29/1.02        ( v1_funct_2(X0_47,X0_48,X1_48) <=>
% 2.29/1.02             (
% 2.29/1.02              ? [X0_46] : 
% 2.29/1.02                (
% 2.29/1.02                  ( X0_47=k3_struct_0(X0_46) & X0_48=u1_struct_0(X0_46) & X1_48=u1_struct_0(X0_46) )
% 2.29/1.02                )
% 2.29/1.02  
% 2.29/1.02               | 
% 2.29/1.02              ? [X0_46,X1_46] : 
% 2.29/1.02                (
% 2.29/1.02                  ( X0_47=k4_tmap_1(X0_46,X1_46) & X0_48=u1_struct_0(X1_46) & X1_48=u1_struct_0(X0_46) )
% 2.29/1.02                )
% 2.29/1.02  
% 2.29/1.02               | 
% 2.29/1.02              ? [X0_46,X1_46] : 
% 2.29/1.02                (
% 2.29/1.02                  ( X0_47=k2_tmap_1(X0_46,X0_46,k3_struct_0(X0_46),X1_46) & X0_48=u1_struct_0(X1_46) & X1_48=u1_struct_0(X0_46) )
% 2.29/1.02                )
% 2.29/1.02  
% 2.29/1.02             )
% 2.29/1.02        )
% 2.29/1.02      )
% 2.29/1.02     ).
% 2.29/1.02  
% 2.29/1.02  %------ Positive definition of v1_funct_1 
% 2.29/1.02  fof(lit_def,axiom,
% 2.29/1.02      (! [X0_47] : 
% 2.29/1.02        ( v1_funct_1(X0_47) <=>
% 2.29/1.02             (
% 2.29/1.02                (
% 2.29/1.02                  ( X0_47=k4_tmap_1(sK0,sK1) )
% 2.29/1.02                )
% 2.29/1.02  
% 2.29/1.02               | 
% 2.29/1.02              ? [X0_46] : 
% 2.29/1.02                (
% 2.29/1.02                  ( X0_47=k3_struct_0(X0_46) )
% 2.29/1.02                )
% 2.29/1.02  
% 2.29/1.02               | 
% 2.29/1.02              ? [X0_46,X1_46] : 
% 2.29/1.02                (
% 2.29/1.02                  ( X0_47=k4_tmap_1(X0_46,X1_46) )
% 2.29/1.02                )
% 2.29/1.02  
% 2.29/1.02               | 
% 2.29/1.02              ? [X0_46,X1_46] : 
% 2.29/1.02                (
% 2.29/1.02                  ( X0_47=k2_tmap_1(X0_46,X0_46,k3_struct_0(X0_46),X1_46) )
% 2.29/1.02                )
% 2.29/1.02  
% 2.29/1.02             )
% 2.29/1.02        )
% 2.29/1.02      )
% 2.29/1.02     ).
% 2.29/1.02  
% 2.29/1.02  %------ Negative definition of l1_pre_topc 
% 2.29/1.02  fof(lit_def,axiom,
% 2.29/1.02      (! [X0_46] : 
% 2.29/1.02        ( ~(l1_pre_topc(X0_46)) <=>
% 2.29/1.02            $false
% 2.29/1.02        )
% 2.29/1.02      )
% 2.29/1.02     ).
% 2.29/1.02  
% 2.29/1.02  %------ Negative definition of v2_pre_topc 
% 2.29/1.02  fof(lit_def,axiom,
% 2.29/1.02      (! [X0_46] : 
% 2.29/1.02        ( ~(v2_pre_topc(X0_46)) <=>
% 2.29/1.02            $false
% 2.29/1.02        )
% 2.29/1.02      )
% 2.29/1.02     ).
% 2.29/1.02  
% 2.29/1.02  %------ Positive definition of v2_struct_0 
% 2.29/1.02  fof(lit_def,axiom,
% 2.29/1.02      (! [X0_46] : 
% 2.29/1.02        ( v2_struct_0(X0_46) <=>
% 2.29/1.02            $false
% 2.29/1.02        )
% 2.29/1.02      )
% 2.29/1.02     ).
% 2.29/1.02  
% 2.29/1.02  %------ Positive definition of v5_pre_topc 
% 2.29/1.02  fof(lit_def,axiom,
% 2.29/1.02      (! [X0_47,X0_46,X1_46] : 
% 2.29/1.02        ( v5_pre_topc(X0_47,X0_46,X1_46) <=>
% 2.29/1.02             (
% 2.29/1.02                (
% 2.29/1.02                  ( X0_47=k3_struct_0(X0_46) & X1_46=X0_46 )
% 2.29/1.02                )
% 2.29/1.02  
% 2.29/1.02             )
% 2.29/1.02        )
% 2.29/1.02      )
% 2.29/1.02     ).
% 2.29/1.02  % SZS output end Model for theBenchmark.p
% 2.29/1.02  ------                               Statistics
% 2.29/1.02  
% 2.29/1.02  ------ Selected
% 2.29/1.02  
% 2.29/1.02  total_time:                             0.064
% 2.29/1.02  
%------------------------------------------------------------------------------
