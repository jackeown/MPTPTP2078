%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:11:26 EST 2020

% Result     : Timeout 59.76s
% Output     : None 
% Verified   : 
% Statistics : Number of formulae       :    9 (   9 expanded)
%              Number of leaves         :    9 (   9 expanded)
%              Depth                    :    0
%              Number of atoms          :  245 ( 245 expanded)
%              Number of equality atoms :  232 ( 232 expanded)
%              Maximal formula depth    :   29 (  12 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%------ Positive definition of equality_sorted 
fof(lit_def,axiom,(
    ! [X0_0,X0_2,X1_2] :
      ( equality_sorted(X0_0,X0_2,X1_2)
    <=> ( ( X0_0 = $o
          & X1_2 = X0_2 )
        | ( X0_0 = $i
          & X0 != u1_struct_0(X0)
          & X0 != sK7
          & ( X0 != sK5
            | X1 != sK6 )
          & ( X0 != u1_struct_0(sK5)
            | X1 != u1_struct_0(sK6) )
          & ( X0 != k1_zfmisc_1(u1_struct_0(sK5))
            | X1 != k1_zfmisc_1(u1_struct_0(sK6)) )
          & X0 != sK6
          & X0 != u1_struct_0(sK6)
          & X0 != k1_zfmisc_1(u1_struct_0(sK6))
          & X0 != arAF0_u1_pre_topc_0
          & X1 != u1_struct_0(X1)
          & X1 != sK7
          & X1 != sK6
          & X1 != u1_struct_0(sK6)
          & X1 != k1_zfmisc_1(u1_struct_0(sK6))
          & X1 != arAF0_u1_pre_topc_0 )
        | ( X0_0 = $i
          & X0 = k1_xboole_0
          & X1 != u1_struct_0(X1)
          & X1 != sK7
          & X1 != sK6
          & X1 != u1_struct_0(sK6)
          & X1 != k1_zfmisc_1(u1_struct_0(sK6))
          & X1 != arAF0_u1_pre_topc_0 )
        | ? [X2,X3] :
            ( X0_0 = $i
            & X0 = k1_zfmisc_1(X2)
            & X1 = k1_zfmisc_1(X3)
            & ( X2 != u1_struct_0(sK5)
              | X3 != u1_struct_0(sK6) )
            & X2 != u1_struct_0(sK6)
            & X3 != u1_struct_0(sK6) )
        | ? [X2] :
            ( X0_0 = $i
            & X0 = u1_struct_0(sK5)
            & X1 = u1_struct_0(X2)
            & X2 != sK6 )
        | ( X0_0 = $i
          & X0 = u1_struct_0(sK6)
          & X1 = u1_struct_0(sK6) )
        | ( X0_0 = $i
          & X0 = k1_zfmisc_1(u1_struct_0(sK6))
          & X1 = k1_zfmisc_1(u1_struct_0(sK6)) )
        | ? [X2,X3] :
            ( X0_0 = $i
            & X0 = u1_struct_0(X2)
            & X1 = u1_struct_0(X3)
            & X2 != sK5
            & ( X2 != sK5
              | X3 != sK6 )
            & X2 != sK6
            & X3 != sK6 )
        | ( X0_0 = $i
          & X0 = arAF0_k9_subset_1_0
          & X1 != u1_struct_0(X1)
          & X1 != sK7
          & X1 != sK6
          & X1 != u1_struct_0(sK6)
          & X1 != k1_zfmisc_1(u1_struct_0(sK6))
          & X1 != arAF0_u1_pre_topc_0 )
        | ( X0_0 = $i
          & X1 = X0 ) ) ) )).

%------ Negative definition of v1_xboole_0 
fof(lit_def_001,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
    <=> ( ? [X1] : X0 = u1_struct_0(X1)
        | X0 = sK7
        | X0 = sK6
        | X0 = u1_struct_0(sK6)
        | X0 = k1_zfmisc_1(u1_struct_0(sK6))
        | X0 = arAF0_u1_pre_topc_0 ) ) )).

%------ Negative definition of r1_tarski 
fof(lit_def_002,axiom,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
    <=> ( ( X0 = sK7
          & X1 != u1_struct_0(sK6) )
        | ( X0 = sK7
          & X1 = u1_struct_0(sK5) )
        | X0 = sK6
        | X0 = u1_struct_0(sK6)
        | ( X0 = k1_zfmisc_1(u1_struct_0(sK6))
          & X1 != k1_zfmisc_1(X1)
          & X1 != u1_struct_0(sK6) )
        | ? [X2] :
            ( X0 = k1_zfmisc_1(u1_struct_0(sK6))
            & X1 = k1_zfmisc_1(X2) )
        | ? [X2] : X0 = u1_struct_0(X2)
        | X0 = arAF0_u1_pre_topc_0 ) ) )).

%------ Positive definition of m1_subset_1 
fof(lit_def_003,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
    <=> ( ( X0 != u1_struct_0(X0)
          & ( X0 != u1_struct_0(X0)
            | X1 != k1_zfmisc_1(X1) )
          & X0 != sK7
          & ( X0 != sK7
            | X1 != k1_zfmisc_1(u1_struct_0(sK5)) )
          & X0 != sK6
          & X0 != u1_struct_0(sK6)
          & ( X0 != u1_struct_0(sK6)
            | X1 != k1_zfmisc_1(X0) )
          & ( X0 != u1_struct_0(sK6)
            | X1 != k1_zfmisc_1(X2) )
          & X0 != k1_zfmisc_1(u1_struct_0(sK6))
          & X0 != arAF0_u1_pre_topc_0 )
        | ( X0 = sK7
          & X1 = sK7 )
        | ( X0 = sK7
          & X1 = u1_struct_0(sK6) )
        | ( X0 = sK7
          & X1 = k1_zfmisc_1(u1_struct_0(sK6)) )
        | ( X0 = k1_zfmisc_1(u1_struct_0(sK6))
          & X1 = u1_struct_0(sK6) )
        | ( X0 = k1_zfmisc_1(u1_struct_0(sK6))
          & X1 = k1_zfmisc_1(u1_struct_0(sK6)) )
        | ? [X2] :
            ( X0 = arAF0_sK4_0
            & X1 = k1_zfmisc_1(u1_struct_0(X2)) )
        | ? [X2] :
            ( X1 = k1_zfmisc_1(X2)
            & X0 != u1_struct_0(X0)
            & X0 != sK7
            & ( X0 != sK7
              | X2 != u1_struct_0(sK5) )
            & X0 != sK6
            & X0 != u1_struct_0(sK6)
            & X0 != k1_zfmisc_1(u1_struct_0(sK6))
            & X0 != arAF0_u1_pre_topc_0 )
        | ( X1 = sK7
          & X0 != u1_struct_0(X0)
          & X0 != sK7
          & X0 != sK6
          & X0 != arAF0_u1_pre_topc_0 )
        | ( X1 = sK6
          & X0 != u1_struct_0(X0)
          & X0 != sK7
          & X0 != sK6
          & X0 != k1_zfmisc_1(u1_struct_0(sK6))
          & X0 != arAF0_u1_pre_topc_0 )
        | ( X1 = u1_struct_0(sK6)
          & X0 != u1_struct_0(X0)
          & X0 != sK7
          & X0 != sK6
          & X0 != u1_struct_0(sK6)
          & X0 != k1_zfmisc_1(u1_struct_0(sK6))
          & X0 != arAF0_u1_pre_topc_0 )
        | ( X1 = k1_zfmisc_1(u1_struct_0(sK6))
          & X0 != u1_struct_0(X0)
          & X0 != sK7
          & X0 != sK6
          & X0 != u1_struct_0(sK6)
          & X0 != k1_zfmisc_1(u1_struct_0(sK6))
          & X0 != arAF0_u1_pre_topc_0 )
        | ? [X2] :
            ( X1 = u1_struct_0(X2)
            & X0 != u1_struct_0(X0)
            & ( X0 != u1_struct_0(X0)
              | X2 != sK6 )
            & X0 != sK7
            & X0 != sK6
            & ( X0 != sK6
              | X2 != sK6 )
            & ( X0 != u1_struct_0(sK6)
              | X2 != sK6 )
            & X0 != k1_zfmisc_1(u1_struct_0(sK6))
            & X0 != arAF0_u1_pre_topc_0
            & ( X0 != arAF0_u1_pre_topc_0
              | X2 != sK6 ) )
        | ( X1 = arAF0_u1_pre_topc_0
          & X0 != u1_struct_0(X0)
          & X0 != sK7
          & X0 != sK6
          & X0 != k1_zfmisc_1(u1_struct_0(sK6))
          & X0 != arAF0_u1_pre_topc_0 ) ) ) )).

%------ Positive definition of r2_hidden 
fof(lit_def_004,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
    <=> ( ( X0 != u1_struct_0(X0)
          & X0 != sK7
          & X0 != sK6
          & ( X0 != sK6
            | X1 != arAF0_u1_pre_topc_0 )
          & X0 != u1_struct_0(sK6)
          & X0 != k1_zfmisc_1(u1_struct_0(sK6))
          & X0 != arAF0_u1_pre_topc_0
          & ( X0 != arAF0_u1_pre_topc_0
            | X1 != arAF0_u1_pre_topc_0 ) )
        | ( X0 = sK7
          & X1 = sK7 )
        | ( X0 = sK7
          & X1 = u1_struct_0(sK6) )
        | ( X0 = sK7
          & X1 = k1_zfmisc_1(u1_struct_0(sK6)) )
        | ( X0 = k1_zfmisc_1(u1_struct_0(sK6))
          & X1 = u1_struct_0(sK6) )
        | ( X0 = arAF0_k9_subset_1_0
          & X1 = arAF0_u1_pre_topc_0 )
        | ( X0 = arAF0_sK4_0
          & X1 = arAF0_u1_pre_topc_0 )
        | ( X1 = sK7
          & X0 != u1_struct_0(X0)
          & X0 != sK7
          & X0 != sK6
          & X0 != u1_struct_0(sK6)
          & X0 != arAF0_u1_pre_topc_0 )
        | ( X1 = sK6
          & X0 != u1_struct_0(X0)
          & X0 != sK7
          & X0 != sK6
          & X0 != k1_zfmisc_1(u1_struct_0(sK6))
          & X0 != arAF0_u1_pre_topc_0 )
        | ( X1 = u1_struct_0(sK6)
          & X0 != u1_struct_0(X0)
          & X0 != sK7
          & X0 != sK6
          & X0 != u1_struct_0(sK6)
          & X0 != k1_zfmisc_1(u1_struct_0(sK6))
          & X0 != arAF0_u1_pre_topc_0 )
        | ( X1 = k1_zfmisc_1(u1_struct_0(sK6))
          & X0 != u1_struct_0(X0)
          & X0 != sK7
          & X0 != sK6
          & X0 != u1_struct_0(sK6)
          & X0 != arAF0_u1_pre_topc_0 )
        | ? [X2] :
            ( X1 = u1_struct_0(X2)
            & X0 != u1_struct_0(X0)
            & ( X0 != u1_struct_0(X0)
              | X2 != sK6 )
            & X0 != sK7
            & X0 != sK6
            & ( X0 != sK6
              | X2 != sK6 )
            & X0 != u1_struct_0(sK6)
            & ( X0 != u1_struct_0(sK6)
              | X2 != sK6 )
            & X0 != k1_zfmisc_1(u1_struct_0(sK6))
            & X0 != arAF0_u1_pre_topc_0
            & ( X0 != arAF0_u1_pre_topc_0
              | X2 != sK6 ) )
        | ( X1 = arAF0_u1_pre_topc_0
          & X0 != u1_struct_0(X0)
          & X0 != sK7
          & X0 != sK6
          & X0 != u1_struct_0(sK6)
          & X0 != k1_zfmisc_1(u1_struct_0(sK6))
          & X0 != arAF0_u1_pre_topc_0 ) ) ) )).

%------ Positive definition of arAF0_sP1_0 
fof(lit_def_005,axiom,
    ( arAF0_sP1_0
  <=> $true )).

%------ Positive definition of arAF0_sP0_0 
fof(lit_def_006,axiom,
    ( arAF0_sP0_0
  <=> $true )).

%------ Positive definition of arAF0_m1_pre_topc_0 
fof(lit_def_007,axiom,
    ( arAF0_m1_pre_topc_0
  <=> $true )).

%------ Positive definition of arAF0_l1_pre_topc_0 
fof(lit_def_008,axiom,
    ( arAF0_l1_pre_topc_0
  <=> $true )).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:21:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 59.76/8.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 59.76/8.00  
% 59.76/8.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 59.76/8.00  
% 59.76/8.00  ------  iProver source info
% 59.76/8.00  
% 59.76/8.00  git: date: 2020-06-30 10:37:57 +0100
% 59.76/8.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 59.76/8.00  git: non_committed_changes: false
% 59.76/8.00  git: last_make_outside_of_git: false
% 59.76/8.00  
% 59.76/8.00  ------ 
% 59.76/8.00  ------ Parsing...
% 59.76/8.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 59.76/8.00  
% 59.76/8.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 59.76/8.00  
% 59.76/8.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 59.76/8.00  
% 59.76/8.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 59.76/8.00  ------ Proving...
% 59.76/8.00  ------ Problem Properties 
% 59.76/8.00  
% 59.76/8.00  
% 59.76/8.00  clauses                                 28
% 59.76/8.00  conjectures                             4
% 59.76/8.00  EPR                                     12
% 59.76/8.00  Horn                                    22
% 59.76/8.00  unary                                   5
% 59.76/8.00  binary                                  5
% 59.76/8.00  lits                                    80
% 59.76/8.00  lits eq                                 4
% 59.76/8.00  fd_pure                                 0
% 59.76/8.00  fd_pseudo                               0
% 59.76/8.00  fd_cond                                 1
% 59.76/8.00  fd_pseudo_cond                          0
% 59.76/8.00  AC symbols                              0
% 59.76/8.00  
% 59.76/8.00  ------ Input Options Time Limit: Unbounded
% 59.76/8.00  
% 59.76/8.00  
% 59.76/8.00  
% 59.76/8.00  
% 59.76/8.00  ------ Preprocessing...
% 59.76/8.00  
% 59.76/8.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e ------ 
% 59.76/8.00  Current options:
% 59.76/8.00  ------ 
% 59.76/8.00  
% 59.76/8.00  
% 59.76/8.00  
% 59.76/8.00  
% 59.76/8.00  ------ Proving...
% 59.76/8.00  
% 59.76/8.00  
% 59.76/8.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 59.76/8.00  
% 59.76/8.00  ------ Proving...
% 59.76/8.00  
% 59.76/8.00  
% 59.76/8.00  ------ Preprocessing...
% 59.76/8.00  
% 59.76/8.00  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 59.76/8.00  
% 59.76/8.00  ------ Proving...
% 59.76/8.00  
% 59.76/8.00  
% 59.76/8.00  ------ Preprocessing...
% 59.76/8.00  
% 59.76/8.00  ------ Preprocessing...
% 59.76/8.00  
% 59.76/8.00  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 59.76/8.00  
% 59.76/8.00  ------ Proving...
% 59.76/8.00  
% 59.76/8.00  
% 59.76/8.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 59.76/8.00  
% 59.76/8.00  ------ Proving...
% 59.76/8.00  
% 59.76/8.00  
% 59.76/8.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 59.76/8.00  
% 59.76/8.00  ------ Proving...
% 59.76/8.00  
% 59.76/8.00  
% 59.76/8.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 59.76/8.00  
% 59.76/8.00  ------ Proving...
% 59.76/8.00  
% 59.76/8.00  
% 59.76/8.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 59.76/8.00  
% 59.76/8.00  ------ Proving...
% 59.76/8.00  
% 59.76/8.00  
% 59.76/8.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 59.76/8.00  
% 59.76/8.00  ------ Proving...
% 59.76/8.00  
% 59.76/8.00  
% 59.76/8.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 59.76/8.00  
% 59.76/8.00  ------ Proving...
% 59.76/8.00  
% 59.76/8.00  
% 59.76/8.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 59.76/8.00  
% 59.76/8.00  ------ Proving...
% 59.76/8.00  
% 59.76/8.00  
% 59.76/8.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 59.76/8.00  
% 59.76/8.00  ------ Proving...
% 59.76/8.00  
% 59.76/8.00  
% 59.76/8.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 59.76/8.00  
% 59.76/8.00  ------ Proving...
% 59.76/8.00  
% 59.76/8.00  
% 59.76/8.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 59.76/8.00  
% 59.76/8.00  ------ Proving...
% 59.76/8.00  
% 59.76/8.00  
% 59.76/8.00  % SZS status CounterSatisfiable for theBenchmark.p
% 59.76/8.00  
% 59.76/8.00  ------ Building Model...Done
% 59.76/8.00  
% 59.76/8.00  %------ The model is defined over ground terms (initial term algebra).
% 59.76/8.00  %------ Predicates are defined as (\forall x_1,..,x_n  ((~)P(x_1,..,x_n) <=> (\phi(x_1,..,x_n)))) 
% 59.76/8.00  %------ where \phi is a formula over the term algebra.
% 59.76/8.00  %------ If we have equality in the problem then it is also defined as a predicate above, 
% 59.76/8.00  %------ with "=" on the right-hand-side of the definition interpreted over the term algebra term_algebra_type
% 59.76/8.00  %------ See help for --sat_out_model for different model outputs.
% 59.76/8.00  %------ equality_sorted(X0,X1,X2) can be used in the place of usual "="
% 59.76/8.00  %------ where the first argument stands for the sort ($i in the unsorted case)
% 59.76/8.00  % SZS output start Model for theBenchmark.p
% 59.76/8.00  
% 59.76/8.00  %------ Positive definition of equality_sorted 
% 59.76/8.00  fof(lit_def,axiom,
% 59.76/8.00      (! [X0_0,X0_2,X1_2] : 
% 59.76/8.00        ( equality_sorted(X0_0,X0_2,X1_2) <=>
% 59.76/8.00             (
% 59.76/8.00                (
% 59.76/8.00                  ( X0_0=$o & X1_2=X0_2 )
% 59.76/8.00                )
% 59.76/8.00  
% 59.76/8.00               | 
% 59.76/8.00                (
% 59.76/8.00                  ( X0_0=$i )
% 59.76/8.00                 &
% 59.76/8.00                  ( X0!=u1_struct_0(X0) )
% 59.76/8.00                 &
% 59.76/8.00                  ( X0!=sK7 )
% 59.76/8.00                 &
% 59.76/8.00                  ( X0!=sK5 | X1!=sK6 )
% 59.76/8.00                 &
% 59.76/8.00                  ( X0!=u1_struct_0(sK5) | X1!=u1_struct_0(sK6) )
% 59.76/8.00                 &
% 59.76/8.00                  ( X0!=k1_zfmisc_1(u1_struct_0(sK5)) | X1!=k1_zfmisc_1(u1_struct_0(sK6)) )
% 59.76/8.00                 &
% 59.76/8.00                  ( X0!=sK6 )
% 59.76/8.00                 &
% 59.76/8.00                  ( X0!=u1_struct_0(sK6) )
% 59.76/8.00                 &
% 59.76/8.00                  ( X0!=k1_zfmisc_1(u1_struct_0(sK6)) )
% 59.76/8.00                 &
% 59.76/8.00                  ( X0!=arAF0_u1_pre_topc_0 )
% 59.76/8.00                 &
% 59.76/8.00                  ( X1!=u1_struct_0(X1) )
% 59.76/8.00                 &
% 59.76/8.00                  ( X1!=sK7 )
% 59.76/8.00                 &
% 59.76/8.00                  ( X1!=sK6 )
% 59.76/8.00                 &
% 59.76/8.00                  ( X1!=u1_struct_0(sK6) )
% 59.76/8.00                 &
% 59.76/8.00                  ( X1!=k1_zfmisc_1(u1_struct_0(sK6)) )
% 59.76/8.00                 &
% 59.76/8.00                  ( X1!=arAF0_u1_pre_topc_0 )
% 59.76/8.00                )
% 59.76/8.00  
% 59.76/8.00               | 
% 59.76/8.00                (
% 59.76/8.00                  ( X0_0=$i & X0=k1_xboole_0 )
% 59.76/8.00                 &
% 59.76/8.00                  ( X1!=u1_struct_0(X1) )
% 59.76/8.00                 &
% 59.76/8.00                  ( X1!=sK7 )
% 59.76/8.00                 &
% 59.76/8.00                  ( X1!=sK6 )
% 59.76/8.00                 &
% 59.76/8.00                  ( X1!=u1_struct_0(sK6) )
% 59.76/8.00                 &
% 59.76/8.00                  ( X1!=k1_zfmisc_1(u1_struct_0(sK6)) )
% 59.76/8.00                 &
% 59.76/8.00                  ( X1!=arAF0_u1_pre_topc_0 )
% 59.76/8.00                )
% 59.76/8.00  
% 59.76/8.00               | 
% 59.76/8.00              ? [X2,X3] : 
% 59.76/8.00                (
% 59.76/8.00                  ( X0_0=$i & X0=k1_zfmisc_1(X2) & X1=k1_zfmisc_1(X3) )
% 59.76/8.00                 &
% 59.76/8.00                  ( X2!=u1_struct_0(sK5) | X3!=u1_struct_0(sK6) )
% 59.76/8.00                 &
% 59.76/8.00                  ( X2!=u1_struct_0(sK6) )
% 59.76/8.00                 &
% 59.76/8.00                  ( X3!=u1_struct_0(sK6) )
% 59.76/8.00                )
% 59.76/8.00  
% 59.76/8.00               | 
% 59.76/8.00              ? [X2] : 
% 59.76/8.00                (
% 59.76/8.00                  ( X0_0=$i & X0=u1_struct_0(sK5) & X1=u1_struct_0(X2) )
% 59.76/8.00                 &
% 59.76/8.00                  ( X2!=sK6 )
% 59.76/8.00                )
% 59.76/8.00  
% 59.76/8.00               | 
% 59.76/8.00                (
% 59.76/8.00                  ( X0_0=$i & X0=u1_struct_0(sK6) & X1=u1_struct_0(sK6) )
% 59.76/8.00                )
% 59.76/8.00  
% 59.76/8.00               | 
% 59.76/8.00                (
% 59.76/8.00                  ( X0_0=$i & X0=k1_zfmisc_1(u1_struct_0(sK6)) & X1=k1_zfmisc_1(u1_struct_0(sK6)) )
% 59.76/8.00                )
% 59.76/8.00  
% 59.76/8.00               | 
% 59.76/8.00              ? [X2,X3] : 
% 59.76/8.00                (
% 59.76/8.00                  ( X0_0=$i & X0=u1_struct_0(X2) & X1=u1_struct_0(X3) )
% 59.76/8.00                 &
% 59.76/8.00                  ( X2!=sK5 )
% 59.76/8.00                 &
% 59.76/8.00                  ( X2!=sK5 | X3!=sK6 )
% 59.76/8.00                 &
% 59.76/8.00                  ( X2!=sK6 )
% 59.76/8.00                 &
% 59.76/8.00                  ( X3!=sK6 )
% 59.76/8.00                )
% 59.76/8.00  
% 59.76/8.00               | 
% 59.76/8.00                (
% 59.76/8.00                  ( X0_0=$i & X0=arAF0_k9_subset_1_0 )
% 59.76/8.00                 &
% 59.76/8.00                  ( X1!=u1_struct_0(X1) )
% 59.76/8.00                 &
% 59.76/8.00                  ( X1!=sK7 )
% 59.76/8.00                 &
% 59.76/8.00                  ( X1!=sK6 )
% 59.76/8.00                 &
% 59.76/8.00                  ( X1!=u1_struct_0(sK6) )
% 59.76/8.00                 &
% 59.76/8.00                  ( X1!=k1_zfmisc_1(u1_struct_0(sK6)) )
% 59.76/8.00                 &
% 59.76/8.00                  ( X1!=arAF0_u1_pre_topc_0 )
% 59.76/8.00                )
% 59.76/8.00  
% 59.76/8.00               | 
% 59.76/8.00                (
% 59.76/8.00                  ( X0_0=$i & X1=X0 )
% 59.76/8.00                )
% 59.76/8.00  
% 59.76/8.00             )
% 59.76/8.00        )
% 59.76/8.00      )
% 59.76/8.00     ).
% 59.76/8.00  
% 59.76/8.00  %------ Negative definition of v1_xboole_0 
% 59.76/8.00  fof(lit_def,axiom,
% 59.76/8.00      (! [X0] : 
% 59.76/8.00        ( ~(v1_xboole_0(X0)) <=>
% 59.76/8.00             (
% 59.76/8.00              ? [X1] : 
% 59.76/8.00                (
% 59.76/8.00                  ( X0=u1_struct_0(X1) )
% 59.76/8.00                )
% 59.76/8.00  
% 59.76/8.00               | 
% 59.76/8.00                (
% 59.76/8.00                  ( X0=sK7 )
% 59.76/8.00                )
% 59.76/8.00  
% 59.76/8.00               | 
% 59.76/8.00                (
% 59.76/8.00                  ( X0=sK6 )
% 59.76/8.00                )
% 59.76/8.00  
% 59.76/8.00               | 
% 59.76/8.00                (
% 59.76/8.00                  ( X0=u1_struct_0(sK6) )
% 59.76/8.00                )
% 59.76/8.00  
% 59.76/8.00               | 
% 59.76/8.00                (
% 59.76/8.00                  ( X0=k1_zfmisc_1(u1_struct_0(sK6)) )
% 59.76/8.00                )
% 59.76/8.00  
% 59.76/8.00               | 
% 59.76/8.00                (
% 59.76/8.00                  ( X0=arAF0_u1_pre_topc_0 )
% 59.76/8.00                )
% 59.76/8.00  
% 59.76/8.00             )
% 59.76/8.00        )
% 59.76/8.00      )
% 59.76/8.00     ).
% 59.76/8.00  
% 59.76/8.00  %------ Negative definition of r1_tarski 
% 59.76/8.00  fof(lit_def,axiom,
% 59.76/8.00      (! [X0,X1] : 
% 59.76/8.00        ( ~(r1_tarski(X0,X1)) <=>
% 59.76/8.00             (
% 59.76/8.00                (
% 59.76/8.00                  ( X0=sK7 )
% 59.76/8.00                 &
% 59.76/8.00                  ( X1!=u1_struct_0(sK6) )
% 59.76/8.00                )
% 59.76/8.00  
% 59.76/8.00               | 
% 59.76/8.00                (
% 59.76/8.00                  ( X0=sK7 & X1=u1_struct_0(sK5) )
% 59.76/8.00                )
% 59.76/8.00  
% 59.76/8.00               | 
% 59.76/8.00                (
% 59.76/8.00                  ( X0=sK6 )
% 59.76/8.00                )
% 59.76/8.00  
% 59.76/8.00               | 
% 59.76/8.00                (
% 59.76/8.00                  ( X0=u1_struct_0(sK6) )
% 59.76/8.00                )
% 59.76/8.00  
% 59.76/8.00               | 
% 59.76/8.00                (
% 59.76/8.00                  ( X0=k1_zfmisc_1(u1_struct_0(sK6)) )
% 59.76/8.00                 &
% 59.76/8.00                  ( X1!=k1_zfmisc_1(X1) )
% 59.76/8.00                 &
% 59.76/8.00                  ( X1!=u1_struct_0(sK6) )
% 59.76/8.00                )
% 59.76/8.00  
% 59.76/8.00               | 
% 59.76/8.00              ? [X2] : 
% 59.76/8.00                (
% 59.76/8.00                  ( X0=k1_zfmisc_1(u1_struct_0(sK6)) & X1=k1_zfmisc_1(X2) )
% 59.76/8.00                )
% 59.76/8.00  
% 59.76/8.00               | 
% 59.76/8.00              ? [X2] : 
% 59.76/8.00                (
% 59.76/8.00                  ( X0=u1_struct_0(X2) )
% 59.76/8.00                )
% 59.76/8.00  
% 59.76/8.00               | 
% 59.76/8.00                (
% 59.76/8.00                  ( X0=arAF0_u1_pre_topc_0 )
% 59.76/8.00                )
% 59.76/8.00  
% 59.76/8.00             )
% 59.76/8.00        )
% 59.76/8.00      )
% 59.76/8.00     ).
% 59.76/8.00  
% 59.76/8.00  %------ Positive definition of m1_subset_1 
% 59.76/8.00  fof(lit_def,axiom,
% 59.76/8.00      (! [X0,X1] : 
% 59.76/8.00        ( m1_subset_1(X0,X1) <=>
% 59.76/8.00             (
% 59.76/8.00                (
% 59.76/8.00                  ( X0!=u1_struct_0(X0) )
% 59.76/8.00                 &
% 59.76/8.00                  ( X0!=u1_struct_0(X0) | X1!=k1_zfmisc_1(X1) )
% 59.76/8.00                 &
% 59.76/8.00                  ( X0!=sK7 )
% 59.76/8.00                 &
% 59.76/8.00                  ( X0!=sK7 | X1!=k1_zfmisc_1(u1_struct_0(sK5)) )
% 59.76/8.00                 &
% 59.76/8.00                  ( X0!=sK6 )
% 59.76/8.00                 &
% 59.76/8.00                  ( X0!=u1_struct_0(sK6) )
% 59.76/8.00                 &
% 59.76/8.00                  ( X0!=u1_struct_0(sK6) | X1!=k1_zfmisc_1(X0) )
% 59.76/8.00                 &
% 59.76/8.00                  ( X0!=u1_struct_0(sK6) | X1!=k1_zfmisc_1(X2) )
% 59.76/8.00                 &
% 59.76/8.00                  ( X0!=k1_zfmisc_1(u1_struct_0(sK6)) )
% 59.76/8.00                 &
% 59.76/8.00                  ( X0!=arAF0_u1_pre_topc_0 )
% 59.76/8.00                )
% 59.76/8.00  
% 59.76/8.00               | 
% 59.76/8.00                (
% 59.76/8.00                  ( X0=sK7 & X1=sK7 )
% 59.76/8.00                )
% 59.76/8.00  
% 59.76/8.00               | 
% 59.76/8.00                (
% 59.76/8.00                  ( X0=sK7 & X1=u1_struct_0(sK6) )
% 59.76/8.00                )
% 59.76/8.00  
% 59.76/8.00               | 
% 59.76/8.00                (
% 59.76/8.00                  ( X0=sK7 & X1=k1_zfmisc_1(u1_struct_0(sK6)) )
% 59.76/8.00                )
% 59.76/8.00  
% 59.76/8.00               | 
% 59.76/8.00                (
% 59.76/8.00                  ( X0=k1_zfmisc_1(u1_struct_0(sK6)) & X1=u1_struct_0(sK6) )
% 59.76/8.00                )
% 59.76/8.00  
% 59.76/8.00               | 
% 59.76/8.00                (
% 59.76/8.00                  ( X0=k1_zfmisc_1(u1_struct_0(sK6)) & X1=k1_zfmisc_1(u1_struct_0(sK6)) )
% 59.76/8.00                )
% 59.76/8.00  
% 59.76/8.00               | 
% 59.76/8.00              ? [X2] : 
% 59.76/8.00                (
% 59.76/8.00                  ( X0=arAF0_sK4_0 & X1=k1_zfmisc_1(u1_struct_0(X2)) )
% 59.76/8.00                )
% 59.76/8.00  
% 59.76/8.00               | 
% 59.76/8.00              ? [X2] : 
% 59.76/8.00                (
% 59.76/8.00                  ( X1=k1_zfmisc_1(X2) )
% 59.76/8.00                 &
% 59.76/8.00                  ( X0!=u1_struct_0(X0) )
% 59.76/8.00                 &
% 59.76/8.00                  ( X0!=sK7 )
% 59.76/8.00                 &
% 59.76/8.00                  ( X0!=sK7 | X2!=u1_struct_0(sK5) )
% 59.76/8.00                 &
% 59.76/8.00                  ( X0!=sK6 )
% 59.76/8.00                 &
% 59.76/8.00                  ( X0!=u1_struct_0(sK6) )
% 59.76/8.00                 &
% 59.76/8.00                  ( X0!=k1_zfmisc_1(u1_struct_0(sK6)) )
% 59.76/8.00                 &
% 59.76/8.00                  ( X0!=arAF0_u1_pre_topc_0 )
% 59.76/8.00                )
% 59.76/8.00  
% 59.76/8.00               | 
% 59.76/8.00                (
% 59.76/8.00                  ( X1=sK7 )
% 59.76/8.00                 &
% 59.76/8.00                  ( X0!=u1_struct_0(X0) )
% 59.76/8.00                 &
% 59.76/8.00                  ( X0!=sK7 )
% 59.76/8.00                 &
% 59.76/8.00                  ( X0!=sK6 )
% 59.76/8.00                 &
% 59.76/8.00                  ( X0!=arAF0_u1_pre_topc_0 )
% 59.76/8.00                )
% 59.76/8.00  
% 59.76/8.00               | 
% 59.76/8.00                (
% 59.76/8.00                  ( X1=sK6 )
% 59.76/8.00                 &
% 59.76/8.00                  ( X0!=u1_struct_0(X0) )
% 59.76/8.00                 &
% 59.76/8.00                  ( X0!=sK7 )
% 59.76/8.00                 &
% 59.76/8.00                  ( X0!=sK6 )
% 59.76/8.00                 &
% 59.76/8.00                  ( X0!=k1_zfmisc_1(u1_struct_0(sK6)) )
% 59.76/8.00                 &
% 59.76/8.00                  ( X0!=arAF0_u1_pre_topc_0 )
% 59.76/8.00                )
% 59.76/8.00  
% 59.76/8.00               | 
% 59.76/8.00                (
% 59.76/8.00                  ( X1=u1_struct_0(sK6) )
% 59.76/8.00                 &
% 59.76/8.00                  ( X0!=u1_struct_0(X0) )
% 59.76/8.00                 &
% 59.76/8.00                  ( X0!=sK7 )
% 59.76/8.00                 &
% 59.76/8.00                  ( X0!=sK6 )
% 59.76/8.00                 &
% 59.76/8.00                  ( X0!=u1_struct_0(sK6) )
% 59.76/8.00                 &
% 59.76/8.00                  ( X0!=k1_zfmisc_1(u1_struct_0(sK6)) )
% 59.76/8.00                 &
% 59.76/8.00                  ( X0!=arAF0_u1_pre_topc_0 )
% 59.76/8.00                )
% 59.76/8.00  
% 59.76/8.00               | 
% 59.76/8.00                (
% 59.76/8.00                  ( X1=k1_zfmisc_1(u1_struct_0(sK6)) )
% 59.76/8.00                 &
% 59.76/8.00                  ( X0!=u1_struct_0(X0) )
% 59.76/8.00                 &
% 59.76/8.00                  ( X0!=sK7 )
% 59.76/8.00                 &
% 59.76/8.00                  ( X0!=sK6 )
% 59.76/8.00                 &
% 59.76/8.00                  ( X0!=u1_struct_0(sK6) )
% 59.76/8.00                 &
% 59.76/8.00                  ( X0!=k1_zfmisc_1(u1_struct_0(sK6)) )
% 59.76/8.00                 &
% 59.76/8.00                  ( X0!=arAF0_u1_pre_topc_0 )
% 59.76/8.00                )
% 59.76/8.00  
% 59.76/8.00               | 
% 59.76/8.00              ? [X2] : 
% 59.76/8.00                (
% 59.76/8.00                  ( X1=u1_struct_0(X2) )
% 59.76/8.00                 &
% 59.76/8.00                  ( X0!=u1_struct_0(X0) )
% 59.76/8.00                 &
% 59.76/8.00                  ( X0!=u1_struct_0(X0) | X2!=sK6 )
% 59.76/8.00                 &
% 59.76/8.00                  ( X0!=sK7 )
% 59.76/8.00                 &
% 59.76/8.00                  ( X0!=sK6 )
% 59.76/8.00                 &
% 59.76/8.00                  ( X0!=sK6 | X2!=sK6 )
% 59.76/8.00                 &
% 59.76/8.00                  ( X0!=u1_struct_0(sK6) | X2!=sK6 )
% 59.76/8.00                 &
% 59.76/8.00                  ( X0!=k1_zfmisc_1(u1_struct_0(sK6)) )
% 59.76/8.00                 &
% 59.76/8.00                  ( X0!=arAF0_u1_pre_topc_0 )
% 59.76/8.00                 &
% 59.76/8.00                  ( X0!=arAF0_u1_pre_topc_0 | X2!=sK6 )
% 59.76/8.00                )
% 59.76/8.00  
% 59.76/8.00               | 
% 59.76/8.00                (
% 59.76/8.00                  ( X1=arAF0_u1_pre_topc_0 )
% 59.76/8.00                 &
% 59.76/8.00                  ( X0!=u1_struct_0(X0) )
% 59.76/8.00                 &
% 59.76/8.00                  ( X0!=sK7 )
% 59.76/8.00                 &
% 59.76/8.00                  ( X0!=sK6 )
% 59.76/8.00                 &
% 59.76/8.00                  ( X0!=k1_zfmisc_1(u1_struct_0(sK6)) )
% 59.76/8.00                 &
% 59.76/8.00                  ( X0!=arAF0_u1_pre_topc_0 )
% 59.76/8.00                )
% 59.76/8.00  
% 59.76/8.00             )
% 59.76/8.00        )
% 59.76/8.00      )
% 59.76/8.00     ).
% 59.76/8.00  
% 59.76/8.00  %------ Positive definition of r2_hidden 
% 59.76/8.00  fof(lit_def,axiom,
% 59.76/8.00      (! [X0,X1] : 
% 59.76/8.00        ( r2_hidden(X0,X1) <=>
% 59.76/8.00             (
% 59.76/8.00                (
% 59.76/8.00                  ( X0!=u1_struct_0(X0) )
% 59.76/8.00                 &
% 59.76/8.00                  ( X0!=sK7 )
% 59.76/8.00                 &
% 59.76/8.00                  ( X0!=sK6 )
% 59.76/8.00                 &
% 59.76/8.00                  ( X0!=sK6 | X1!=arAF0_u1_pre_topc_0 )
% 59.76/8.00                 &
% 59.76/8.00                  ( X0!=u1_struct_0(sK6) )
% 59.76/8.00                 &
% 59.76/8.00                  ( X0!=k1_zfmisc_1(u1_struct_0(sK6)) )
% 59.76/8.00                 &
% 59.76/8.00                  ( X0!=arAF0_u1_pre_topc_0 )
% 59.76/8.00                 &
% 59.76/8.00                  ( X0!=arAF0_u1_pre_topc_0 | X1!=arAF0_u1_pre_topc_0 )
% 59.76/8.00                )
% 59.76/8.00  
% 59.76/8.00               | 
% 59.76/8.00                (
% 59.76/8.00                  ( X0=sK7 & X1=sK7 )
% 59.76/8.00                )
% 59.76/8.00  
% 59.76/8.00               | 
% 59.76/8.00                (
% 59.76/8.00                  ( X0=sK7 & X1=u1_struct_0(sK6) )
% 59.76/8.00                )
% 59.76/8.00  
% 59.76/8.00               | 
% 59.76/8.00                (
% 59.76/8.00                  ( X0=sK7 & X1=k1_zfmisc_1(u1_struct_0(sK6)) )
% 59.76/8.00                )
% 59.76/8.00  
% 59.76/8.00               | 
% 59.76/8.00                (
% 59.76/8.00                  ( X0=k1_zfmisc_1(u1_struct_0(sK6)) & X1=u1_struct_0(sK6) )
% 59.76/8.00                )
% 59.76/8.00  
% 59.76/8.00               | 
% 59.76/8.00                (
% 59.76/8.00                  ( X0=arAF0_k9_subset_1_0 & X1=arAF0_u1_pre_topc_0 )
% 59.76/8.00                )
% 59.76/8.00  
% 59.76/8.00               | 
% 59.76/8.00                (
% 59.76/8.00                  ( X0=arAF0_sK4_0 & X1=arAF0_u1_pre_topc_0 )
% 59.76/8.00                )
% 59.76/8.00  
% 59.76/8.00               | 
% 59.76/8.00                (
% 59.76/8.00                  ( X1=sK7 )
% 59.76/8.00                 &
% 59.76/8.00                  ( X0!=u1_struct_0(X0) )
% 59.76/8.00                 &
% 59.76/8.00                  ( X0!=sK7 )
% 59.76/8.00                 &
% 59.76/8.00                  ( X0!=sK6 )
% 59.76/8.00                 &
% 59.76/8.00                  ( X0!=u1_struct_0(sK6) )
% 59.76/8.00                 &
% 59.76/8.00                  ( X0!=arAF0_u1_pre_topc_0 )
% 59.76/8.00                )
% 59.76/8.00  
% 59.76/8.00               | 
% 59.76/8.00                (
% 59.76/8.00                  ( X1=sK6 )
% 59.76/8.00                 &
% 59.76/8.00                  ( X0!=u1_struct_0(X0) )
% 59.76/8.00                 &
% 59.76/8.00                  ( X0!=sK7 )
% 59.76/8.00                 &
% 59.76/8.00                  ( X0!=sK6 )
% 59.76/8.00                 &
% 59.76/8.00                  ( X0!=k1_zfmisc_1(u1_struct_0(sK6)) )
% 59.76/8.00                 &
% 59.76/8.00                  ( X0!=arAF0_u1_pre_topc_0 )
% 59.76/8.00                )
% 59.76/8.00  
% 59.76/8.00               | 
% 59.76/8.00                (
% 59.76/8.00                  ( X1=u1_struct_0(sK6) )
% 59.76/8.00                 &
% 59.76/8.00                  ( X0!=u1_struct_0(X0) )
% 59.76/8.00                 &
% 59.76/8.00                  ( X0!=sK7 )
% 59.76/8.00                 &
% 59.76/8.00                  ( X0!=sK6 )
% 59.76/8.00                 &
% 59.76/8.00                  ( X0!=u1_struct_0(sK6) )
% 59.76/8.00                 &
% 59.76/8.00                  ( X0!=k1_zfmisc_1(u1_struct_0(sK6)) )
% 59.76/8.00                 &
% 59.76/8.00                  ( X0!=arAF0_u1_pre_topc_0 )
% 59.76/8.00                )
% 59.76/8.00  
% 59.76/8.00               | 
% 59.76/8.00                (
% 59.76/8.00                  ( X1=k1_zfmisc_1(u1_struct_0(sK6)) )
% 59.76/8.00                 &
% 59.76/8.00                  ( X0!=u1_struct_0(X0) )
% 59.76/8.00                 &
% 59.76/8.00                  ( X0!=sK7 )
% 59.76/8.00                 &
% 59.76/8.00                  ( X0!=sK6 )
% 59.76/8.00                 &
% 59.76/8.00                  ( X0!=u1_struct_0(sK6) )
% 59.76/8.00                 &
% 59.76/8.00                  ( X0!=arAF0_u1_pre_topc_0 )
% 59.76/8.00                )
% 59.76/8.00  
% 59.76/8.00               | 
% 59.76/8.00              ? [X2] : 
% 59.76/8.00                (
% 59.76/8.00                  ( X1=u1_struct_0(X2) )
% 59.76/8.00                 &
% 59.76/8.00                  ( X0!=u1_struct_0(X0) )
% 59.76/8.00                 &
% 59.76/8.00                  ( X0!=u1_struct_0(X0) | X2!=sK6 )
% 59.76/8.00                 &
% 59.76/8.00                  ( X0!=sK7 )
% 59.76/8.00                 &
% 59.76/8.00                  ( X0!=sK6 )
% 59.76/8.00                 &
% 59.76/8.00                  ( X0!=sK6 | X2!=sK6 )
% 59.76/8.00                 &
% 59.76/8.00                  ( X0!=u1_struct_0(sK6) )
% 59.76/8.00                 &
% 59.76/8.00                  ( X0!=u1_struct_0(sK6) | X2!=sK6 )
% 59.76/8.00                 &
% 59.76/8.00                  ( X0!=k1_zfmisc_1(u1_struct_0(sK6)) )
% 59.76/8.00                 &
% 59.76/8.00                  ( X0!=arAF0_u1_pre_topc_0 )
% 59.76/8.00                 &
% 59.76/8.00                  ( X0!=arAF0_u1_pre_topc_0 | X2!=sK6 )
% 59.76/8.00                )
% 59.76/8.00  
% 59.76/8.00               | 
% 59.76/8.00                (
% 59.76/8.00                  ( X1=arAF0_u1_pre_topc_0 )
% 59.76/8.00                 &
% 59.76/8.00                  ( X0!=u1_struct_0(X0) )
% 59.76/8.00                 &
% 59.76/8.00                  ( X0!=sK7 )
% 59.76/8.00                 &
% 59.76/8.00                  ( X0!=sK6 )
% 59.76/8.00                 &
% 59.76/8.00                  ( X0!=u1_struct_0(sK6) )
% 59.76/8.00                 &
% 59.76/8.00                  ( X0!=k1_zfmisc_1(u1_struct_0(sK6)) )
% 59.76/8.00                 &
% 59.76/8.00                  ( X0!=arAF0_u1_pre_topc_0 )
% 59.76/8.00                )
% 59.76/8.00  
% 59.76/8.00             )
% 59.76/8.00        )
% 59.76/8.00      )
% 59.76/8.00     ).
% 59.76/8.00  
% 59.76/8.00  %------ Positive definition of arAF0_sP1_0 
% 59.76/8.00  fof(lit_def,axiom,
% 59.76/8.00        ( arAF0_sP1_0 <=>
% 59.76/8.00            $true
% 59.76/8.00        )
% 59.76/8.00     ).
% 59.76/8.00  
% 59.76/8.00  %------ Positive definition of arAF0_sP0_0 
% 59.76/8.00  fof(lit_def,axiom,
% 59.76/8.00        ( arAF0_sP0_0 <=>
% 59.76/8.00            $true
% 59.76/8.00        )
% 59.76/8.00     ).
% 59.76/8.00  
% 59.76/8.00  %------ Positive definition of arAF0_m1_pre_topc_0 
% 59.76/8.00  fof(lit_def,axiom,
% 59.76/8.00        ( arAF0_m1_pre_topc_0 <=>
% 59.76/8.00            $true
% 59.76/8.00        )
% 59.76/8.00     ).
% 59.76/8.00  
% 59.76/8.00  %------ Positive definition of arAF0_l1_pre_topc_0 
% 59.76/8.00  fof(lit_def,axiom,
% 59.76/8.00        ( arAF0_l1_pre_topc_0 <=>
% 59.76/8.00            $true
% 59.76/8.00        )
% 59.76/8.00     ).
% 59.76/8.00  % SZS output end Model for theBenchmark.p
% 59.76/8.00  ------                               Statistics
% 59.76/8.00  
% 59.76/8.00  ------ Selected
% 59.76/8.00  
% 59.76/8.00  total_time:                             7.4
% 59.76/8.00  
%------------------------------------------------------------------------------
