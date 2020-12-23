%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:11:26 EST 2020

% Result     : CounterSatisfiable 3.68s
% Output     : Model 3.68s
% Verified   : 
% Statistics : Number of formulae       :    8 (   8 expanded)
%              Number of leaves         :    8 (   8 expanded)
%              Depth                    :    0
%              Number of atoms          :  146 ( 146 expanded)
%              Number of equality atoms :  133 ( 133 expanded)
%              Maximal formula depth    :   34 (  10 average)
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
          & X0 != sK7
          & X0 != sK6
          & X0 != u1_struct_0(sK6)
          & X0 != k1_zfmisc_1(u1_struct_0(sK6))
          & X0 != arAF0_k2_xboole_0_0
          & X0 != arAF0_k2_struct_0_0
          & X0 != k1_zfmisc_1(arAF0_k2_xboole_0_0)
          & X0 != k1_zfmisc_1(arAF0_k2_struct_0_0)
          & X1 != sK7
          & X1 != sK6
          & X1 != u1_struct_0(sK6)
          & X1 != k1_zfmisc_1(u1_struct_0(sK6))
          & X1 != arAF0_k2_xboole_0_0
          & X1 != arAF0_k2_struct_0_0
          & X1 != k1_zfmisc_1(arAF0_k2_xboole_0_0)
          & X1 != k1_zfmisc_1(arAF0_k2_struct_0_0) )
        | ? [X2,X3] :
            ( X0_0 = $i
            & X0 = u1_struct_0(X2)
            & X1 = u1_struct_0(X3)
            & X2 != sK6
            & X3 != sK6 )
        | ( X0_0 = $i
          & X0 = u1_struct_0(sK6)
          & X1 = u1_struct_0(sK6) )
        | ( X0_0 = $i
          & X0 = u1_struct_0(sK6)
          & X1 = arAF0_k2_xboole_0_0 )
        | ( X0_0 = $i
          & X0 = u1_struct_0(sK6)
          & X1 = arAF0_k2_struct_0_0 )
        | ( X0_0 = $i
          & X0 = k1_zfmisc_1(u1_struct_0(sK6))
          & X1 = k1_zfmisc_1(u1_struct_0(sK6)) )
        | ( X0_0 = $i
          & X0 = k1_zfmisc_1(u1_struct_0(sK6))
          & X1 = k1_zfmisc_1(arAF0_k2_xboole_0_0) )
        | ( X0_0 = $i
          & X0 = k1_zfmisc_1(u1_struct_0(sK6))
          & X1 = k1_zfmisc_1(arAF0_k2_struct_0_0) )
        | ( X0_0 = $i
          & X0 = arAF0_k2_xboole_0_0
          & X1 = u1_struct_0(sK6) )
        | ( X0_0 = $i
          & X0 = arAF0_k2_xboole_0_0
          & X1 = arAF0_k2_struct_0_0 )
        | ( X0_0 = $i
          & X0 = arAF0_k2_struct_0_0
          & X1 = u1_struct_0(sK6) )
        | ( X0_0 = $i
          & X0 = arAF0_k2_struct_0_0
          & X1 = arAF0_k2_xboole_0_0 )
        | ( X0_0 = $i
          & X0 = k1_zfmisc_1(arAF0_k2_xboole_0_0)
          & X1 = k1_zfmisc_1(u1_struct_0(sK6)) )
        | ( X0_0 = $i
          & X0 = k1_zfmisc_1(arAF0_k2_xboole_0_0)
          & X1 = k1_zfmisc_1(arAF0_k2_xboole_0_0) )
        | ( X0_0 = $i
          & X0 = k1_zfmisc_1(arAF0_k2_xboole_0_0)
          & X1 = k1_zfmisc_1(arAF0_k2_struct_0_0) )
        | ? [X2,X3] :
            ( X0_0 = $i
            & X0 = k1_zfmisc_1(X2)
            & X1 = k1_zfmisc_1(X3)
            & ( X2 != u1_struct_0(sK5)
              | X3 != u1_struct_0(sK6) )
            & X2 != u1_struct_0(sK6)
            & X2 != arAF0_k2_xboole_0_0
            & X2 != arAF0_k2_struct_0_0
            & X3 != u1_struct_0(sK6)
            & X3 != arAF0_k2_xboole_0_0
            & X3 != arAF0_k2_struct_0_0 )
        | ( X0_0 = $i
          & X0 = k1_zfmisc_1(arAF0_k2_struct_0_0)
          & X1 = k1_zfmisc_1(u1_struct_0(sK6)) )
        | ( X0_0 = $i
          & X0 = k1_zfmisc_1(arAF0_k2_struct_0_0)
          & X1 = k1_zfmisc_1(arAF0_k2_xboole_0_0) )
        | ( X0_0 = $i
          & X0 = k1_zfmisc_1(arAF0_k2_struct_0_0)
          & X1 = k1_zfmisc_1(arAF0_k2_struct_0_0) )
        | ( X0_0 = $i
          & X1 = X0 ) ) ) )).

%------ Positive definition of r1_tarski 
fof(lit_def_001,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ( ( X0 = sK7
          & X1 = u1_struct_0(sK6) )
        | ( X0 = sK7
          & X1 = arAF0_k2_xboole_0_0 )
        | ( X0 = sK7
          & X1 = arAF0_k2_struct_0_0 )
        | ( X0 = u1_struct_0(sK6)
          & X1 = u1_struct_0(sK6) )
        | ( X0 = u1_struct_0(sK6)
          & X1 = arAF0_k2_xboole_0_0 )
        | ( X0 = u1_struct_0(sK6)
          & X1 = arAF0_k2_struct_0_0 )
        | ( X0 = arAF0_k2_xboole_0_0
          & X1 = u1_struct_0(sK6) )
        | ( X0 = arAF0_k2_xboole_0_0
          & X1 = arAF0_k2_xboole_0_0 )
        | ( X0 = arAF0_k2_xboole_0_0
          & X1 = arAF0_k2_struct_0_0 )
        | ( X0 = arAF0_k2_struct_0_0
          & X1 = u1_struct_0(sK6) )
        | ( X0 = arAF0_k2_struct_0_0
          & X1 = arAF0_k2_xboole_0_0 )
        | ( X0 = arAF0_k2_struct_0_0
          & X1 = arAF0_k2_struct_0_0 ) ) ) )).

%------ Positive definition of m1_subset_1 
fof(lit_def_002,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
    <=> ( ( X0 = sK7
          & X1 = k1_zfmisc_1(u1_struct_0(sK6)) )
        | ( X0 = sK7
          & X1 = k1_zfmisc_1(arAF0_k2_xboole_0_0) )
        | ( X0 = sK7
          & X1 = k1_zfmisc_1(arAF0_k2_struct_0_0) )
        | ( X0 = u1_struct_0(sK6)
          & X1 = k1_zfmisc_1(u1_struct_0(sK6)) )
        | ( X0 = u1_struct_0(sK6)
          & X1 = k1_zfmisc_1(arAF0_k2_xboole_0_0) )
        | ( X0 = u1_struct_0(sK6)
          & X1 = k1_zfmisc_1(arAF0_k2_struct_0_0) )
        | ( X0 = arAF0_k2_xboole_0_0
          & X1 = k1_zfmisc_1(u1_struct_0(sK6)) )
        | ( X0 = arAF0_k2_xboole_0_0
          & X1 = k1_zfmisc_1(arAF0_k2_xboole_0_0) )
        | ( X0 = arAF0_k2_xboole_0_0
          & X1 = k1_zfmisc_1(arAF0_k2_struct_0_0) )
        | ( X0 = arAF0_k2_struct_0_0
          & X1 = k1_zfmisc_1(u1_struct_0(sK6)) )
        | ( X0 = arAF0_k2_struct_0_0
          & X1 = k1_zfmisc_1(arAF0_k2_xboole_0_0) )
        | ( X0 = arAF0_k2_struct_0_0
          & X1 = k1_zfmisc_1(arAF0_k2_struct_0_0) ) ) ) )).

%------ Positive definition of l1_pre_topc 
fof(lit_def_003,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
    <=> $true ) )).

%------ Positive definition of arAF0_r2_hidden_0 
fof(lit_def_004,axiom,
    ( arAF0_r2_hidden_0
  <=> $false )).

%------ Positive definition of arAF0_sP1_0_1 
fof(lit_def_005,axiom,(
    ! [X0] :
      ( arAF0_sP1_0_1(X0)
    <=> $true ) )).

%------ Positive definition of arAF0_sP0_0_1 
fof(lit_def_006,axiom,(
    ! [X0] :
      ( arAF0_sP0_0_1(X0)
    <=> $true ) )).

%------ Positive definition of arAF0_m1_pre_topc_0_1 
fof(lit_def_007,axiom,(
    ! [X0] :
      ( arAF0_m1_pre_topc_0_1(X0)
    <=> $true ) )).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:10:32 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 3.68/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.68/0.98  
% 3.68/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.68/0.98  
% 3.68/0.98  ------  iProver source info
% 3.68/0.98  
% 3.68/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.68/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.68/0.98  git: non_committed_changes: false
% 3.68/0.98  git: last_make_outside_of_git: false
% 3.68/0.98  
% 3.68/0.98  ------ 
% 3.68/0.98  ------ Parsing...
% 3.68/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.68/0.98  
% 3.68/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.68/0.98  
% 3.68/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.68/0.98  
% 3.68/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.68/0.98  ------ Proving...
% 3.68/0.98  ------ Problem Properties 
% 3.68/0.98  
% 3.68/0.98  
% 3.68/0.98  clauses                                 23
% 3.68/0.98  conjectures                             4
% 3.68/0.98  EPR                                     6
% 3.68/0.98  Horn                                    19
% 3.68/0.98  unary                                   5
% 3.68/0.98  binary                                  5
% 3.68/0.98  lits                                    65
% 3.68/0.98  lits eq                                 5
% 3.68/0.98  fd_pure                                 0
% 3.68/0.98  fd_pseudo                               0
% 3.68/0.98  fd_cond                                 0
% 3.68/0.98  fd_pseudo_cond                          0
% 3.68/0.98  AC symbols                              0
% 3.68/0.98  
% 3.68/0.98  ------ Input Options Time Limit: Unbounded
% 3.68/0.98  
% 3.68/0.98  
% 3.68/0.98  
% 3.68/0.98  
% 3.68/0.98  ------ Preprocessing...
% 3.68/0.98  
% 3.68/0.98  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 3.68/0.98  Current options:
% 3.68/0.98  ------ 
% 3.68/0.98  
% 3.68/0.98  
% 3.68/0.98  
% 3.68/0.98  
% 3.68/0.98  ------ Proving...
% 3.68/0.98  
% 3.68/0.98  
% 3.68/0.98  ------ Preprocessing...
% 3.68/0.98  
% 3.68/0.98  ------ Preprocessing...
% 3.68/0.98  
% 3.68/0.98  ------ Preprocessing...
% 3.68/0.98  
% 3.68/0.98  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.68/0.98  
% 3.68/0.98  ------ Proving...
% 3.68/0.98  
% 3.68/0.98  
% 3.68/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.68/0.98  
% 3.68/0.98  ------ Proving...
% 3.68/0.98  
% 3.68/0.98  
% 3.68/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.68/0.98  
% 3.68/0.98  ------ Proving...
% 3.68/0.98  
% 3.68/0.98  
% 3.68/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.68/0.98  
% 3.68/0.98  ------ Proving...
% 3.68/0.98  
% 3.68/0.98  
% 3.68/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.68/0.98  
% 3.68/0.98  ------ Proving...
% 3.68/0.98  
% 3.68/0.98  
% 3.68/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.68/0.98  
% 3.68/0.98  ------ Proving...
% 3.68/0.98  
% 3.68/0.98  
% 3.68/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.68/0.98  
% 3.68/0.98  ------ Proving...
% 3.68/0.98  
% 3.68/0.98  
% 3.68/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.68/0.98  
% 3.68/0.98  ------ Proving...
% 3.68/0.98  
% 3.68/0.98  
% 3.68/0.98  % SZS status CounterSatisfiable for theBenchmark.p
% 3.68/0.98  
% 3.68/0.98  ------ Building Model...Done
% 3.68/0.98  
% 3.68/0.98  %------ The model is defined over ground terms (initial term algebra).
% 3.68/0.98  %------ Predicates are defined as (\forall x_1,..,x_n  ((~)P(x_1,..,x_n) <=> (\phi(x_1,..,x_n)))) 
% 3.68/0.98  %------ where \phi is a formula over the term algebra.
% 3.68/0.98  %------ If we have equality in the problem then it is also defined as a predicate above, 
% 3.68/0.98  %------ with "=" on the right-hand-side of the definition interpreted over the term algebra term_algebra_type
% 3.68/0.98  %------ See help for --sat_out_model for different model outputs.
% 3.68/0.98  %------ equality_sorted(X0,X1,X2) can be used in the place of usual "="
% 3.68/0.98  %------ where the first argument stands for the sort ($i in the unsorted case)
% 3.68/0.98  % SZS output start Model for theBenchmark.p
% 3.68/0.98  
% 3.68/0.98  %------ Positive definition of equality_sorted 
% 3.68/0.98  fof(lit_def,axiom,
% 3.68/0.98      (! [X0_0,X0_2,X1_2] : 
% 3.68/0.98        ( equality_sorted(X0_0,X0_2,X1_2) <=>
% 3.68/0.98             (
% 3.68/0.98                (
% 3.68/0.98                  ( X0_0=$o & X1_2=X0_2 )
% 3.68/0.98                )
% 3.68/0.98  
% 3.68/0.98               | 
% 3.68/0.98                (
% 3.68/0.98                  ( X0_0=$i )
% 3.68/0.98                 &
% 3.68/0.98                  ( X0!=sK7 )
% 3.68/0.98                 &
% 3.68/0.98                  ( X0!=sK6 )
% 3.68/0.98                 &
% 3.68/0.98                  ( X0!=u1_struct_0(sK6) )
% 3.68/0.98                 &
% 3.68/0.98                  ( X0!=k1_zfmisc_1(u1_struct_0(sK6)) )
% 3.68/0.98                 &
% 3.68/0.98                  ( X0!=arAF0_k2_xboole_0_0 )
% 3.68/0.98                 &
% 3.68/0.98                  ( X0!=arAF0_k2_struct_0_0 )
% 3.68/0.98                 &
% 3.68/0.98                  ( X0!=k1_zfmisc_1(arAF0_k2_xboole_0_0) )
% 3.68/0.98                 &
% 3.68/0.98                  ( X0!=k1_zfmisc_1(arAF0_k2_struct_0_0) )
% 3.68/0.98                 &
% 3.68/0.98                  ( X1!=sK7 )
% 3.68/0.98                 &
% 3.68/0.98                  ( X1!=sK6 )
% 3.68/0.98                 &
% 3.68/0.98                  ( X1!=u1_struct_0(sK6) )
% 3.68/0.98                 &
% 3.68/0.98                  ( X1!=k1_zfmisc_1(u1_struct_0(sK6)) )
% 3.68/0.98                 &
% 3.68/0.98                  ( X1!=arAF0_k2_xboole_0_0 )
% 3.68/0.98                 &
% 3.68/0.98                  ( X1!=arAF0_k2_struct_0_0 )
% 3.68/0.98                 &
% 3.68/0.98                  ( X1!=k1_zfmisc_1(arAF0_k2_xboole_0_0) )
% 3.68/0.98                 &
% 3.68/0.98                  ( X1!=k1_zfmisc_1(arAF0_k2_struct_0_0) )
% 3.68/0.98                )
% 3.68/0.98  
% 3.68/0.98               | 
% 3.68/0.98              ? [X2,X3] : 
% 3.68/0.98                (
% 3.68/0.98                  ( X0_0=$i & X0=u1_struct_0(X2) & X1=u1_struct_0(X3) )
% 3.68/0.98                 &
% 3.68/0.98                  ( X2!=sK6 )
% 3.68/0.98                 &
% 3.68/0.98                  ( X3!=sK6 )
% 3.68/0.98                )
% 3.68/0.98  
% 3.68/0.98               | 
% 3.68/0.98                (
% 3.68/0.98                  ( X0_0=$i & X0=u1_struct_0(sK6) & X1=u1_struct_0(sK6) )
% 3.68/0.98                )
% 3.68/0.98  
% 3.68/0.98               | 
% 3.68/0.98                (
% 3.68/0.98                  ( X0_0=$i & X0=u1_struct_0(sK6) & X1=arAF0_k2_xboole_0_0 )
% 3.68/0.98                )
% 3.68/0.98  
% 3.68/0.98               | 
% 3.68/0.98                (
% 3.68/0.98                  ( X0_0=$i & X0=u1_struct_0(sK6) & X1=arAF0_k2_struct_0_0 )
% 3.68/0.98                )
% 3.68/0.98  
% 3.68/0.98               | 
% 3.68/0.98                (
% 3.68/0.98                  ( X0_0=$i & X0=k1_zfmisc_1(u1_struct_0(sK6)) & X1=k1_zfmisc_1(u1_struct_0(sK6)) )
% 3.68/0.98                )
% 3.68/0.98  
% 3.68/0.98               | 
% 3.68/0.98                (
% 3.68/0.98                  ( X0_0=$i & X0=k1_zfmisc_1(u1_struct_0(sK6)) & X1=k1_zfmisc_1(arAF0_k2_xboole_0_0) )
% 3.68/0.98                )
% 3.68/0.98  
% 3.68/0.98               | 
% 3.68/0.98                (
% 3.68/0.98                  ( X0_0=$i & X0=k1_zfmisc_1(u1_struct_0(sK6)) & X1=k1_zfmisc_1(arAF0_k2_struct_0_0) )
% 3.68/0.98                )
% 3.68/0.98  
% 3.68/0.98               | 
% 3.68/0.98                (
% 3.68/0.98                  ( X0_0=$i & X0=arAF0_k2_xboole_0_0 & X1=u1_struct_0(sK6) )
% 3.68/0.98                )
% 3.68/0.98  
% 3.68/0.98               | 
% 3.68/0.98                (
% 3.68/0.98                  ( X0_0=$i & X0=arAF0_k2_xboole_0_0 & X1=arAF0_k2_struct_0_0 )
% 3.68/0.98                )
% 3.68/0.98  
% 3.68/0.98               | 
% 3.68/0.98                (
% 3.68/0.98                  ( X0_0=$i & X0=arAF0_k2_struct_0_0 & X1=u1_struct_0(sK6) )
% 3.68/0.98                )
% 3.68/0.98  
% 3.68/0.98               | 
% 3.68/0.98                (
% 3.68/0.98                  ( X0_0=$i & X0=arAF0_k2_struct_0_0 & X1=arAF0_k2_xboole_0_0 )
% 3.68/0.98                )
% 3.68/0.98  
% 3.68/0.98               | 
% 3.68/0.98                (
% 3.68/0.98                  ( X0_0=$i & X0=k1_zfmisc_1(arAF0_k2_xboole_0_0) & X1=k1_zfmisc_1(u1_struct_0(sK6)) )
% 3.68/0.98                )
% 3.68/0.98  
% 3.68/0.98               | 
% 3.68/0.98                (
% 3.68/0.98                  ( X0_0=$i & X0=k1_zfmisc_1(arAF0_k2_xboole_0_0) & X1=k1_zfmisc_1(arAF0_k2_xboole_0_0) )
% 3.68/0.98                )
% 3.68/0.98  
% 3.68/0.98               | 
% 3.68/0.98                (
% 3.68/0.98                  ( X0_0=$i & X0=k1_zfmisc_1(arAF0_k2_xboole_0_0) & X1=k1_zfmisc_1(arAF0_k2_struct_0_0) )
% 3.68/0.98                )
% 3.68/0.98  
% 3.68/0.98               | 
% 3.68/0.98              ? [X2,X3] : 
% 3.68/0.98                (
% 3.68/0.98                  ( X0_0=$i & X0=k1_zfmisc_1(X2) & X1=k1_zfmisc_1(X3) )
% 3.68/0.98                 &
% 3.68/0.98                  ( X2!=u1_struct_0(sK5) | X3!=u1_struct_0(sK6) )
% 3.68/0.98                 &
% 3.68/0.98                  ( X2!=u1_struct_0(sK6) )
% 3.68/0.98                 &
% 3.68/0.98                  ( X2!=arAF0_k2_xboole_0_0 )
% 3.68/0.98                 &
% 3.68/0.98                  ( X2!=arAF0_k2_struct_0_0 )
% 3.68/0.98                 &
% 3.68/0.98                  ( X3!=u1_struct_0(sK6) )
% 3.68/0.98                 &
% 3.68/0.98                  ( X3!=arAF0_k2_xboole_0_0 )
% 3.68/0.98                 &
% 3.68/0.98                  ( X3!=arAF0_k2_struct_0_0 )
% 3.68/0.98                )
% 3.68/0.98  
% 3.68/0.98               | 
% 3.68/0.98                (
% 3.68/0.98                  ( X0_0=$i & X0=k1_zfmisc_1(arAF0_k2_struct_0_0) & X1=k1_zfmisc_1(u1_struct_0(sK6)) )
% 3.68/0.98                )
% 3.68/0.98  
% 3.68/0.98               | 
% 3.68/0.98                (
% 3.68/0.98                  ( X0_0=$i & X0=k1_zfmisc_1(arAF0_k2_struct_0_0) & X1=k1_zfmisc_1(arAF0_k2_xboole_0_0) )
% 3.68/0.98                )
% 3.68/0.98  
% 3.68/0.98               | 
% 3.68/0.98                (
% 3.68/0.98                  ( X0_0=$i & X0=k1_zfmisc_1(arAF0_k2_struct_0_0) & X1=k1_zfmisc_1(arAF0_k2_struct_0_0) )
% 3.68/0.98                )
% 3.68/0.98  
% 3.68/0.98               | 
% 3.68/0.98                (
% 3.68/0.98                  ( X0_0=$i & X1=X0 )
% 3.68/0.98                )
% 3.68/0.98  
% 3.68/0.98             )
% 3.68/0.98        )
% 3.68/0.98      )
% 3.68/0.98     ).
% 3.68/0.98  
% 3.68/0.98  %------ Positive definition of r1_tarski 
% 3.68/0.98  fof(lit_def,axiom,
% 3.68/0.98      (! [X0,X1] : 
% 3.68/0.98        ( r1_tarski(X0,X1) <=>
% 3.68/0.98             (
% 3.68/0.98                (
% 3.68/0.98                  ( X0=sK7 & X1=u1_struct_0(sK6) )
% 3.68/0.98                )
% 3.68/0.98  
% 3.68/0.98               | 
% 3.68/0.98                (
% 3.68/0.98                  ( X0=sK7 & X1=arAF0_k2_xboole_0_0 )
% 3.68/0.98                )
% 3.68/0.98  
% 3.68/0.98               | 
% 3.68/0.98                (
% 3.68/0.98                  ( X0=sK7 & X1=arAF0_k2_struct_0_0 )
% 3.68/0.98                )
% 3.68/0.98  
% 3.68/0.98               | 
% 3.68/0.98                (
% 3.68/0.98                  ( X0=u1_struct_0(sK6) & X1=u1_struct_0(sK6) )
% 3.68/0.98                )
% 3.68/0.98  
% 3.68/0.98               | 
% 3.68/0.98                (
% 3.68/0.98                  ( X0=u1_struct_0(sK6) & X1=arAF0_k2_xboole_0_0 )
% 3.68/0.98                )
% 3.68/0.98  
% 3.68/0.98               | 
% 3.68/0.98                (
% 3.68/0.98                  ( X0=u1_struct_0(sK6) & X1=arAF0_k2_struct_0_0 )
% 3.68/0.98                )
% 3.68/0.98  
% 3.68/0.98               | 
% 3.68/0.98                (
% 3.68/0.98                  ( X0=arAF0_k2_xboole_0_0 & X1=u1_struct_0(sK6) )
% 3.68/0.98                )
% 3.68/0.98  
% 3.68/0.98               | 
% 3.68/0.98                (
% 3.68/0.98                  ( X0=arAF0_k2_xboole_0_0 & X1=arAF0_k2_xboole_0_0 )
% 3.68/0.98                )
% 3.68/0.98  
% 3.68/0.98               | 
% 3.68/0.98                (
% 3.68/0.98                  ( X0=arAF0_k2_xboole_0_0 & X1=arAF0_k2_struct_0_0 )
% 3.68/0.98                )
% 3.68/0.98  
% 3.68/0.98               | 
% 3.68/0.98                (
% 3.68/0.98                  ( X0=arAF0_k2_struct_0_0 & X1=u1_struct_0(sK6) )
% 3.68/0.98                )
% 3.68/0.98  
% 3.68/0.98               | 
% 3.68/0.98                (
% 3.68/0.98                  ( X0=arAF0_k2_struct_0_0 & X1=arAF0_k2_xboole_0_0 )
% 3.68/0.98                )
% 3.68/0.98  
% 3.68/0.98               | 
% 3.68/0.98                (
% 3.68/0.98                  ( X0=arAF0_k2_struct_0_0 & X1=arAF0_k2_struct_0_0 )
% 3.68/0.98                )
% 3.68/0.98  
% 3.68/0.98             )
% 3.68/0.98        )
% 3.68/0.98      )
% 3.68/0.98     ).
% 3.68/0.98  
% 3.68/0.98  %------ Positive definition of m1_subset_1 
% 3.68/0.98  fof(lit_def,axiom,
% 3.68/0.98      (! [X0,X1] : 
% 3.68/0.98        ( m1_subset_1(X0,X1) <=>
% 3.68/0.98             (
% 3.68/0.98                (
% 3.68/0.98                  ( X0=sK7 & X1=k1_zfmisc_1(u1_struct_0(sK6)) )
% 3.68/0.98                )
% 3.68/0.98  
% 3.68/0.98               | 
% 3.68/0.98                (
% 3.68/0.98                  ( X0=sK7 & X1=k1_zfmisc_1(arAF0_k2_xboole_0_0) )
% 3.68/0.98                )
% 3.68/0.98  
% 3.68/0.98               | 
% 3.68/0.98                (
% 3.68/0.98                  ( X0=sK7 & X1=k1_zfmisc_1(arAF0_k2_struct_0_0) )
% 3.68/0.98                )
% 3.68/0.98  
% 3.68/0.98               | 
% 3.68/0.98                (
% 3.68/0.98                  ( X0=u1_struct_0(sK6) & X1=k1_zfmisc_1(u1_struct_0(sK6)) )
% 3.68/0.98                )
% 3.68/0.98  
% 3.68/0.98               | 
% 3.68/0.98                (
% 3.68/0.98                  ( X0=u1_struct_0(sK6) & X1=k1_zfmisc_1(arAF0_k2_xboole_0_0) )
% 3.68/0.98                )
% 3.68/0.98  
% 3.68/0.98               | 
% 3.68/0.98                (
% 3.68/0.98                  ( X0=u1_struct_0(sK6) & X1=k1_zfmisc_1(arAF0_k2_struct_0_0) )
% 3.68/0.98                )
% 3.68/0.98  
% 3.68/0.98               | 
% 3.68/0.98                (
% 3.68/0.98                  ( X0=arAF0_k2_xboole_0_0 & X1=k1_zfmisc_1(u1_struct_0(sK6)) )
% 3.68/0.98                )
% 3.68/0.98  
% 3.68/0.98               | 
% 3.68/0.98                (
% 3.68/0.98                  ( X0=arAF0_k2_xboole_0_0 & X1=k1_zfmisc_1(arAF0_k2_xboole_0_0) )
% 3.68/0.98                )
% 3.68/0.98  
% 3.68/0.98               | 
% 3.68/0.98                (
% 3.68/0.98                  ( X0=arAF0_k2_xboole_0_0 & X1=k1_zfmisc_1(arAF0_k2_struct_0_0) )
% 3.68/0.98                )
% 3.68/0.98  
% 3.68/0.98               | 
% 3.68/0.98                (
% 3.68/0.98                  ( X0=arAF0_k2_struct_0_0 & X1=k1_zfmisc_1(u1_struct_0(sK6)) )
% 3.68/0.98                )
% 3.68/0.98  
% 3.68/0.98               | 
% 3.68/0.98                (
% 3.68/0.98                  ( X0=arAF0_k2_struct_0_0 & X1=k1_zfmisc_1(arAF0_k2_xboole_0_0) )
% 3.68/0.98                )
% 3.68/0.98  
% 3.68/0.98               | 
% 3.68/0.98                (
% 3.68/0.98                  ( X0=arAF0_k2_struct_0_0 & X1=k1_zfmisc_1(arAF0_k2_struct_0_0) )
% 3.68/0.98                )
% 3.68/0.98  
% 3.68/0.98             )
% 3.68/0.98        )
% 3.68/0.98      )
% 3.68/0.98     ).
% 3.68/0.98  
% 3.68/0.98  %------ Positive definition of l1_pre_topc 
% 3.68/0.98  fof(lit_def,axiom,
% 3.68/0.98      (! [X0] : 
% 3.68/0.98        ( l1_pre_topc(X0) <=>
% 3.68/0.98            $true
% 3.68/0.98        )
% 3.68/0.98      )
% 3.68/0.98     ).
% 3.68/0.98  
% 3.68/0.98  %------ Positive definition of arAF0_r2_hidden_0 
% 3.68/0.98  fof(lit_def,axiom,
% 3.68/0.98        ( arAF0_r2_hidden_0 <=>
% 3.68/0.98            $false
% 3.68/0.98        )
% 3.68/0.98     ).
% 3.68/0.98  
% 3.68/0.98  %------ Positive definition of arAF0_sP1_0_1 
% 3.68/0.98  fof(lit_def,axiom,
% 3.68/0.98      (! [X0] : 
% 3.68/0.98        ( arAF0_sP1_0_1(X0) <=>
% 3.68/0.98            $true
% 3.68/0.98        )
% 3.68/0.98      )
% 3.68/0.98     ).
% 3.68/0.98  
% 3.68/0.98  %------ Positive definition of arAF0_sP0_0_1 
% 3.68/0.98  fof(lit_def,axiom,
% 3.68/0.98      (! [X0] : 
% 3.68/0.98        ( arAF0_sP0_0_1(X0) <=>
% 3.68/0.98            $true
% 3.68/0.98        )
% 3.68/0.98      )
% 3.68/0.98     ).
% 3.68/0.98  
% 3.68/0.98  %------ Positive definition of arAF0_m1_pre_topc_0_1 
% 3.68/0.98  fof(lit_def,axiom,
% 3.68/0.98      (! [X0] : 
% 3.68/0.98        ( arAF0_m1_pre_topc_0_1(X0) <=>
% 3.68/0.98            $true
% 3.68/0.98        )
% 3.68/0.98      )
% 3.68/0.98     ).
% 3.68/0.98  % SZS output end Model for theBenchmark.p
% 3.68/0.98  ------                               Statistics
% 3.68/0.98  
% 3.68/0.98  ------ Selected
% 3.68/0.98  
% 3.68/0.98  total_time:                             0.283
% 3.68/0.98  
%------------------------------------------------------------------------------
