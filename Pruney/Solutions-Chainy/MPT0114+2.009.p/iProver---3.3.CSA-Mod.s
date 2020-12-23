%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:25:59 EST 2020

% Result     : CounterSatisfiable 3.48s
% Output     : Model 3.48s
% Verified   : 
% Statistics : Number of formulae       :    3 (   3 expanded)
%              Number of leaves         :    3 (   3 expanded)
%              Depth                    :    0
%              Number of atoms          :   39 (  39 expanded)
%              Number of equality atoms :   36 (  36 expanded)
%              Maximal formula depth    :   16 (  12 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%------ Positive definition of equality_sorted 
fof(lit_def,axiom,(
    ! [X0_0,X0_2,X1_2] :
      ( equality_sorted(X0_0,X0_2,X1_2)
    <=> ( ( X0_0 = $o
          & X1_2 = X0_2 )
        | ( X0_0 = $i
          & X0 != sK0
          & X0 != arAF0_k2_xboole_0_0
          & X0 != arAF0_k4_xboole_0_0
          & X0 != arAF0_k3_xboole_0_0_1(X0)
          & X1 != sK0
          & X1 != arAF0_k2_xboole_0_0
          & X1 != arAF0_k4_xboole_0_0
          & X1 != arAF0_k3_xboole_0_0_1(X1) )
        | ? [X2,X3] :
            ( X0_0 = $i
            & X0 = arAF0_k3_xboole_0_0_1(X2)
            & X1 = arAF0_k3_xboole_0_0_1(X3) )
        | ( X0_0 = $i
          & X1 = X0 ) ) ) )).

%------ Positive definition of r1_xboole_0 
fof(lit_def_001,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> ( ? [X2] :
            ( X0 = arAF0_k4_xboole_0_0
            & X1 = arAF0_k3_xboole_0_0_1(X2) )
        | ? [X2] :
            ( X0 = arAF0_k3_xboole_0_0_1(X2)
            & X1 = arAF0_k4_xboole_0_0 ) ) ) )).

%------ Positive definition of r1_tarski 
fof(lit_def_002,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ( ( X0 = sK0
          & X1 = arAF0_k2_xboole_0_0 )
        | ( X0 = sK0
          & X1 = arAF0_k4_xboole_0_0 )
        | ( X0 = arAF0_k4_xboole_0_0
          & X1 = arAF0_k2_xboole_0_0 )
        | ( X0 = arAF0_k4_xboole_0_0
          & X1 = arAF0_k4_xboole_0_0 )
        | ? [X2] :
            ( X0 = arAF0_k3_xboole_0_0_1(X2)
            & X1 = arAF0_k2_xboole_0_0 )
        | ? [X2] :
            ( X0 = arAF0_k3_xboole_0_0_1(X2)
            & X1 = arAF0_k4_xboole_0_0 )
        | ( X1 = arAF0_k2_xboole_0_0
          & X0 != arAF0_k2_xboole_0_0
          & X0 != arAF0_k4_xboole_0_0
          & X0 != arAF0_k3_xboole_0_0_1(X0) ) ) ) )).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:52:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.48/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.48/0.99  
% 3.48/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.48/0.99  
% 3.48/0.99  ------  iProver source info
% 3.48/0.99  
% 3.48/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.48/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.48/0.99  git: non_committed_changes: false
% 3.48/0.99  git: last_make_outside_of_git: false
% 3.48/0.99  
% 3.48/0.99  ------ 
% 3.48/0.99  ------ Parsing...
% 3.48/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.48/0.99  
% 3.48/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.48/0.99  
% 3.48/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.48/0.99  
% 3.48/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.48/0.99  ------ Proving...
% 3.48/0.99  ------ Problem Properties 
% 3.48/0.99  
% 3.48/0.99  
% 3.48/0.99  clauses                                 10
% 3.48/0.99  conjectures                             3
% 3.48/0.99  EPR                                     3
% 3.48/0.99  Horn                                    8
% 3.48/0.99  unary                                   3
% 3.48/0.99  binary                                  3
% 3.48/0.99  lits                                    22
% 3.48/0.99  lits eq                                 1
% 3.48/0.99  fd_pure                                 0
% 3.48/0.99  fd_pseudo                               0
% 3.48/0.99  fd_cond                                 0
% 3.48/0.99  fd_pseudo_cond                          0
% 3.48/0.99  AC symbols                              0
% 3.48/0.99  
% 3.48/0.99  ------ Input Options Time Limit: Unbounded
% 3.48/0.99  
% 3.48/0.99  
% 3.48/0.99  
% 3.48/0.99  
% 3.48/0.99  ------ Preprocessing...
% 3.48/0.99  
% 3.48/0.99  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 3.48/0.99  Current options:
% 3.48/0.99  ------ 
% 3.48/0.99  
% 3.48/0.99  
% 3.48/0.99  
% 3.48/0.99  
% 3.48/0.99  ------ Proving...
% 3.48/0.99  
% 3.48/0.99  
% 3.48/0.99  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.48/0.99  
% 3.48/0.99  ------ Proving...
% 3.48/0.99  
% 3.48/0.99  
% 3.48/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.48/0.99  
% 3.48/0.99  ------ Proving...
% 3.48/0.99  
% 3.48/0.99  
% 3.48/0.99  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.48/0.99  
% 3.48/0.99  ------ Proving...
% 3.48/0.99  
% 3.48/0.99  
% 3.48/0.99  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.48/0.99  
% 3.48/0.99  ------ Proving...
% 3.48/0.99  
% 3.48/0.99  
% 3.48/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.48/0.99  
% 3.48/0.99  ------ Proving...
% 3.48/0.99  
% 3.48/0.99  
% 3.48/0.99  % SZS status CounterSatisfiable for theBenchmark.p
% 3.48/0.99  
% 3.48/0.99  ------ Building Model...Done
% 3.48/0.99  
% 3.48/0.99  %------ The model is defined over ground terms (initial term algebra).
% 3.48/0.99  %------ Predicates are defined as (\forall x_1,..,x_n  ((~)P(x_1,..,x_n) <=> (\phi(x_1,..,x_n)))) 
% 3.48/0.99  %------ where \phi is a formula over the term algebra.
% 3.48/0.99  %------ If we have equality in the problem then it is also defined as a predicate above, 
% 3.48/0.99  %------ with "=" on the right-hand-side of the definition interpreted over the term algebra term_algebra_type
% 3.48/0.99  %------ See help for --sat_out_model for different model outputs.
% 3.48/0.99  %------ equality_sorted(X0,X1,X2) can be used in the place of usual "="
% 3.48/0.99  %------ where the first argument stands for the sort ($i in the unsorted case)
% 3.48/0.99  % SZS output start Model for theBenchmark.p
% 3.48/0.99  
% 3.48/0.99  %------ Positive definition of equality_sorted 
% 3.48/0.99  fof(lit_def,axiom,
% 3.48/0.99      (! [X0_0,X0_2,X1_2] : 
% 3.48/0.99        ( equality_sorted(X0_0,X0_2,X1_2) <=>
% 3.48/0.99             (
% 3.48/0.99                (
% 3.48/0.99                  ( X0_0=$o & X1_2=X0_2 )
% 3.48/0.99                )
% 3.48/0.99  
% 3.48/0.99               | 
% 3.48/0.99                (
% 3.48/0.99                  ( X0_0=$i )
% 3.48/0.99                 &
% 3.48/0.99                  ( X0!=sK0 )
% 3.48/0.99                 &
% 3.48/0.99                  ( X0!=arAF0_k2_xboole_0_0 )
% 3.48/0.99                 &
% 3.48/0.99                  ( X0!=arAF0_k4_xboole_0_0 )
% 3.48/0.99                 &
% 3.48/0.99                  ( X0!=arAF0_k3_xboole_0_0_1(X0) )
% 3.48/0.99                 &
% 3.48/0.99                  ( X1!=sK0 )
% 3.48/0.99                 &
% 3.48/0.99                  ( X1!=arAF0_k2_xboole_0_0 )
% 3.48/0.99                 &
% 3.48/0.99                  ( X1!=arAF0_k4_xboole_0_0 )
% 3.48/0.99                 &
% 3.48/0.99                  ( X1!=arAF0_k3_xboole_0_0_1(X1) )
% 3.48/0.99                )
% 3.48/0.99  
% 3.48/0.99               | 
% 3.48/0.99              ? [X2,X3] : 
% 3.48/0.99                (
% 3.48/0.99                  ( X0_0=$i & X0=arAF0_k3_xboole_0_0_1(X2) & X1=arAF0_k3_xboole_0_0_1(X3) )
% 3.48/0.99                )
% 3.48/0.99  
% 3.48/0.99               | 
% 3.48/0.99                (
% 3.48/0.99                  ( X0_0=$i & X1=X0 )
% 3.48/0.99                )
% 3.48/0.99  
% 3.48/0.99             )
% 3.48/0.99        )
% 3.48/0.99      )
% 3.48/0.99     ).
% 3.48/0.99  
% 3.48/0.99  %------ Positive definition of r1_xboole_0 
% 3.48/0.99  fof(lit_def,axiom,
% 3.48/0.99      (! [X0,X1] : 
% 3.48/0.99        ( r1_xboole_0(X0,X1) <=>
% 3.48/0.99             (
% 3.48/0.99              ? [X2] : 
% 3.48/0.99                (
% 3.48/0.99                  ( X0=arAF0_k4_xboole_0_0 & X1=arAF0_k3_xboole_0_0_1(X2) )
% 3.48/0.99                )
% 3.48/0.99  
% 3.48/0.99               | 
% 3.48/0.99              ? [X2] : 
% 3.48/0.99                (
% 3.48/0.99                  ( X0=arAF0_k3_xboole_0_0_1(X2) & X1=arAF0_k4_xboole_0_0 )
% 3.48/0.99                )
% 3.48/0.99  
% 3.48/0.99             )
% 3.48/0.99        )
% 3.48/0.99      )
% 3.48/0.99     ).
% 3.48/0.99  
% 3.48/0.99  %------ Positive definition of r1_tarski 
% 3.48/0.99  fof(lit_def,axiom,
% 3.48/0.99      (! [X0,X1] : 
% 3.48/0.99        ( r1_tarski(X0,X1) <=>
% 3.48/0.99             (
% 3.48/0.99                (
% 3.48/0.99                  ( X0=sK0 & X1=arAF0_k2_xboole_0_0 )
% 3.48/0.99                )
% 3.48/0.99  
% 3.48/0.99               | 
% 3.48/0.99                (
% 3.48/0.99                  ( X0=sK0 & X1=arAF0_k4_xboole_0_0 )
% 3.48/0.99                )
% 3.48/0.99  
% 3.48/0.99               | 
% 3.48/0.99                (
% 3.48/0.99                  ( X0=arAF0_k4_xboole_0_0 & X1=arAF0_k2_xboole_0_0 )
% 3.48/0.99                )
% 3.48/0.99  
% 3.48/0.99               | 
% 3.48/0.99                (
% 3.48/0.99                  ( X0=arAF0_k4_xboole_0_0 & X1=arAF0_k4_xboole_0_0 )
% 3.48/0.99                )
% 3.48/0.99  
% 3.48/0.99               | 
% 3.48/0.99              ? [X2] : 
% 3.48/0.99                (
% 3.48/0.99                  ( X0=arAF0_k3_xboole_0_0_1(X2) & X1=arAF0_k2_xboole_0_0 )
% 3.48/0.99                )
% 3.48/0.99  
% 3.48/0.99               | 
% 3.48/0.99              ? [X2] : 
% 3.48/0.99                (
% 3.48/0.99                  ( X0=arAF0_k3_xboole_0_0_1(X2) & X1=arAF0_k4_xboole_0_0 )
% 3.48/0.99                )
% 3.48/0.99  
% 3.48/0.99               | 
% 3.48/0.99                (
% 3.48/0.99                  ( X1=arAF0_k2_xboole_0_0 )
% 3.48/0.99                 &
% 3.48/0.99                  ( X0!=arAF0_k2_xboole_0_0 )
% 3.48/0.99                 &
% 3.48/0.99                  ( X0!=arAF0_k4_xboole_0_0 )
% 3.48/0.99                 &
% 3.48/0.99                  ( X0!=arAF0_k3_xboole_0_0_1(X0) )
% 3.48/0.99                )
% 3.48/0.99  
% 3.48/0.99             )
% 3.48/0.99        )
% 3.48/0.99      )
% 3.48/0.99     ).
% 3.48/0.99  % SZS output end Model for theBenchmark.p
% 3.48/0.99  ------                               Statistics
% 3.48/0.99  
% 3.48/0.99  ------ Selected
% 3.48/0.99  
% 3.48/0.99  total_time:                             0.091
% 3.48/0.99  
%------------------------------------------------------------------------------
