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
% DateTime   : Thu Dec  3 11:23:56 EST 2020

% Result     : CounterSatisfiable 7.62s
% Output     : Model 7.62s
% Verified   : 
% Statistics : Number of formulae       :    3 (   3 expanded)
%              Number of leaves         :    3 (   3 expanded)
%              Depth                    :    0
%              Number of atoms          :   45 (  45 expanded)
%              Number of equality atoms :   42 (  42 expanded)
%              Maximal formula depth    :   20 (  10 average)
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
          & ( X0 != k1_xboole_0
            | X1 != k4_xboole_0(sK0,sK1) )
          & X0 != sK0
          & X0 != sK1
          & X0 != sK2
          & X0 != k4_xboole_0(sK0,sK1)
          & ( X0 != k4_xboole_0(sK0,sK1)
            | X1 != k1_xboole_0 )
          & X1 != sK0
          & X1 != sK1
          & X1 != sK2
          & X1 != k4_xboole_0(sK0,sK1) )
        | ( X0_0 = $i
          & X0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))
          & X1 = k1_xboole_0 )
        | ? [X2,X3] :
            ( X0_0 = $i
            & X0 = k4_xboole_0(X2,X3)
            & X1 = k1_xboole_0
            & ( X2 != sK0
              | X3 != sK1 ) )
        | ? [X2,X3,X4,X5] :
            ( X0_0 = $i
            & X0 = k4_xboole_0(X2,X3)
            & X1 = k4_xboole_0(X4,X5)
            & ( X2 != sK0
              | X3 != sK1 )
            & ( X4 != sK0
              | X5 != sK1 ) )
        | ? [X2,X3,X4] :
            ( X0_0 = $i
            & X0 = k4_xboole_0(k4_xboole_0(X2,X3),X4)
            & X1 = k4_xboole_0(X2,arAF0_k2_xboole_0_0) )
        | ( X0_0 = $i
          & X0 = k4_xboole_0(sK0,sK1)
          & X1 = k4_xboole_0(sK0,sK1) )
        | ( X0_0 = $i
          & X1 = X0 ) ) ) )).

%------ Positive definition of r1_xboole_0 
fof(lit_def_001,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> ( X0 = sK0
        & X1 = sK2 ) ) )).

%------ Negative definition of r1_tarski 
fof(lit_def_002,axiom,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
    <=> ( X0 = sK0
        & X1 = sK1 ) ) )).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:16:02 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.62/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.62/1.49  
% 7.62/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.62/1.49  
% 7.62/1.49  ------  iProver source info
% 7.62/1.49  
% 7.62/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.62/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.62/1.49  git: non_committed_changes: false
% 7.62/1.49  git: last_make_outside_of_git: false
% 7.62/1.49  
% 7.62/1.49  ------ 
% 7.62/1.49  ------ Parsing...
% 7.62/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.62/1.49  
% 7.62/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 7.62/1.49  
% 7.62/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.62/1.49  
% 7.62/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.62/1.49  ------ Proving...
% 7.62/1.49  ------ Problem Properties 
% 7.62/1.49  
% 7.62/1.49  
% 7.62/1.49  clauses                                 9
% 7.62/1.49  conjectures                             3
% 7.62/1.49  EPR                                     2
% 7.62/1.49  Horn                                    9
% 7.62/1.49  unary                                   6
% 7.62/1.49  binary                                  3
% 7.62/1.49  lits                                    12
% 7.62/1.49  lits eq                                 5
% 7.62/1.49  fd_pure                                 0
% 7.62/1.49  fd_pseudo                               0
% 7.62/1.49  fd_cond                                 0
% 7.62/1.49  fd_pseudo_cond                          0
% 7.62/1.49  AC symbols                              0
% 7.62/1.49  
% 7.62/1.49  ------ Input Options Time Limit: Unbounded
% 7.62/1.49  
% 7.62/1.49  
% 7.62/1.49  
% 7.62/1.49  
% 7.62/1.49  ------ Preprocessing...
% 7.62/1.49  
% 7.62/1.49  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 7.62/1.49  Current options:
% 7.62/1.49  ------ 
% 7.62/1.49  
% 7.62/1.49  
% 7.62/1.49  
% 7.62/1.49  
% 7.62/1.49  ------ Proving...
% 7.62/1.49  
% 7.62/1.49  
% 7.62/1.49  ------ Preprocessing...
% 7.62/1.49  
% 7.62/1.49  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.62/1.49  
% 7.62/1.49  ------ Proving...
% 7.62/1.49  
% 7.62/1.49  
% 7.62/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.62/1.49  
% 7.62/1.49  ------ Proving...
% 7.62/1.49  
% 7.62/1.49  
% 7.62/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.62/1.49  
% 7.62/1.49  ------ Proving...
% 7.62/1.49  
% 7.62/1.49  
% 7.62/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.62/1.49  
% 7.62/1.49  ------ Proving...
% 7.62/1.49  
% 7.62/1.49  
% 7.62/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.62/1.49  
% 7.62/1.49  ------ Proving...
% 7.62/1.49  
% 7.62/1.49  
% 7.62/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.62/1.49  
% 7.62/1.49  ------ Proving...
% 7.62/1.49  
% 7.62/1.49  
% 7.62/1.49  % SZS status CounterSatisfiable for theBenchmark.p
% 7.62/1.49  
% 7.62/1.49  ------ Building Model...Done
% 7.62/1.49  
% 7.62/1.49  %------ The model is defined over ground terms (initial term algebra).
% 7.62/1.49  %------ Predicates are defined as (\forall x_1,..,x_n  ((~)P(x_1,..,x_n) <=> (\phi(x_1,..,x_n)))) 
% 7.62/1.49  %------ where \phi is a formula over the term algebra.
% 7.62/1.49  %------ If we have equality in the problem then it is also defined as a predicate above, 
% 7.62/1.49  %------ with "=" on the right-hand-side of the definition interpreted over the term algebra term_algebra_type
% 7.62/1.49  %------ See help for --sat_out_model for different model outputs.
% 7.62/1.49  %------ equality_sorted(X0,X1,X2) can be used in the place of usual "="
% 7.62/1.49  %------ where the first argument stands for the sort ($i in the unsorted case)
% 7.62/1.49  % SZS output start Model for theBenchmark.p
% 7.62/1.49  
% 7.62/1.49  %------ Positive definition of equality_sorted 
% 7.62/1.49  fof(lit_def,axiom,
% 7.62/1.49      (! [X0_0,X0_2,X1_2] : 
% 7.62/1.49        ( equality_sorted(X0_0,X0_2,X1_2) <=>
% 7.62/1.49             (
% 7.62/1.49                (
% 7.62/1.49                  ( X0_0=$o & X1_2=X0_2 )
% 7.62/1.49                )
% 7.62/1.49  
% 7.62/1.49               | 
% 7.62/1.49                (
% 7.62/1.49                  ( X0_0=$i )
% 7.62/1.49                 &
% 7.62/1.49                  ( X0!=k1_xboole_0 | X1!=k4_xboole_0(sK0,sK1) )
% 7.62/1.49                 &
% 7.62/1.49                  ( X0!=sK0 )
% 7.62/1.49                 &
% 7.62/1.49                  ( X0!=sK1 )
% 7.62/1.49                 &
% 7.62/1.49                  ( X0!=sK2 )
% 7.62/1.49                 &
% 7.62/1.49                  ( X0!=k4_xboole_0(sK0,sK1) )
% 7.62/1.49                 &
% 7.62/1.49                  ( X0!=k4_xboole_0(sK0,sK1) | X1!=k1_xboole_0 )
% 7.62/1.49                 &
% 7.62/1.49                  ( X1!=sK0 )
% 7.62/1.49                 &
% 7.62/1.49                  ( X1!=sK1 )
% 7.62/1.49                 &
% 7.62/1.49                  ( X1!=sK2 )
% 7.62/1.49                 &
% 7.62/1.49                  ( X1!=k4_xboole_0(sK0,sK1) )
% 7.62/1.49                )
% 7.62/1.49  
% 7.62/1.49               | 
% 7.62/1.49                (
% 7.62/1.49                  ( X0_0=$i & X0=k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) & X1=k1_xboole_0 )
% 7.62/1.49                )
% 7.62/1.49  
% 7.62/1.49               | 
% 7.62/1.49              ? [X2,X3] : 
% 7.62/1.49                (
% 7.62/1.49                  ( X0_0=$i & X0=k4_xboole_0(X2,X3) & X1=k1_xboole_0 )
% 7.62/1.49                 &
% 7.62/1.49                  ( X2!=sK0 | X3!=sK1 )
% 7.62/1.49                )
% 7.62/1.49  
% 7.62/1.49               | 
% 7.62/1.49              ? [X2,X3,X4,X5] : 
% 7.62/1.49                (
% 7.62/1.49                  ( X0_0=$i & X0=k4_xboole_0(X2,X3) & X1=k4_xboole_0(X4,X5) )
% 7.62/1.49                 &
% 7.62/1.49                  ( X2!=sK0 | X3!=sK1 )
% 7.62/1.49                 &
% 7.62/1.49                  ( X4!=sK0 | X5!=sK1 )
% 7.62/1.49                )
% 7.62/1.49  
% 7.62/1.49               | 
% 7.62/1.49              ? [X2,X3,X4] : 
% 7.62/1.49                (
% 7.62/1.49                  ( X0_0=$i & X0=k4_xboole_0(k4_xboole_0(X2,X3),X4) & X1=k4_xboole_0(X2,arAF0_k2_xboole_0_0) )
% 7.62/1.49                )
% 7.62/1.49  
% 7.62/1.49               | 
% 7.62/1.49                (
% 7.62/1.49                  ( X0_0=$i & X0=k4_xboole_0(sK0,sK1) & X1=k4_xboole_0(sK0,sK1) )
% 7.62/1.49                )
% 7.62/1.49  
% 7.62/1.49               | 
% 7.62/1.49                (
% 7.62/1.49                  ( X0_0=$i & X1=X0 )
% 7.62/1.49                )
% 7.62/1.49  
% 7.62/1.49             )
% 7.62/1.49        )
% 7.62/1.49      )
% 7.62/1.49     ).
% 7.62/1.49  
% 7.62/1.49  %------ Positive definition of r1_xboole_0 
% 7.62/1.49  fof(lit_def,axiom,
% 7.62/1.49      (! [X0,X1] : 
% 7.62/1.49        ( r1_xboole_0(X0,X1) <=>
% 7.62/1.49             (
% 7.62/1.49                (
% 7.62/1.49                  ( X0=sK0 & X1=sK2 )
% 7.62/1.49                )
% 7.62/1.49  
% 7.62/1.49             )
% 7.62/1.49        )
% 7.62/1.49      )
% 7.62/1.49     ).
% 7.62/1.49  
% 7.62/1.49  %------ Negative definition of r1_tarski 
% 7.62/1.49  fof(lit_def,axiom,
% 7.62/1.49      (! [X0,X1] : 
% 7.62/1.49        ( ~(r1_tarski(X0,X1)) <=>
% 7.62/1.49             (
% 7.62/1.49                (
% 7.62/1.49                  ( X0=sK0 & X1=sK1 )
% 7.62/1.49                )
% 7.62/1.49  
% 7.62/1.49             )
% 7.62/1.49        )
% 7.62/1.49      )
% 7.62/1.49     ).
% 7.62/1.49  % SZS output end Model for theBenchmark.p
% 7.62/1.49  ------                               Statistics
% 7.62/1.49  
% 7.62/1.49  ------ Selected
% 7.62/1.49  
% 7.62/1.49  total_time:                             0.512
% 7.62/1.49  
%------------------------------------------------------------------------------
