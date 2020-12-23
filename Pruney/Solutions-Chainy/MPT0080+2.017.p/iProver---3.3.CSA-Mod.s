%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:23:56 EST 2020

% Result     : CounterSatisfiable 3.47s
% Output     : Model 3.47s
% Verified   : 
% Statistics : Number of formulae       :    3 (   3 expanded)
%              Number of leaves         :    3 (   3 expanded)
%              Depth                    :    0
%              Number of atoms          :  127 ( 127 expanded)
%              Number of equality atoms :  124 ( 124 expanded)
%              Maximal formula depth    :   31 (  14 average)
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
            | X1 != k4_xboole_0(X1,X2) )
          & X0 != sK0
          & X0 != sK1
          & X0 != sK2
          & X0 != arAF0_k2_xboole_0_0
          & X0 != k4_xboole_0(sK0,sK2)
          & ( X0 != k4_xboole_0(sK0,sK2)
            | X1 != k1_xboole_0 )
          & X0 != k4_xboole_0(sK0,sK1)
          & ( X0 != k4_xboole_0(sK0,sK1)
            | X1 != k1_xboole_0 )
          & ( X0 != k4_xboole_0(X2,X0)
            | X1 != k1_xboole_0 )
          & ( X0 != k4_xboole_0(X2,X0)
            | X1 != sK0 )
          & ( X0 != k4_xboole_0(X2,X0)
            | X1 != sK1 )
          & ( X0 != k4_xboole_0(X2,X0)
            | X1 != arAF0_k2_xboole_0_0 )
          & ( X0 != k4_xboole_0(X2,X0)
            | X1 != k4_xboole_0(sK0,sK2) )
          & ! [X3] : X0 != k4_xboole_0(X0,X3)
          & X1 != sK0
          & X1 != sK1
          & X1 != sK2
          & X1 != arAF0_k2_xboole_0_0
          & X1 != k4_xboole_0(sK0,sK2)
          & X1 != k4_xboole_0(sK0,sK1) )
        | ? [X2,X3] :
            ( X0_0 = $i
            & X0 = k1_xboole_0
            & X1 = k4_xboole_0(X2,X3)
            & ( X2 != sK0
              | X3 != sK1 )
            & ( X2 != sK0
              | X3 != sK2 ) )
        | ( X0_0 = $i
          & X0 = k4_xboole_0(sK0,sK2)
          & X1 = k4_xboole_0(sK0,sK2) )
        | ( X0_0 = $i
          & X0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))
          & X1 != sK0
          & X1 != sK1
          & X1 != sK2
          & X1 != arAF0_k2_xboole_0_0
          & X1 != k4_xboole_0(sK0,sK2)
          & X1 != k4_xboole_0(sK0,sK1) )
        | ( X0_0 = $i
          & X0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))
          & X1 = k1_xboole_0 )
        | ( X0_0 = $i
          & X0 = k4_xboole_0(sK0,arAF0_k2_xboole_0_0)
          & X1 != sK0
          & X1 != sK1
          & X1 != sK2
          & X1 != arAF0_k2_xboole_0_0
          & X1 != k4_xboole_0(sK0,sK2)
          & X1 != k4_xboole_0(sK0,sK1) )
        | ( X0_0 = $i
          & X0 = k4_xboole_0(sK0,arAF0_k2_xboole_0_0)
          & X1 = k1_xboole_0 )
        | ? [X2,X3] :
            ( X0_0 = $i
            & X0 = k4_xboole_0(X2,X3)
            & ( X1 != k1_xboole_0
              | X2 != sK0
              | X3 != sK1 )
            & ( X1 != k1_xboole_0
              | X2 != sK0
              | X3 != sK2 )
            & X1 != sK0
            & X1 != sK1
            & X1 != sK2
            & X1 != arAF0_k2_xboole_0_0
            & X1 != k4_xboole_0(sK0,sK2)
            & ( X1 != k4_xboole_0(X1,X2)
              | X2 != sK0
              | X3 != sK1 )
            & ( X1 != k4_xboole_0(X1,X2)
              | X2 != sK0
              | X3 != sK2 )
            & X1 != k4_xboole_0(sK0,sK1)
            & ( X2 != sK0
              | X3 != sK1 )
            & ( X2 != sK0
              | X3 != sK2 ) )
        | ? [X2,X3] :
            ( X0_0 = $i
            & X0 = k4_xboole_0(X2,X3)
            & X1 = k1_xboole_0
            & ( X2 != sK0
              | X3 != sK1 )
            & ( X2 != sK0
              | X3 != sK2 )
            & ( X2 != sK0
              | X3 != arAF0_k2_xboole_0_0 )
            & ( X2 != sK0
              | X3 != k4_xboole_0(sK0,sK2) ) )
        | ? [X2,X3,X4,X5] :
            ( X0_0 = $i
            & X0 = k4_xboole_0(X2,X3)
            & X1 = k4_xboole_0(X4,X5)
            & ( X2 != sK0
              | X3 != sK1 )
            & ( X2 != sK0
              | X3 != sK2 )
            & ( X4 != sK0
              | X5 != sK1 )
            & ( X4 != sK0
              | X5 != sK2 ) )
        | ( X0_0 = $i
          & X0 = k4_xboole_0(sK0,sK1)
          & X1 = k4_xboole_0(sK0,sK1) )
        | ? [X2,X3,X4] :
            ( X0_0 = $i
            & X0 = k4_xboole_0(k4_xboole_0(X2,X3),X4)
            & X1 = k4_xboole_0(X2,arAF0_k2_xboole_0_0) )
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
    <=> ( ( X0 = sK0
          & X1 = sK1 )
        | ( X0 = sK0
          & X1 = sK2 ) ) ) )).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:42:57 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.47/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.47/0.98  
% 3.47/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.47/0.98  
% 3.47/0.98  ------  iProver source info
% 3.47/0.98  
% 3.47/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.47/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.47/0.98  git: non_committed_changes: false
% 3.47/0.98  git: last_make_outside_of_git: false
% 3.47/0.98  
% 3.47/0.98  ------ 
% 3.47/0.98  ------ Parsing...
% 3.47/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.47/0.98  
% 3.47/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.47/0.98  
% 3.47/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.47/0.98  
% 3.47/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.47/0.98  ------ Proving...
% 3.47/0.98  ------ Problem Properties 
% 3.47/0.98  
% 3.47/0.98  
% 3.47/0.98  clauses                                 9
% 3.47/0.98  conjectures                             3
% 3.47/0.98  EPR                                     2
% 3.47/0.98  Horn                                    9
% 3.47/0.98  unary                                   6
% 3.47/0.98  binary                                  3
% 3.47/0.98  lits                                    12
% 3.47/0.98  lits eq                                 6
% 3.47/0.98  fd_pure                                 0
% 3.47/0.98  fd_pseudo                               0
% 3.47/0.98  fd_cond                                 0
% 3.47/0.98  fd_pseudo_cond                          0
% 3.47/0.98  AC symbols                              0
% 3.47/0.98  
% 3.47/0.98  ------ Input Options Time Limit: Unbounded
% 3.47/0.98  
% 3.47/0.98  
% 3.47/0.98  
% 3.47/0.98  
% 3.47/0.98  ------ Preprocessing...
% 3.47/0.98  
% 3.47/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e ------ 
% 3.47/0.98  Current options:
% 3.47/0.98  ------ 
% 3.47/0.98  
% 3.47/0.98  
% 3.47/0.98  
% 3.47/0.98  
% 3.47/0.98  ------ Proving...
% 3.47/0.98  
% 3.47/0.98  
% 3.47/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.47/0.98  
% 3.47/0.98  ------ Proving...
% 3.47/0.98  
% 3.47/0.98  
% 3.47/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.47/0.98  
% 3.47/0.98  ------ Proving...
% 3.47/0.98  
% 3.47/0.98  
% 3.47/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.47/0.98  
% 3.47/0.98  ------ Proving...
% 3.47/0.98  
% 3.47/0.98  
% 3.47/0.98  % SZS status CounterSatisfiable for theBenchmark.p
% 3.47/0.98  
% 3.47/0.98  ------ Building Model...Done
% 3.47/0.98  
% 3.47/0.98  %------ The model is defined over ground terms (initial term algebra).
% 3.47/0.98  %------ Predicates are defined as (\forall x_1,..,x_n  ((~)P(x_1,..,x_n) <=> (\phi(x_1,..,x_n)))) 
% 3.47/0.98  %------ where \phi is a formula over the term algebra.
% 3.47/0.98  %------ If we have equality in the problem then it is also defined as a predicate above, 
% 3.47/0.98  %------ with "=" on the right-hand-side of the definition interpreted over the term algebra term_algebra_type
% 3.47/0.98  %------ See help for --sat_out_model for different model outputs.
% 3.47/0.98  %------ equality_sorted(X0,X1,X2) can be used in the place of usual "="
% 3.47/0.98  %------ where the first argument stands for the sort ($i in the unsorted case)
% 3.47/0.98  % SZS output start Model for theBenchmark.p
% 3.47/0.98  
% 3.47/0.98  %------ Positive definition of equality_sorted 
% 3.47/0.98  fof(lit_def,axiom,
% 3.47/0.98      (! [X0_0,X0_2,X1_2] : 
% 3.47/0.98        ( equality_sorted(X0_0,X0_2,X1_2) <=>
% 3.47/0.98             (
% 3.47/0.98                (
% 3.47/0.98                  ( X0_0=$o & X1_2=X0_2 )
% 3.47/0.98                )
% 3.47/0.98  
% 3.47/0.98               | 
% 3.47/0.98                (
% 3.47/0.98                  ( X0_0=$i )
% 3.47/0.98                 &
% 3.47/0.98                  ( X0!=k1_xboole_0 | X1!=k4_xboole_0(X1,X2) )
% 3.47/0.98                 &
% 3.47/0.98                  ( X0!=sK0 )
% 3.47/0.98                 &
% 3.47/0.98                  ( X0!=sK1 )
% 3.47/0.98                 &
% 3.47/0.98                  ( X0!=sK2 )
% 3.47/0.98                 &
% 3.47/0.98                  ( X0!=arAF0_k2_xboole_0_0 )
% 3.47/0.98                 &
% 3.47/0.98                  ( X0!=k4_xboole_0(sK0,sK2) )
% 3.47/0.98                 &
% 3.47/0.98                  ( X0!=k4_xboole_0(sK0,sK2) | X1!=k1_xboole_0 )
% 3.47/0.98                 &
% 3.47/0.98                  ( X0!=k4_xboole_0(sK0,sK1) )
% 3.47/0.98                 &
% 3.47/0.98                  ( X0!=k4_xboole_0(sK0,sK1) | X1!=k1_xboole_0 )
% 3.47/0.98                 &
% 3.47/0.98                  ( X0!=k4_xboole_0(X2,X0) | X1!=k1_xboole_0 )
% 3.47/0.98                 &
% 3.47/0.98                  ( X0!=k4_xboole_0(X2,X0) | X1!=sK0 )
% 3.47/0.98                 &
% 3.47/0.98                  ( X0!=k4_xboole_0(X2,X0) | X1!=sK1 )
% 3.47/0.98                 &
% 3.47/0.98                  ( X0!=k4_xboole_0(X2,X0) | X1!=arAF0_k2_xboole_0_0 )
% 3.47/0.98                 &
% 3.47/0.98                  ( X0!=k4_xboole_0(X2,X0) | X1!=k4_xboole_0(sK0,sK2) )
% 3.47/0.98                 &
% 3.47/0.98                  ! [X3] : ( X0!=k4_xboole_0(X0,X3) )
% 3.47/0.98                 &
% 3.47/0.98                  ( X1!=sK0 )
% 3.47/0.98                 &
% 3.47/0.98                  ( X1!=sK1 )
% 3.47/0.98                 &
% 3.47/0.98                  ( X1!=sK2 )
% 3.47/0.98                 &
% 3.47/0.98                  ( X1!=arAF0_k2_xboole_0_0 )
% 3.47/0.98                 &
% 3.47/0.98                  ( X1!=k4_xboole_0(sK0,sK2) )
% 3.47/0.98                 &
% 3.47/0.98                  ( X1!=k4_xboole_0(sK0,sK1) )
% 3.47/0.98                )
% 3.47/0.98  
% 3.47/0.98               | 
% 3.47/0.98              ? [X2,X3] : 
% 3.47/0.98                (
% 3.47/0.98                  ( X0_0=$i & X0=k1_xboole_0 & X1=k4_xboole_0(X2,X3) )
% 3.47/0.98                 &
% 3.47/0.98                  ( X2!=sK0 | X3!=sK1 )
% 3.47/0.98                 &
% 3.47/0.98                  ( X2!=sK0 | X3!=sK2 )
% 3.47/0.98                )
% 3.47/0.98  
% 3.47/0.98               | 
% 3.47/0.98                (
% 3.47/0.98                  ( X0_0=$i & X0=k4_xboole_0(sK0,sK2) & X1=k4_xboole_0(sK0,sK2) )
% 3.47/0.98                )
% 3.47/0.98  
% 3.47/0.98               | 
% 3.47/0.98                (
% 3.47/0.98                  ( X0_0=$i & X0=k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) )
% 3.47/0.98                 &
% 3.47/0.98                  ( X1!=sK0 )
% 3.47/0.98                 &
% 3.47/0.98                  ( X1!=sK1 )
% 3.47/0.98                 &
% 3.47/0.98                  ( X1!=sK2 )
% 3.47/0.98                 &
% 3.47/0.98                  ( X1!=arAF0_k2_xboole_0_0 )
% 3.47/0.98                 &
% 3.47/0.98                  ( X1!=k4_xboole_0(sK0,sK2) )
% 3.47/0.98                 &
% 3.47/0.98                  ( X1!=k4_xboole_0(sK0,sK1) )
% 3.47/0.98                )
% 3.47/0.98  
% 3.47/0.98               | 
% 3.47/0.98                (
% 3.47/0.98                  ( X0_0=$i & X0=k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) & X1=k1_xboole_0 )
% 3.47/0.98                )
% 3.47/0.98  
% 3.47/0.98               | 
% 3.47/0.98                (
% 3.47/0.98                  ( X0_0=$i & X0=k4_xboole_0(sK0,arAF0_k2_xboole_0_0) )
% 3.47/0.98                 &
% 3.47/0.98                  ( X1!=sK0 )
% 3.47/0.98                 &
% 3.47/0.98                  ( X1!=sK1 )
% 3.47/0.98                 &
% 3.47/0.98                  ( X1!=sK2 )
% 3.47/0.98                 &
% 3.47/0.98                  ( X1!=arAF0_k2_xboole_0_0 )
% 3.47/0.98                 &
% 3.47/0.98                  ( X1!=k4_xboole_0(sK0,sK2) )
% 3.47/0.98                 &
% 3.47/0.98                  ( X1!=k4_xboole_0(sK0,sK1) )
% 3.47/0.98                )
% 3.47/0.98  
% 3.47/0.98               | 
% 3.47/0.98                (
% 3.47/0.98                  ( X0_0=$i & X0=k4_xboole_0(sK0,arAF0_k2_xboole_0_0) & X1=k1_xboole_0 )
% 3.47/0.98                )
% 3.47/0.98  
% 3.47/0.98               | 
% 3.47/0.98              ? [X2,X3] : 
% 3.47/0.98                (
% 3.47/0.98                  ( X0_0=$i & X0=k4_xboole_0(X2,X3) )
% 3.47/0.98                 &
% 3.47/0.98                  ( X1!=k1_xboole_0 | X2!=sK0 | X3!=sK1 )
% 3.47/0.98                 &
% 3.47/0.98                  ( X1!=k1_xboole_0 | X2!=sK0 | X3!=sK2 )
% 3.47/0.98                 &
% 3.47/0.98                  ( X1!=sK0 )
% 3.47/0.98                 &
% 3.47/0.98                  ( X1!=sK1 )
% 3.47/0.98                 &
% 3.47/0.98                  ( X1!=sK2 )
% 3.47/0.98                 &
% 3.47/0.98                  ( X1!=arAF0_k2_xboole_0_0 )
% 3.47/0.98                 &
% 3.47/0.98                  ( X1!=k4_xboole_0(sK0,sK2) )
% 3.47/0.98                 &
% 3.47/0.98                  ( X1!=k4_xboole_0(X1,X2) | X2!=sK0 | X3!=sK1 )
% 3.47/0.98                 &
% 3.47/0.98                  ( X1!=k4_xboole_0(X1,X2) | X2!=sK0 | X3!=sK2 )
% 3.47/0.98                 &
% 3.47/0.98                  ( X1!=k4_xboole_0(sK0,sK1) )
% 3.47/0.98                 &
% 3.47/0.98                  ( X2!=sK0 | X3!=sK1 )
% 3.47/0.98                 &
% 3.47/0.98                  ( X2!=sK0 | X3!=sK2 )
% 3.47/0.98                )
% 3.47/0.98  
% 3.47/0.98               | 
% 3.47/0.98              ? [X2,X3] : 
% 3.47/0.98                (
% 3.47/0.98                  ( X0_0=$i & X0=k4_xboole_0(X2,X3) & X1=k1_xboole_0 )
% 3.47/0.98                 &
% 3.47/0.98                  ( X2!=sK0 | X3!=sK1 )
% 3.47/0.98                 &
% 3.47/0.98                  ( X2!=sK0 | X3!=sK2 )
% 3.47/0.98                 &
% 3.47/0.98                  ( X2!=sK0 | X3!=arAF0_k2_xboole_0_0 )
% 3.47/0.98                 &
% 3.47/0.98                  ( X2!=sK0 | X3!=k4_xboole_0(sK0,sK2) )
% 3.47/0.98                )
% 3.47/0.98  
% 3.47/0.98               | 
% 3.47/0.98              ? [X2,X3,X4,X5] : 
% 3.47/0.98                (
% 3.47/0.98                  ( X0_0=$i & X0=k4_xboole_0(X2,X3) & X1=k4_xboole_0(X4,X5) )
% 3.47/0.98                 &
% 3.47/0.98                  ( X2!=sK0 | X3!=sK1 )
% 3.47/0.98                 &
% 3.47/0.98                  ( X2!=sK0 | X3!=sK2 )
% 3.47/0.98                 &
% 3.47/0.98                  ( X4!=sK0 | X5!=sK1 )
% 3.47/0.98                 &
% 3.47/0.98                  ( X4!=sK0 | X5!=sK2 )
% 3.47/0.98                )
% 3.47/0.98  
% 3.47/0.98               | 
% 3.47/0.98                (
% 3.47/0.98                  ( X0_0=$i & X0=k4_xboole_0(sK0,sK1) & X1=k4_xboole_0(sK0,sK1) )
% 3.47/0.98                )
% 3.47/0.98  
% 3.47/0.98               | 
% 3.47/0.98              ? [X2,X3,X4] : 
% 3.47/0.98                (
% 3.47/0.98                  ( X0_0=$i & X0=k4_xboole_0(k4_xboole_0(X2,X3),X4) & X1=k4_xboole_0(X2,arAF0_k2_xboole_0_0) )
% 3.47/0.98                )
% 3.47/0.98  
% 3.47/0.98               | 
% 3.47/0.98                (
% 3.47/0.98                  ( X0_0=$i & X1=X0 )
% 3.47/0.98                )
% 3.47/0.98  
% 3.47/0.98             )
% 3.47/0.98        )
% 3.47/0.98      )
% 3.47/0.98     ).
% 3.47/0.98  
% 3.47/0.98  %------ Positive definition of r1_xboole_0 
% 3.47/0.98  fof(lit_def,axiom,
% 3.47/0.98      (! [X0,X1] : 
% 3.47/0.98        ( r1_xboole_0(X0,X1) <=>
% 3.47/0.98             (
% 3.47/0.98                (
% 3.47/0.98                  ( X0=sK0 & X1=sK2 )
% 3.47/0.98                )
% 3.47/0.98  
% 3.47/0.98             )
% 3.47/0.98        )
% 3.47/0.98      )
% 3.47/0.98     ).
% 3.47/0.98  
% 3.47/0.98  %------ Negative definition of r1_tarski 
% 3.47/0.98  fof(lit_def,axiom,
% 3.47/0.98      (! [X0,X1] : 
% 3.47/0.98        ( ~(r1_tarski(X0,X1)) <=>
% 3.47/0.98             (
% 3.47/0.98                (
% 3.47/0.98                  ( X0=sK0 & X1=sK1 )
% 3.47/0.98                )
% 3.47/0.98  
% 3.47/0.98               | 
% 3.47/0.98                (
% 3.47/0.98                  ( X0=sK0 & X1=sK2 )
% 3.47/0.98                )
% 3.47/0.98  
% 3.47/0.98             )
% 3.47/0.98        )
% 3.47/0.98      )
% 3.47/0.98     ).
% 3.47/0.98  % SZS output end Model for theBenchmark.p
% 3.47/0.98  ------                               Statistics
% 3.47/0.98  
% 3.47/0.98  ------ Selected
% 3.47/0.98  
% 3.47/0.98  total_time:                             0.104
% 3.47/0.98  
%------------------------------------------------------------------------------
