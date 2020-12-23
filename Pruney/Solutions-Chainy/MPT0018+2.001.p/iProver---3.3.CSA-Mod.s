%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:22:15 EST 2020

% Result     : CounterSatisfiable 3.79s
% Output     : Model 3.79s
% Verified   : 
% Statistics : Number of formulae       :    2 (   2 expanded)
%              Number of leaves         :    2 (   2 expanded)
%              Depth                    :    0
%              Number of atoms          :    9 (   9 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :    9 (   6 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%------ Negative definition of equality_sorted 
fof(lit_def,axiom,(
    ! [X0_0,X0_2,X1_2] :
      ( ~ equality_sorted(X0_0,X0_2,X1_2)
    <=> ( ( X0_0 = $i
          & X0 = arAF0_k2_xboole_0_0
          & X1 != arAF0_k2_xboole_0_0 )
        | ( X0_0 = $i
          & X1 = arAF0_k2_xboole_0_0
          & X0 != arAF0_k2_xboole_0_0 ) ) ) )).

%------ Positive definition of arAF0_r1_tarski_0_1 
fof(lit_def_001,axiom,(
    ! [X0] :
      ( arAF0_r1_tarski_0_1(X0)
    <=> X0 = arAF0_k2_xboole_0_0 ) )).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:34:54 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.79/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.79/1.01  
% 3.79/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.79/1.01  
% 3.79/1.01  ------  iProver source info
% 3.79/1.01  
% 3.79/1.01  git: date: 2020-06-30 10:37:57 +0100
% 3.79/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.79/1.01  git: non_committed_changes: false
% 3.79/1.01  git: last_make_outside_of_git: false
% 3.79/1.01  
% 3.79/1.01  ------ 
% 3.79/1.01  ------ Parsing...
% 3.79/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.79/1.01  
% 3.79/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.79/1.01  
% 3.79/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.79/1.01  
% 3.79/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.79/1.01  ------ Proving...
% 3.79/1.01  ------ Problem Properties 
% 3.79/1.01  
% 3.79/1.01  
% 3.79/1.01  clauses                                 5
% 3.79/1.01  conjectures                             2
% 3.79/1.01  EPR                                     2
% 3.79/1.01  Horn                                    5
% 3.79/1.01  unary                                   3
% 3.79/1.01  binary                                  1
% 3.79/1.01  lits                                    8
% 3.79/1.01  lits eq                                 1
% 3.79/1.01  fd_pure                                 0
% 3.79/1.01  fd_pseudo                               0
% 3.79/1.01  fd_cond                                 0
% 3.79/1.01  fd_pseudo_cond                          0
% 3.79/1.01  AC symbols                              0
% 3.79/1.01  
% 3.79/1.01  ------ Input Options Time Limit: Unbounded
% 3.79/1.01  
% 3.79/1.01  
% 3.79/1.01  
% 3.79/1.01  
% 3.79/1.01  ------ Preprocessing...
% 3.79/1.01  
% 3.79/1.01  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 3.79/1.01  Current options:
% 3.79/1.01  ------ 
% 3.79/1.01  
% 3.79/1.01  
% 3.79/1.01  
% 3.79/1.01  
% 3.79/1.01  ------ Proving...
% 3.79/1.01  
% 3.79/1.01  
% 3.79/1.01  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.79/1.01  
% 3.79/1.01  ------ Proving...
% 3.79/1.01  
% 3.79/1.01  
% 3.79/1.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.79/1.01  
% 3.79/1.01  ------ Proving...
% 3.79/1.01  
% 3.79/1.01  
% 3.79/1.01  % SZS status CounterSatisfiable for theBenchmark.p
% 3.79/1.01  
% 3.79/1.01  ------ Building Model...Done
% 3.79/1.01  
% 3.79/1.01  %------ The model is defined over ground terms (initial term algebra).
% 3.79/1.01  %------ Predicates are defined as (\forall x_1,..,x_n  ((~)P(x_1,..,x_n) <=> (\phi(x_1,..,x_n)))) 
% 3.79/1.01  %------ where \phi is a formula over the term algebra.
% 3.79/1.01  %------ If we have equality in the problem then it is also defined as a predicate above, 
% 3.79/1.01  %------ with "=" on the right-hand-side of the definition interpreted over the term algebra term_algebra_type
% 3.79/1.01  %------ See help for --sat_out_model for different model outputs.
% 3.79/1.01  %------ equality_sorted(X0,X1,X2) can be used in the place of usual "="
% 3.79/1.01  %------ where the first argument stands for the sort ($i in the unsorted case)
% 3.79/1.01  % SZS output start Model for theBenchmark.p
% 3.79/1.01  
% 3.79/1.01  %------ Negative definition of equality_sorted 
% 3.79/1.01  fof(lit_def,axiom,
% 3.79/1.01      (! [X0_0,X0_2,X1_2] : 
% 3.79/1.01        ( ~(equality_sorted(X0_0,X0_2,X1_2)) <=>
% 3.79/1.01             (
% 3.79/1.01                (
% 3.79/1.01                  ( X0_0=$i & X0=arAF0_k2_xboole_0_0 )
% 3.79/1.01                 &
% 3.79/1.01                  ( X1!=arAF0_k2_xboole_0_0 )
% 3.79/1.01                )
% 3.79/1.01  
% 3.79/1.01               | 
% 3.79/1.01                (
% 3.79/1.01                  ( X0_0=$i & X1=arAF0_k2_xboole_0_0 )
% 3.79/1.01                 &
% 3.79/1.01                  ( X0!=arAF0_k2_xboole_0_0 )
% 3.79/1.01                )
% 3.79/1.01  
% 3.79/1.01             )
% 3.79/1.01        )
% 3.79/1.01      )
% 3.79/1.01     ).
% 3.79/1.01  
% 3.79/1.01  %------ Positive definition of arAF0_r1_tarski_0_1 
% 3.79/1.01  fof(lit_def,axiom,
% 3.79/1.01      (! [X0] : 
% 3.79/1.01        ( arAF0_r1_tarski_0_1(X0) <=>
% 3.79/1.01             (
% 3.79/1.01                (
% 3.79/1.01                  ( X0=arAF0_k2_xboole_0_0 )
% 3.79/1.01                )
% 3.79/1.01  
% 3.79/1.01             )
% 3.79/1.01        )
% 3.79/1.01      )
% 3.79/1.01     ).
% 3.79/1.01  % SZS output end Model for theBenchmark.p
% 3.79/1.01  ------                               Statistics
% 3.79/1.01  
% 3.79/1.01  ------ Selected
% 3.79/1.01  
% 3.79/1.01  total_time:                             0.022
% 3.79/1.01  
%------------------------------------------------------------------------------
