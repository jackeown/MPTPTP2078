%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:22:44 EST 2020

% Result     : CounterSatisfiable 1.94s
% Output     : Model 1.94s
% Verified   : 
% Statistics : Number of formulae       :    1 (   1 expanded)
%              Number of leaves         :    1 (   1 expanded)
%              Depth                    :    0
%              Number of atoms          :   96 (  96 expanded)
%              Number of equality atoms :   95 (  95 expanded)
%              Maximal formula depth    :   32 (  32 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%------ Positive definition of equality_sorted 
fof(lit_def,axiom,(
    ! [X0_0,X0,X1] :
      ( equality_sorted(X0_0,X0,X1)
    <=> ( ( X0_0 = $i
          & ( X0 != k1_xboole_0
            | X1 != k4_xboole_0(sK0,k2_xboole_0(sK0,sK1)) )
          & ( X0 != k1_xboole_0
            | X1 != k4_xboole_0(X1,X2) )
          & ( X0 != k1_xboole_0
            | X1 != k4_xboole_0(sK0,sK0) )
          & ( X0 != k1_xboole_0
            | X1 != k4_xboole_0(k4_xboole_0(sK0,sK0),sK1) )
          & X0 != sK0
          & X0 != sK1
          & X0 != k2_xboole_0(sK0,sK1)
          & X0 != k4_xboole_0(sK0,k2_xboole_0(sK0,sK1))
          & ( X0 != k4_xboole_0(sK0,k2_xboole_0(sK0,sK1))
            | X1 != k1_xboole_0 )
          & X0 != k4_xboole_0(sK0,sK0)
          & X0 != k4_xboole_0(k4_xboole_0(sK0,sK0),sK1)
          & X1 != sK0
          & X1 != sK1
          & X1 != k2_xboole_0(sK0,sK1)
          & X1 != k4_xboole_0(sK0,k2_xboole_0(sK0,sK1))
          & X1 != k4_xboole_0(sK0,sK0)
          & X1 != k4_xboole_0(k4_xboole_0(sK0,sK0),sK1) )
        | ? [X2,X3] :
            ( X0_0 = $i
            & X0 = k1_xboole_0
            & X1 = k4_xboole_0(X2,X3)
            & ( X2 != sK0
              | X3 != sK0 )
            & ( X2 != sK0
              | X3 != k2_xboole_0(sK0,sK1) )
            & ( X2 != k4_xboole_0(sK0,sK0)
              | X3 != sK1 ) )
        | ( X0_0 = $i
          & X0 = sK0
          & X1 = sK0 )
        | ( X0_0 = $i
          & X0 = sK1
          & X1 = sK1 )
        | ( X0_0 = $i
          & X0 = k2_xboole_0(sK0,sK1)
          & X1 = k2_xboole_0(sK0,sK1) )
        | ( X0_0 = $i
          & X0 = k4_xboole_0(sK0,k2_xboole_0(sK0,sK1))
          & X1 = k4_xboole_0(sK0,k2_xboole_0(sK0,sK1)) )
        | ( X0_0 = $i
          & X0 = k4_xboole_0(sK0,k2_xboole_0(sK0,sK1))
          & X1 = k4_xboole_0(k4_xboole_0(sK0,sK0),sK1) )
        | ? [X2,X3,X4,X5] :
            ( X0_0 = $i
            & X0 = k2_xboole_0(X2,X3)
            & X1 = k2_xboole_0(X4,X5)
            & ( X2 != sK0
              | X3 != sK1 )
            & ( X4 != sK0
              | X5 != sK1 ) )
        | ( X0_0 = $i
          & X0 = k4_xboole_0(sK0,sK0)
          & X1 = k4_xboole_0(sK0,sK0) )
        | ( X0_0 = $i
          & X0 = k4_xboole_0(k4_xboole_0(sK0,sK0),sK1)
          & X1 = k4_xboole_0(sK0,k2_xboole_0(sK0,sK1)) )
        | ( X0_0 = $i
          & X0 = k4_xboole_0(k4_xboole_0(sK0,sK0),sK1)
          & X1 = k4_xboole_0(k4_xboole_0(sK0,sK0),sK1) )
        | ? [X2] :
            ( X0_0 = $i
            & X0 = k4_xboole_0(k1_xboole_0,X2)
            & X1 = k1_xboole_0 )
        | ? [X2,X3,X4,X5] :
            ( X0_0 = $i
            & X0 = k4_xboole_0(X2,X3)
            & X1 = k4_xboole_0(X4,X5)
            & ( X2 != sK0
              | X3 != sK0 )
            & ( X2 != sK0
              | X3 != k2_xboole_0(sK0,sK1) )
            & ( X2 != k4_xboole_0(sK0,sK0)
              | X3 != sK1 )
            & ( X4 != sK0
              | X5 != sK0 )
            & ( X4 != sK0
              | X5 != k2_xboole_0(sK0,sK1) )
            & ( X4 != k4_xboole_0(sK0,sK0)
              | X5 != sK1 ) )
        | ? [X2,X3,X4] :
            ( X0_0 = $i
            & X0 = k4_xboole_0(k4_xboole_0(X2,X3),X4)
            & X1 = k4_xboole_0(X2,k2_xboole_0(X3,X4))
            & ( X2 != sK0
              | X3 != sK0
              | X4 != sK1 ) )
        | ( X0_0 = $i
          & X1 = X0
          & X0 != sK0
          & X0 != sK1
          & X0 != k2_xboole_0(sK0,sK1)
          & X0 != k4_xboole_0(sK0,k2_xboole_0(sK0,sK1))
          & X0 != k4_xboole_0(sK0,sK0)
          & X0 != k4_xboole_0(k4_xboole_0(sK0,sK0),sK1) ) ) ) )).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:00:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 1.94/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.94/1.00  
% 1.94/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.94/1.00  
% 1.94/1.00  ------  iProver source info
% 1.94/1.00  
% 1.94/1.00  git: date: 2020-06-30 10:37:57 +0100
% 1.94/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.94/1.00  git: non_committed_changes: false
% 1.94/1.00  git: last_make_outside_of_git: false
% 1.94/1.00  
% 1.94/1.00  ------ 
% 1.94/1.00  ------ Parsing...
% 1.94/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.94/1.00  
% 1.94/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 1.94/1.00  
% 1.94/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.94/1.00  
% 1.94/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 1.94/1.00  ------ Proving...
% 1.94/1.00  ------ Problem Properties 
% 1.94/1.00  
% 1.94/1.00  
% 1.94/1.00  clauses                                 3
% 1.94/1.00  conjectures                             1
% 1.94/1.00  EPR                                     0
% 1.94/1.00  Horn                                    3
% 1.94/1.00  unary                                   3
% 1.94/1.00  binary                                  0
% 1.94/1.00  lits                                    3
% 1.94/1.00  lits eq                                 3
% 1.94/1.00  fd_pure                                 0
% 1.94/1.00  fd_pseudo                               0
% 1.94/1.00  fd_cond                                 0
% 1.94/1.00  fd_pseudo_cond                          0
% 1.94/1.00  AC symbols                              0
% 1.94/1.00  
% 1.94/1.00  ------ Input Options Time Limit: Unbounded
% 1.94/1.00  
% 1.94/1.00  
% 1.94/1.00  ------ 
% 1.94/1.00  Current options:
% 1.94/1.00  ------ 
% 1.94/1.00  
% 1.94/1.00  
% 1.94/1.00  
% 1.94/1.00  
% 1.94/1.00  ------ Proving...
% 1.94/1.00  
% 1.94/1.00  
% 1.94/1.00  % SZS status CounterSatisfiable for theBenchmark.p
% 1.94/1.00  
% 1.94/1.00  ------ Building Model...Done
% 1.94/1.00  
% 1.94/1.00  %------ The model is defined over ground terms (initial term algebra).
% 1.94/1.00  %------ Predicates are defined as (\forall x_1,..,x_n  ((~)P(x_1,..,x_n) <=> (\phi(x_1,..,x_n)))) 
% 1.94/1.00  %------ where \phi is a formula over the term algebra.
% 1.94/1.00  %------ If we have equality in the problem then it is also defined as a predicate above, 
% 1.94/1.00  %------ with "=" on the right-hand-side of the definition interpreted over the term algebra term_algebra_type
% 1.94/1.00  %------ See help for --sat_out_model for different model outputs.
% 1.94/1.00  %------ equality_sorted(X0,X1,X2) can be used in the place of usual "="
% 1.94/1.00  %------ where the first argument stands for the sort ($i in the unsorted case)
% 1.94/1.00  % SZS output start Model for theBenchmark.p
% 1.94/1.00  
% 1.94/1.00  %------ Positive definition of equality_sorted 
% 1.94/1.00  fof(lit_def,axiom,
% 1.94/1.00      (! [X0_0,X0,X1] : 
% 1.94/1.00        ( equality_sorted(X0_0,X0,X1) <=>
% 1.94/1.00             (
% 1.94/1.00                (
% 1.94/1.00                  ( X0_0=$i )
% 1.94/1.00                 &
% 1.94/1.00                  ( X0!=k1_xboole_0 | X1!=k4_xboole_0(sK0,k2_xboole_0(sK0,sK1)) )
% 1.94/1.00                 &
% 1.94/1.00                  ( X0!=k1_xboole_0 | X1!=k4_xboole_0(X1,X2) )
% 1.94/1.00                 &
% 1.94/1.00                  ( X0!=k1_xboole_0 | X1!=k4_xboole_0(sK0,sK0) )
% 1.94/1.00                 &
% 1.94/1.00                  ( X0!=k1_xboole_0 | X1!=k4_xboole_0(k4_xboole_0(sK0,sK0),sK1) )
% 1.94/1.00                 &
% 1.94/1.00                  ( X0!=sK0 )
% 1.94/1.00                 &
% 1.94/1.00                  ( X0!=sK1 )
% 1.94/1.00                 &
% 1.94/1.00                  ( X0!=k2_xboole_0(sK0,sK1) )
% 1.94/1.00                 &
% 1.94/1.00                  ( X0!=k4_xboole_0(sK0,k2_xboole_0(sK0,sK1)) )
% 1.94/1.00                 &
% 1.94/1.00                  ( X0!=k4_xboole_0(sK0,k2_xboole_0(sK0,sK1)) | X1!=k1_xboole_0 )
% 1.94/1.00                 &
% 1.94/1.00                  ( X0!=k4_xboole_0(sK0,sK0) )
% 1.94/1.00                 &
% 1.94/1.00                  ( X0!=k4_xboole_0(k4_xboole_0(sK0,sK0),sK1) )
% 1.94/1.00                 &
% 1.94/1.00                  ( X1!=sK0 )
% 1.94/1.00                 &
% 1.94/1.00                  ( X1!=sK1 )
% 1.94/1.00                 &
% 1.94/1.00                  ( X1!=k2_xboole_0(sK0,sK1) )
% 1.94/1.00                 &
% 1.94/1.00                  ( X1!=k4_xboole_0(sK0,k2_xboole_0(sK0,sK1)) )
% 1.94/1.00                 &
% 1.94/1.00                  ( X1!=k4_xboole_0(sK0,sK0) )
% 1.94/1.00                 &
% 1.94/1.00                  ( X1!=k4_xboole_0(k4_xboole_0(sK0,sK0),sK1) )
% 1.94/1.00                )
% 1.94/1.00  
% 1.94/1.00               | 
% 1.94/1.00              ? [X2,X3] : 
% 1.94/1.00                (
% 1.94/1.00                  ( X0_0=$i & X0=k1_xboole_0 & X1=k4_xboole_0(X2,X3) )
% 1.94/1.00                 &
% 1.94/1.00                  ( X2!=sK0 | X3!=sK0 )
% 1.94/1.00                 &
% 1.94/1.00                  ( X2!=sK0 | X3!=k2_xboole_0(sK0,sK1) )
% 1.94/1.00                 &
% 1.94/1.00                  ( X2!=k4_xboole_0(sK0,sK0) | X3!=sK1 )
% 1.94/1.00                )
% 1.94/1.00  
% 1.94/1.00               | 
% 1.94/1.00                (
% 1.94/1.00                  ( X0_0=$i & X0=sK0 & X1=sK0 )
% 1.94/1.00                )
% 1.94/1.00  
% 1.94/1.00               | 
% 1.94/1.00                (
% 1.94/1.00                  ( X0_0=$i & X0=sK1 & X1=sK1 )
% 1.94/1.00                )
% 1.94/1.00  
% 1.94/1.00               | 
% 1.94/1.00                (
% 1.94/1.00                  ( X0_0=$i & X0=k2_xboole_0(sK0,sK1) & X1=k2_xboole_0(sK0,sK1) )
% 1.94/1.00                )
% 1.94/1.00  
% 1.94/1.00               | 
% 1.94/1.00                (
% 1.94/1.00                  ( X0_0=$i & X0=k4_xboole_0(sK0,k2_xboole_0(sK0,sK1)) & X1=k4_xboole_0(sK0,k2_xboole_0(sK0,sK1)) )
% 1.94/1.00                )
% 1.94/1.00  
% 1.94/1.00               | 
% 1.94/1.00                (
% 1.94/1.00                  ( X0_0=$i & X0=k4_xboole_0(sK0,k2_xboole_0(sK0,sK1)) & X1=k4_xboole_0(k4_xboole_0(sK0,sK0),sK1) )
% 1.94/1.00                )
% 1.94/1.00  
% 1.94/1.00               | 
% 1.94/1.00              ? [X2,X3,X4,X5] : 
% 1.94/1.00                (
% 1.94/1.00                  ( X0_0=$i & X0=k2_xboole_0(X2,X3) & X1=k2_xboole_0(X4,X5) )
% 1.94/1.00                 &
% 1.94/1.00                  ( X2!=sK0 | X3!=sK1 )
% 1.94/1.00                 &
% 1.94/1.00                  ( X4!=sK0 | X5!=sK1 )
% 1.94/1.00                )
% 1.94/1.00  
% 1.94/1.00               | 
% 1.94/1.00                (
% 1.94/1.00                  ( X0_0=$i & X0=k4_xboole_0(sK0,sK0) & X1=k4_xboole_0(sK0,sK0) )
% 1.94/1.00                )
% 1.94/1.00  
% 1.94/1.00               | 
% 1.94/1.00                (
% 1.94/1.00                  ( X0_0=$i & X0=k4_xboole_0(k4_xboole_0(sK0,sK0),sK1) & X1=k4_xboole_0(sK0,k2_xboole_0(sK0,sK1)) )
% 1.94/1.00                )
% 1.94/1.00  
% 1.94/1.00               | 
% 1.94/1.00                (
% 1.94/1.00                  ( X0_0=$i & X0=k4_xboole_0(k4_xboole_0(sK0,sK0),sK1) & X1=k4_xboole_0(k4_xboole_0(sK0,sK0),sK1) )
% 1.94/1.00                )
% 1.94/1.00  
% 1.94/1.00               | 
% 1.94/1.00              ? [X2] : 
% 1.94/1.00                (
% 1.94/1.00                  ( X0_0=$i & X0=k4_xboole_0(k1_xboole_0,X2) & X1=k1_xboole_0 )
% 1.94/1.00                )
% 1.94/1.00  
% 1.94/1.00               | 
% 1.94/1.00              ? [X2,X3,X4,X5] : 
% 1.94/1.00                (
% 1.94/1.00                  ( X0_0=$i & X0=k4_xboole_0(X2,X3) & X1=k4_xboole_0(X4,X5) )
% 1.94/1.00                 &
% 1.94/1.00                  ( X2!=sK0 | X3!=sK0 )
% 1.94/1.00                 &
% 1.94/1.00                  ( X2!=sK0 | X3!=k2_xboole_0(sK0,sK1) )
% 1.94/1.00                 &
% 1.94/1.00                  ( X2!=k4_xboole_0(sK0,sK0) | X3!=sK1 )
% 1.94/1.00                 &
% 1.94/1.00                  ( X4!=sK0 | X5!=sK0 )
% 1.94/1.00                 &
% 1.94/1.00                  ( X4!=sK0 | X5!=k2_xboole_0(sK0,sK1) )
% 1.94/1.00                 &
% 1.94/1.00                  ( X4!=k4_xboole_0(sK0,sK0) | X5!=sK1 )
% 1.94/1.00                )
% 1.94/1.00  
% 1.94/1.00               | 
% 1.94/1.00              ? [X2,X3,X4] : 
% 1.94/1.00                (
% 1.94/1.00                  ( X0_0=$i & X0=k4_xboole_0(k4_xboole_0(X2,X3),X4) & X1=k4_xboole_0(X2,k2_xboole_0(X3,X4)) )
% 1.94/1.00                 &
% 1.94/1.00                  ( X2!=sK0 | X3!=sK0 | X4!=sK1 )
% 1.94/1.00                )
% 1.94/1.00  
% 1.94/1.00               | 
% 1.94/1.00                (
% 1.94/1.00                  ( X0_0=$i & X1=X0 )
% 1.94/1.00                 &
% 1.94/1.00                  ( X0!=sK0 )
% 1.94/1.00                 &
% 1.94/1.00                  ( X0!=sK1 )
% 1.94/1.00                 &
% 1.94/1.00                  ( X0!=k2_xboole_0(sK0,sK1) )
% 1.94/1.00                 &
% 1.94/1.00                  ( X0!=k4_xboole_0(sK0,k2_xboole_0(sK0,sK1)) )
% 1.94/1.00                 &
% 1.94/1.00                  ( X0!=k4_xboole_0(sK0,sK0) )
% 1.94/1.00                 &
% 1.94/1.00                  ( X0!=k4_xboole_0(k4_xboole_0(sK0,sK0),sK1) )
% 1.94/1.00                )
% 1.94/1.00  
% 1.94/1.00             )
% 1.94/1.00        )
% 1.94/1.00      )
% 1.94/1.00     ).
% 1.94/1.00  % SZS output end Model for theBenchmark.p
% 1.94/1.00  ------                               Statistics
% 1.94/1.00  
% 1.94/1.00  ------ Selected
% 1.94/1.00  
% 1.94/1.00  total_time:                             0.071
% 1.94/1.00  
%------------------------------------------------------------------------------
