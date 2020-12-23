%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:11:32 EST 2020

% Result     : CounterSatisfiable 19.74s
% Output     : Model 19.74s
% Verified   : 
% Statistics : Number of formulae       :    3 (   3 expanded)
%              Number of leaves         :    3 (   3 expanded)
%              Depth                    :    0
%              Number of atoms          :  164 ( 164 expanded)
%              Number of equality atoms :  161 ( 161 expanded)
%              Maximal formula depth    :   37 (  28 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%------ Positive definition of equality_sorted 
fof(lit_def,axiom,(
    ! [X0_0,X0_2,X1_2] :
      ( equality_sorted(X0_0,X0_2,X1_2)
    <=> ( ( X0_0 = $o
          & X1_2 = X0_2 )
        | ( X0_0 = $i
          & ( X0 != sK2
            | X1 != k1_struct_0(X1) )
          & X0 != k1_struct_0(sK1)
          & ( X0 != k1_struct_0(sK1)
            | X1 != sK2 )
          & ( X0 != k1_struct_0(sK1)
            | X1 != sK0(sK0(sK0(sK0(k1_struct_0(X1))))) )
          & X0 != k1_struct_0(X0)
          & ( X0 != k1_struct_0(X0)
            | X1 != sK0(sK0(sK0(sK0(k1_struct_0(X1))))) )
          & X0 != arAF0_k4_mcart_1_0
          & ( X0 != arAF0_k4_mcart_1_0
            | X1 != sK0(k1_struct_0(X1)) )
          & ( X0 != arAF0_k4_mcart_1_0
            | X1 != sK0(sK0(k1_struct_0(X1))) )
          & ( X0 != arAF0_k4_mcart_1_0
            | X1 != sK0(sK0(sK0(k1_struct_0(X1)))) )
          & ( X0 != arAF0_k4_mcart_1_0
            | X1 != sK0(sK0(sK0(sK0(k1_struct_0(X1))))) )
          & X0 != sK0(k1_struct_0(X0))
          & ( X0 != sK0(k1_struct_0(X0))
            | X1 != sK0(sK0(sK0(sK0(k1_struct_0(X1))))) )
          & X0 != sK0(sK0(k1_struct_0(X0)))
          & ( X0 != sK0(sK0(k1_struct_0(X0)))
            | X1 != sK0(sK0(sK0(sK0(k1_struct_0(X1))))) )
          & X0 != sK0(sK0(sK0(k1_struct_0(X0))))
          & ( X0 != sK0(sK0(sK0(k1_struct_0(X0))))
            | X1 != sK0(sK0(sK0(sK0(k1_struct_0(X1))))) )
          & X0 != sK0(sK0(sK0(sK0(k1_struct_0(X0)))))
          & ( X0 != sK0(sK0(sK0(sK0(k1_struct_0(X0)))))
            | X1 != k1_struct_0(X1) )
          & ( X0 != sK0(sK0(sK0(sK0(k1_struct_0(X0)))))
            | X1 != sK0(k1_struct_0(X1)) )
          & ( X0 != sK0(sK0(sK0(sK0(k1_struct_0(X0)))))
            | X1 != sK0(sK0(k1_struct_0(X1))) )
          & ( X0 != sK0(sK0(sK0(sK0(k1_struct_0(X0)))))
            | X1 != sK0(sK0(sK0(k1_struct_0(X1)))) )
          & ( X0 != sK0(sK0(sK0(sK0(k1_struct_0(X2)))))
            | X1 != arAF0_k4_mcart_1_0 )
          & X1 != k1_struct_0(X1)
          & X1 != arAF0_k4_mcart_1_0
          & X1 != sK0(k1_struct_0(X1))
          & X1 != sK0(sK0(k1_struct_0(X1)))
          & X1 != sK0(sK0(sK0(k1_struct_0(X1))))
          & X1 != sK0(sK0(sK0(sK0(k1_struct_0(X1))))) )
        | ( X0_0 = $i
          & X0 = k1_xboole_0
          & X1 != k1_struct_0(X1)
          & X1 != arAF0_k4_mcart_1_0
          & X1 != sK0(k1_struct_0(X1))
          & X1 != sK0(sK0(k1_struct_0(X1)))
          & X1 != sK0(sK0(sK0(k1_struct_0(X1))))
          & X1 != sK0(sK0(sK0(sK0(k1_struct_0(X1))))) )
        | ? [X2] :
            ( X0_0 = $i
            & X0 = k1_xboole_0
            & X1 = sK0(sK0(sK0(sK0(k1_struct_0(X2))))) )
        | ? [X2] :
            ( X0_0 = $i
            & X0 = k1_struct_0(sK1)
            & X1 = k1_struct_0(X2) )
        | ? [X2] :
            ( X0_0 = $i
            & X0 = k1_struct_0(X2)
            & X1 = k1_struct_0(sK1)
            & X2 != sK1 )
        | ? [X2,X3] :
            ( X0_0 = $i
            & X0 = k1_struct_0(X2)
            & X1 = k1_struct_0(X3) )
        | ? [X2] :
            ( X0_0 = $i
            & X0 = sK0(sK0(sK0(sK0(k1_struct_0(X2)))))
            & X1 != k1_struct_0(sK1)
            & X1 != k1_struct_0(X1)
            & X1 != arAF0_k4_mcart_1_0
            & X1 != sK0(k1_struct_0(X1))
            & X1 != sK0(sK0(k1_struct_0(X1)))
            & X1 != sK0(sK0(sK0(k1_struct_0(X1)))) )
        | ( X0_0 = $i
          & X1 = X0 )
        | ? [X2] :
            ( X0_0 = $i
            & X1 = sK0(sK0(sK0(sK0(k1_struct_0(X2)))))
            & X0 != k1_struct_0(sK1)
            & X0 != k1_struct_0(X0)
            & X0 != arAF0_k4_mcart_1_0
            & X0 != sK0(k1_struct_0(X0))
            & X0 != sK0(sK0(k1_struct_0(X0)))
            & X0 != sK0(sK0(sK0(k1_struct_0(X0)))) ) ) ) )).

%------ Positive definition of r2_hidden 
fof(lit_def_001,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
    <=> ( ? [X2] :
            ( X0 = k1_xboole_0
            & X1 = sK0(sK0(k1_struct_0(X2))) )
        | ? [X2] :
            ( X0 = k1_xboole_0
            & X1 = sK0(sK0(sK0(k1_struct_0(X2)))) )
        | ? [X2] :
            ( X0 = sK0(k1_struct_0(X2))
            & X1 = k1_struct_0(X2) )
        | ? [X2,X3] :
            ( X0 = sK0(k1_struct_0(X2))
            & X1 = k1_struct_0(X3) )
        | ( X0 = sK0(arAF0_k4_mcart_1_0)
          & X1 = arAF0_k4_mcart_1_0 )
        | ? [X2] :
            ( X0 = sK0(sK0(k1_struct_0(X2)))
            & X1 = sK0(k1_struct_0(X2)) )
        | ? [X2] :
            ( X0 = sK0(sK0(sK0(k1_struct_0(X2))))
            & X1 = sK0(sK0(k1_struct_0(X2))) )
        | ? [X2] :
            ( X0 = sK0(sK0(sK0(sK0(k1_struct_0(X2)))))
            & X1 = arAF0_k4_mcart_1_0 )
        | ? [X2,X3] :
            ( X0 = sK0(sK0(sK0(sK0(k1_struct_0(X2)))))
            & X1 = sK0(k1_struct_0(X3)) )
        | ? [X2] :
            ( X0 = sK0(sK0(sK0(sK0(k1_struct_0(X2)))))
            & X1 = sK0(sK0(sK0(k1_struct_0(X2)))) )
        | ? [X2,X3] :
            ( X0 = sK0(sK0(sK0(sK0(k1_struct_0(X2)))))
            & X1 = sK0(sK0(k1_struct_0(X3))) )
        | ( X1 = arAF0_k4_mcart_1_0
          & X0 != k1_struct_0(X0)
          & X0 != arAF0_k4_mcart_1_0
          & X0 != sK0(k1_struct_0(X0))
          & X0 != sK0(sK0(k1_struct_0(X0)))
          & X0 != sK0(sK0(sK0(k1_struct_0(X0))))
          & X0 != sK0(sK0(sK0(sK0(k1_struct_0(X0))))) )
        | ? [X2] :
            ( X1 = sK0(k1_struct_0(X2))
            & X0 != k1_struct_0(X0)
            & X0 != arAF0_k4_mcart_1_0
            & X0 != sK0(k1_struct_0(X0))
            & X0 != sK0(sK0(sK0(k1_struct_0(X0))))
            & X0 != sK0(sK0(sK0(sK0(k1_struct_0(X0))))) )
        | ? [X2] :
            ( X1 = sK0(sK0(k1_struct_0(X2)))
            & X0 != k1_struct_0(X0)
            & X0 != arAF0_k4_mcart_1_0
            & X0 != sK0(k1_struct_0(X0))
            & X0 != sK0(sK0(k1_struct_0(X0)))
            & X0 != sK0(sK0(sK0(sK0(k1_struct_0(X0))))) )
        | ? [X2] :
            ( X1 = sK0(sK0(sK0(k1_struct_0(X2))))
            & X0 != k1_xboole_0
            & X0 != k1_struct_0(X0)
            & X0 != arAF0_k4_mcart_1_0
            & X0 != sK0(k1_struct_0(X0))
            & X0 != sK0(sK0(k1_struct_0(X0)))
            & X0 != sK0(sK0(sK0(k1_struct_0(X0))))
            & ( X0 != sK0(sK0(sK0(sK0(k1_struct_0(X0)))))
              | X2 != X0 ) ) ) ) )).

%------ Negative definition of m1_subset_1 
fof(lit_def_002,axiom,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
    <=> ( X0 = arAF0_k4_mcart_1_0
        | ( X0 = arAF0_k4_mcart_1_0
          & X1 = arAF0_k1_zfmisc_1_0 )
        | ? [X2] : X0 = k1_struct_0(X2)
        | ? [X2] :
            ( X0 = k1_struct_0(X2)
            & X1 = arAF0_k1_zfmisc_1_0 )
        | ? [X2] :
            ( X0 = sK0(k1_struct_0(X2))
            & X1 != k1_struct_0(X1)
            & ( X1 != k1_struct_0(X2)
              | X2 != X2 ) )
        | ? [X2] :
            ( X0 = sK0(k1_struct_0(X2))
            & X1 = arAF0_k1_zfmisc_1_0 )
        | ? [X2] :
            ( X0 = sK0(sK0(k1_struct_0(X2)))
            & ( X1 != sK0(k1_struct_0(X2))
              | X2 != X2 )
            & X1 != sK0(k1_struct_0(X1)) )
        | ? [X2] :
            ( X0 = sK0(sK0(k1_struct_0(X2)))
            & X1 = arAF0_k1_zfmisc_1_0 )
        | ? [X2] :
            ( X0 = sK0(sK0(sK0(k1_struct_0(X2))))
            & X1 != sK0(sK0(k1_struct_0(X1)))
            & ( X1 != sK0(sK0(k1_struct_0(X2)))
              | X2 != X2 ) )
        | ? [X2] :
            ( X0 = sK0(sK0(sK0(k1_struct_0(X2))))
            & X1 = arAF0_k1_zfmisc_1_0 ) ) ) )).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:11:04 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 19.74/3.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.74/3.00  
% 19.74/3.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 19.74/3.00  
% 19.74/3.00  ------  iProver source info
% 19.74/3.00  
% 19.74/3.00  git: date: 2020-06-30 10:37:57 +0100
% 19.74/3.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 19.74/3.00  git: non_committed_changes: false
% 19.74/3.00  git: last_make_outside_of_git: false
% 19.74/3.00  
% 19.74/3.00  ------ 
% 19.74/3.00  ------ Parsing...
% 19.74/3.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 19.74/3.00  
% 19.74/3.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 19.74/3.00  
% 19.74/3.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 19.74/3.00  
% 19.74/3.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.74/3.00  ------ Proving...
% 19.74/3.00  ------ Problem Properties 
% 19.74/3.00  
% 19.74/3.00  
% 19.74/3.00  clauses                                 8
% 19.74/3.00  conjectures                             3
% 19.74/3.00  EPR                                     1
% 19.74/3.00  Horn                                    7
% 19.74/3.00  unary                                   2
% 19.74/3.00  binary                                  3
% 19.74/3.00  lits                                    17
% 19.74/3.00  lits eq                                 6
% 19.74/3.00  fd_pure                                 0
% 19.74/3.00  fd_pseudo                               0
% 19.74/3.00  fd_cond                                 3
% 19.74/3.00  fd_pseudo_cond                          0
% 19.74/3.00  AC symbols                              0
% 19.74/3.00  
% 19.74/3.00  ------ Input Options Time Limit: Unbounded
% 19.74/3.00  
% 19.74/3.00  
% 19.74/3.00  
% 19.74/3.00  
% 19.74/3.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 19.74/3.00  Current options:
% 19.74/3.00  ------ 
% 19.74/3.00  
% 19.74/3.00  
% 19.74/3.00  
% 19.74/3.00  
% 19.74/3.00  ------ Proving...
% 19.74/3.00  
% 19.74/3.00  
% 19.74/3.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.74/3.00  
% 19.74/3.00  ------ Proving...
% 19.74/3.00  
% 19.74/3.00  
% 19.74/3.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.74/3.00  
% 19.74/3.00  ------ Proving...
% 19.74/3.00  
% 19.74/3.00  
% 19.74/3.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.74/3.00  
% 19.74/3.00  ------ Proving...
% 19.74/3.00  
% 19.74/3.00  
% 19.74/3.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.74/3.00  
% 19.74/3.00  ------ Proving...
% 19.74/3.00  
% 19.74/3.00  
% 19.74/3.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.74/3.00  
% 19.74/3.00  ------ Proving...
% 19.74/3.00  
% 19.74/3.00  
% 19.74/3.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.74/3.00  
% 19.74/3.00  ------ Proving...
% 19.74/3.00  
% 19.74/3.00  
% 19.74/3.00  % SZS status CounterSatisfiable for theBenchmark.p
% 19.74/3.00  
% 19.74/3.00  ------ Building Model...Done
% 19.74/3.00  
% 19.74/3.00  %------ The model is defined over ground terms (initial term algebra).
% 19.74/3.00  %------ Predicates are defined as (\forall x_1,..,x_n  ((~)P(x_1,..,x_n) <=> (\phi(x_1,..,x_n)))) 
% 19.74/3.00  %------ where \phi is a formula over the term algebra.
% 19.74/3.00  %------ If we have equality in the problem then it is also defined as a predicate above, 
% 19.74/3.00  %------ with "=" on the right-hand-side of the definition interpreted over the term algebra term_algebra_type
% 19.74/3.00  %------ See help for --sat_out_model for different model outputs.
% 19.74/3.00  %------ equality_sorted(X0,X1,X2) can be used in the place of usual "="
% 19.74/3.00  %------ where the first argument stands for the sort ($i in the unsorted case)
% 19.74/3.00  % SZS output start Model for theBenchmark.p
% 19.74/3.00  
% 19.74/3.00  %------ Positive definition of equality_sorted 
% 19.74/3.00  fof(lit_def,axiom,
% 19.74/3.00      (! [X0_0,X0_2,X1_2] : 
% 19.74/3.00        ( equality_sorted(X0_0,X0_2,X1_2) <=>
% 19.74/3.00             (
% 19.74/3.00                (
% 19.74/3.00                  ( X0_0=$o & X1_2=X0_2 )
% 19.74/3.00                )
% 19.74/3.00  
% 19.74/3.00               | 
% 19.74/3.00                (
% 19.74/3.00                  ( X0_0=$i )
% 19.74/3.00                 &
% 19.74/3.00                  ( X0!=sK2 | X1!=k1_struct_0(X1) )
% 19.74/3.00                 &
% 19.74/3.00                  ( X0!=k1_struct_0(sK1) )
% 19.74/3.00                 &
% 19.74/3.00                  ( X0!=k1_struct_0(sK1) | X1!=sK2 )
% 19.74/3.00                 &
% 19.74/3.00                  ( X0!=k1_struct_0(sK1) | X1!=sK0(sK0(sK0(sK0(k1_struct_0(X1))))) )
% 19.74/3.00                 &
% 19.74/3.00                  ( X0!=k1_struct_0(X0) )
% 19.74/3.00                 &
% 19.74/3.00                  ( X0!=k1_struct_0(X0) | X1!=sK0(sK0(sK0(sK0(k1_struct_0(X1))))) )
% 19.74/3.00                 &
% 19.74/3.00                  ( X0!=arAF0_k4_mcart_1_0 )
% 19.74/3.00                 &
% 19.74/3.00                  ( X0!=arAF0_k4_mcart_1_0 | X1!=sK0(k1_struct_0(X1)) )
% 19.74/3.00                 &
% 19.74/3.00                  ( X0!=arAF0_k4_mcart_1_0 | X1!=sK0(sK0(k1_struct_0(X1))) )
% 19.74/3.00                 &
% 19.74/3.00                  ( X0!=arAF0_k4_mcart_1_0 | X1!=sK0(sK0(sK0(k1_struct_0(X1)))) )
% 19.74/3.00                 &
% 19.74/3.00                  ( X0!=arAF0_k4_mcart_1_0 | X1!=sK0(sK0(sK0(sK0(k1_struct_0(X1))))) )
% 19.74/3.00                 &
% 19.74/3.00                  ( X0!=sK0(k1_struct_0(X0)) )
% 19.74/3.00                 &
% 19.74/3.00                  ( X0!=sK0(k1_struct_0(X0)) | X1!=sK0(sK0(sK0(sK0(k1_struct_0(X1))))) )
% 19.74/3.00                 &
% 19.74/3.00                  ( X0!=sK0(sK0(k1_struct_0(X0))) )
% 19.74/3.00                 &
% 19.74/3.00                  ( X0!=sK0(sK0(k1_struct_0(X0))) | X1!=sK0(sK0(sK0(sK0(k1_struct_0(X1))))) )
% 19.74/3.00                 &
% 19.74/3.00                  ( X0!=sK0(sK0(sK0(k1_struct_0(X0)))) )
% 19.74/3.00                 &
% 19.74/3.00                  ( X0!=sK0(sK0(sK0(k1_struct_0(X0)))) | X1!=sK0(sK0(sK0(sK0(k1_struct_0(X1))))) )
% 19.74/3.00                 &
% 19.74/3.00                  ( X0!=sK0(sK0(sK0(sK0(k1_struct_0(X0))))) )
% 19.74/3.00                 &
% 19.74/3.00                  ( X0!=sK0(sK0(sK0(sK0(k1_struct_0(X0))))) | X1!=k1_struct_0(X1) )
% 19.74/3.00                 &
% 19.74/3.00                  ( X0!=sK0(sK0(sK0(sK0(k1_struct_0(X0))))) | X1!=sK0(k1_struct_0(X1)) )
% 19.74/3.00                 &
% 19.74/3.00                  ( X0!=sK0(sK0(sK0(sK0(k1_struct_0(X0))))) | X1!=sK0(sK0(k1_struct_0(X1))) )
% 19.74/3.00                 &
% 19.74/3.00                  ( X0!=sK0(sK0(sK0(sK0(k1_struct_0(X0))))) | X1!=sK0(sK0(sK0(k1_struct_0(X1)))) )
% 19.74/3.00                 &
% 19.74/3.00                  ( X0!=sK0(sK0(sK0(sK0(k1_struct_0(X2))))) | X1!=arAF0_k4_mcart_1_0 )
% 19.74/3.00                 &
% 19.74/3.00                  ( X1!=k1_struct_0(X1) )
% 19.74/3.00                 &
% 19.74/3.00                  ( X1!=arAF0_k4_mcart_1_0 )
% 19.74/3.00                 &
% 19.74/3.00                  ( X1!=sK0(k1_struct_0(X1)) )
% 19.74/3.00                 &
% 19.74/3.00                  ( X1!=sK0(sK0(k1_struct_0(X1))) )
% 19.74/3.00                 &
% 19.74/3.00                  ( X1!=sK0(sK0(sK0(k1_struct_0(X1)))) )
% 19.74/3.00                 &
% 19.74/3.00                  ( X1!=sK0(sK0(sK0(sK0(k1_struct_0(X1))))) )
% 19.74/3.00                )
% 19.74/3.00  
% 19.74/3.00               | 
% 19.74/3.00                (
% 19.74/3.00                  ( X0_0=$i & X0=k1_xboole_0 )
% 19.74/3.00                 &
% 19.74/3.00                  ( X1!=k1_struct_0(X1) )
% 19.74/3.00                 &
% 19.74/3.00                  ( X1!=arAF0_k4_mcart_1_0 )
% 19.74/3.00                 &
% 19.74/3.00                  ( X1!=sK0(k1_struct_0(X1)) )
% 19.74/3.00                 &
% 19.74/3.00                  ( X1!=sK0(sK0(k1_struct_0(X1))) )
% 19.74/3.00                 &
% 19.74/3.00                  ( X1!=sK0(sK0(sK0(k1_struct_0(X1)))) )
% 19.74/3.00                 &
% 19.74/3.00                  ( X1!=sK0(sK0(sK0(sK0(k1_struct_0(X1))))) )
% 19.74/3.00                )
% 19.74/3.00  
% 19.74/3.00               | 
% 19.74/3.00              ? [X2] : 
% 19.74/3.00                (
% 19.74/3.00                  ( X0_0=$i & X0=k1_xboole_0 & X1=sK0(sK0(sK0(sK0(k1_struct_0(X2))))) )
% 19.74/3.00                )
% 19.74/3.00  
% 19.74/3.00               | 
% 19.74/3.00              ? [X2] : 
% 19.74/3.00                (
% 19.74/3.00                  ( X0_0=$i & X0=k1_struct_0(sK1) & X1=k1_struct_0(X2) )
% 19.74/3.00                )
% 19.74/3.00  
% 19.74/3.00               | 
% 19.74/3.00              ? [X2] : 
% 19.74/3.00                (
% 19.74/3.00                  ( X0_0=$i & X0=k1_struct_0(X2) & X1=k1_struct_0(sK1) )
% 19.74/3.00                 &
% 19.74/3.00                  ( X2!=sK1 )
% 19.74/3.00                )
% 19.74/3.00  
% 19.74/3.00               | 
% 19.74/3.00              ? [X2,X3] : 
% 19.74/3.00                (
% 19.74/3.00                  ( X0_0=$i & X0=k1_struct_0(X2) & X1=k1_struct_0(X3) )
% 19.74/3.00                )
% 19.74/3.00  
% 19.74/3.00               | 
% 19.74/3.00              ? [X2] : 
% 19.74/3.00                (
% 19.74/3.00                  ( X0_0=$i & X0=sK0(sK0(sK0(sK0(k1_struct_0(X2))))) )
% 19.74/3.00                 &
% 19.74/3.00                  ( X1!=k1_struct_0(sK1) )
% 19.74/3.00                 &
% 19.74/3.00                  ( X1!=k1_struct_0(X1) )
% 19.74/3.00                 &
% 19.74/3.00                  ( X1!=arAF0_k4_mcart_1_0 )
% 19.74/3.00                 &
% 19.74/3.00                  ( X1!=sK0(k1_struct_0(X1)) )
% 19.74/3.00                 &
% 19.74/3.00                  ( X1!=sK0(sK0(k1_struct_0(X1))) )
% 19.74/3.00                 &
% 19.74/3.00                  ( X1!=sK0(sK0(sK0(k1_struct_0(X1)))) )
% 19.74/3.00                )
% 19.74/3.00  
% 19.74/3.00               | 
% 19.74/3.00                (
% 19.74/3.00                  ( X0_0=$i & X1=X0 )
% 19.74/3.00                )
% 19.74/3.00  
% 19.74/3.00               | 
% 19.74/3.00              ? [X2] : 
% 19.74/3.00                (
% 19.74/3.00                  ( X0_0=$i & X1=sK0(sK0(sK0(sK0(k1_struct_0(X2))))) )
% 19.74/3.00                 &
% 19.74/3.00                  ( X0!=k1_struct_0(sK1) )
% 19.74/3.00                 &
% 19.74/3.00                  ( X0!=k1_struct_0(X0) )
% 19.74/3.00                 &
% 19.74/3.00                  ( X0!=arAF0_k4_mcart_1_0 )
% 19.74/3.00                 &
% 19.74/3.00                  ( X0!=sK0(k1_struct_0(X0)) )
% 19.74/3.00                 &
% 19.74/3.00                  ( X0!=sK0(sK0(k1_struct_0(X0))) )
% 19.74/3.00                 &
% 19.74/3.00                  ( X0!=sK0(sK0(sK0(k1_struct_0(X0)))) )
% 19.74/3.00                )
% 19.74/3.00  
% 19.74/3.00             )
% 19.74/3.00        )
% 19.74/3.00      )
% 19.74/3.00     ).
% 19.74/3.00  
% 19.74/3.00  %------ Positive definition of r2_hidden 
% 19.74/3.00  fof(lit_def,axiom,
% 19.74/3.00      (! [X0,X1] : 
% 19.74/3.00        ( r2_hidden(X0,X1) <=>
% 19.74/3.00             (
% 19.74/3.00              ? [X2] : 
% 19.74/3.00                (
% 19.74/3.00                  ( X0=k1_xboole_0 & X1=sK0(sK0(k1_struct_0(X2))) )
% 19.74/3.00                )
% 19.74/3.00  
% 19.74/3.00               | 
% 19.74/3.00              ? [X2] : 
% 19.74/3.00                (
% 19.74/3.00                  ( X0=k1_xboole_0 & X1=sK0(sK0(sK0(k1_struct_0(X2)))) )
% 19.74/3.00                )
% 19.74/3.00  
% 19.74/3.00               | 
% 19.74/3.00              ? [X2] : 
% 19.74/3.00                (
% 19.74/3.00                  ( X0=sK0(k1_struct_0(X2)) & X1=k1_struct_0(X2) )
% 19.74/3.00                )
% 19.74/3.00  
% 19.74/3.00               | 
% 19.74/3.00              ? [X2,X3] : 
% 19.74/3.00                (
% 19.74/3.00                  ( X0=sK0(k1_struct_0(X2)) & X1=k1_struct_0(X3) )
% 19.74/3.00                )
% 19.74/3.00  
% 19.74/3.00               | 
% 19.74/3.00                (
% 19.74/3.00                  ( X0=sK0(arAF0_k4_mcart_1_0) & X1=arAF0_k4_mcart_1_0 )
% 19.74/3.00                )
% 19.74/3.00  
% 19.74/3.00               | 
% 19.74/3.00              ? [X2] : 
% 19.74/3.00                (
% 19.74/3.00                  ( X0=sK0(sK0(k1_struct_0(X2))) & X1=sK0(k1_struct_0(X2)) )
% 19.74/3.00                )
% 19.74/3.00  
% 19.74/3.00               | 
% 19.74/3.00              ? [X2] : 
% 19.74/3.00                (
% 19.74/3.00                  ( X0=sK0(sK0(sK0(k1_struct_0(X2)))) & X1=sK0(sK0(k1_struct_0(X2))) )
% 19.74/3.00                )
% 19.74/3.00  
% 19.74/3.00               | 
% 19.74/3.00              ? [X2] : 
% 19.74/3.00                (
% 19.74/3.00                  ( X0=sK0(sK0(sK0(sK0(k1_struct_0(X2))))) & X1=arAF0_k4_mcart_1_0 )
% 19.74/3.00                )
% 19.74/3.00  
% 19.74/3.00               | 
% 19.74/3.00              ? [X2,X3] : 
% 19.74/3.00                (
% 19.74/3.00                  ( X0=sK0(sK0(sK0(sK0(k1_struct_0(X2))))) & X1=sK0(k1_struct_0(X3)) )
% 19.74/3.00                )
% 19.74/3.00  
% 19.74/3.00               | 
% 19.74/3.00              ? [X2] : 
% 19.74/3.00                (
% 19.74/3.00                  ( X0=sK0(sK0(sK0(sK0(k1_struct_0(X2))))) & X1=sK0(sK0(sK0(k1_struct_0(X2)))) )
% 19.74/3.00                )
% 19.74/3.00  
% 19.74/3.00               | 
% 19.74/3.00              ? [X2,X3] : 
% 19.74/3.00                (
% 19.74/3.00                  ( X0=sK0(sK0(sK0(sK0(k1_struct_0(X2))))) & X1=sK0(sK0(k1_struct_0(X3))) )
% 19.74/3.00                )
% 19.74/3.00  
% 19.74/3.00               | 
% 19.74/3.00                (
% 19.74/3.00                  ( X1=arAF0_k4_mcart_1_0 )
% 19.74/3.00                 &
% 19.74/3.00                  ( X0!=k1_struct_0(X0) )
% 19.74/3.00                 &
% 19.74/3.00                  ( X0!=arAF0_k4_mcart_1_0 )
% 19.74/3.00                 &
% 19.74/3.00                  ( X0!=sK0(k1_struct_0(X0)) )
% 19.74/3.00                 &
% 19.74/3.00                  ( X0!=sK0(sK0(k1_struct_0(X0))) )
% 19.74/3.00                 &
% 19.74/3.00                  ( X0!=sK0(sK0(sK0(k1_struct_0(X0)))) )
% 19.74/3.00                 &
% 19.74/3.00                  ( X0!=sK0(sK0(sK0(sK0(k1_struct_0(X0))))) )
% 19.74/3.00                )
% 19.74/3.00  
% 19.74/3.00               | 
% 19.74/3.00              ? [X2] : 
% 19.74/3.00                (
% 19.74/3.00                  ( X1=sK0(k1_struct_0(X2)) )
% 19.74/3.00                 &
% 19.74/3.00                  ( X0!=k1_struct_0(X0) )
% 19.74/3.00                 &
% 19.74/3.00                  ( X0!=arAF0_k4_mcart_1_0 )
% 19.74/3.00                 &
% 19.74/3.00                  ( X0!=sK0(k1_struct_0(X0)) )
% 19.74/3.00                 &
% 19.74/3.00                  ( X0!=sK0(sK0(sK0(k1_struct_0(X0)))) )
% 19.74/3.00                 &
% 19.74/3.00                  ( X0!=sK0(sK0(sK0(sK0(k1_struct_0(X0))))) )
% 19.74/3.00                )
% 19.74/3.00  
% 19.74/3.00               | 
% 19.74/3.00              ? [X2] : 
% 19.74/3.00                (
% 19.74/3.00                  ( X1=sK0(sK0(k1_struct_0(X2))) )
% 19.74/3.00                 &
% 19.74/3.00                  ( X0!=k1_struct_0(X0) )
% 19.74/3.00                 &
% 19.74/3.00                  ( X0!=arAF0_k4_mcart_1_0 )
% 19.74/3.00                 &
% 19.74/3.00                  ( X0!=sK0(k1_struct_0(X0)) )
% 19.74/3.00                 &
% 19.74/3.00                  ( X0!=sK0(sK0(k1_struct_0(X0))) )
% 19.74/3.00                 &
% 19.74/3.00                  ( X0!=sK0(sK0(sK0(sK0(k1_struct_0(X0))))) )
% 19.74/3.00                )
% 19.74/3.00  
% 19.74/3.00               | 
% 19.74/3.00              ? [X2] : 
% 19.74/3.00                (
% 19.74/3.00                  ( X1=sK0(sK0(sK0(k1_struct_0(X2)))) )
% 19.74/3.00                 &
% 19.74/3.00                  ( X0!=k1_xboole_0 )
% 19.74/3.00                 &
% 19.74/3.00                  ( X0!=k1_struct_0(X0) )
% 19.74/3.00                 &
% 19.74/3.00                  ( X0!=arAF0_k4_mcart_1_0 )
% 19.74/3.00                 &
% 19.74/3.00                  ( X0!=sK0(k1_struct_0(X0)) )
% 19.74/3.00                 &
% 19.74/3.00                  ( X0!=sK0(sK0(k1_struct_0(X0))) )
% 19.74/3.00                 &
% 19.74/3.00                  ( X0!=sK0(sK0(sK0(k1_struct_0(X0)))) )
% 19.74/3.00                 &
% 19.74/3.00                  ( X0!=sK0(sK0(sK0(sK0(k1_struct_0(X0))))) | X2!=X0 )
% 19.74/3.00                )
% 19.74/3.00  
% 19.74/3.00             )
% 19.74/3.00        )
% 19.74/3.00      )
% 19.74/3.00     ).
% 19.74/3.00  
% 19.74/3.00  %------ Negative definition of m1_subset_1 
% 19.74/3.00  fof(lit_def,axiom,
% 19.74/3.00      (! [X0,X1] : 
% 19.74/3.00        ( ~(m1_subset_1(X0,X1)) <=>
% 19.74/3.00             (
% 19.74/3.00                (
% 19.74/3.00                  ( X0=arAF0_k4_mcart_1_0 )
% 19.74/3.00                )
% 19.74/3.00  
% 19.74/3.00               | 
% 19.74/3.00                (
% 19.74/3.00                  ( X0=arAF0_k4_mcart_1_0 & X1=arAF0_k1_zfmisc_1_0 )
% 19.74/3.00                )
% 19.74/3.00  
% 19.74/3.00               | 
% 19.74/3.00              ? [X2] : 
% 19.74/3.00                (
% 19.74/3.00                  ( X0=k1_struct_0(X2) )
% 19.74/3.00                )
% 19.74/3.00  
% 19.74/3.00               | 
% 19.74/3.00              ? [X2] : 
% 19.74/3.00                (
% 19.74/3.00                  ( X0=k1_struct_0(X2) & X1=arAF0_k1_zfmisc_1_0 )
% 19.74/3.00                )
% 19.74/3.00  
% 19.74/3.00               | 
% 19.74/3.00              ? [X2] : 
% 19.74/3.00                (
% 19.74/3.00                  ( X0=sK0(k1_struct_0(X2)) )
% 19.74/3.00                 &
% 19.74/3.00                  ( X1!=k1_struct_0(X1) )
% 19.74/3.00                 &
% 19.74/3.00                  ( X1!=k1_struct_0(X2) | X2!=X2 )
% 19.74/3.00                )
% 19.74/3.00  
% 19.74/3.00               | 
% 19.74/3.00              ? [X2] : 
% 19.74/3.00                (
% 19.74/3.00                  ( X0=sK0(k1_struct_0(X2)) & X1=arAF0_k1_zfmisc_1_0 )
% 19.74/3.00                )
% 19.74/3.00  
% 19.74/3.00               | 
% 19.74/3.00              ? [X2] : 
% 19.74/3.00                (
% 19.74/3.00                  ( X0=sK0(sK0(k1_struct_0(X2))) )
% 19.74/3.00                 &
% 19.74/3.00                  ( X1!=sK0(k1_struct_0(X2)) | X2!=X2 )
% 19.74/3.00                 &
% 19.74/3.00                  ( X1!=sK0(k1_struct_0(X1)) )
% 19.74/3.00                )
% 19.74/3.00  
% 19.74/3.00               | 
% 19.74/3.00              ? [X2] : 
% 19.74/3.00                (
% 19.74/3.00                  ( X0=sK0(sK0(k1_struct_0(X2))) & X1=arAF0_k1_zfmisc_1_0 )
% 19.74/3.00                )
% 19.74/3.00  
% 19.74/3.00               | 
% 19.74/3.00              ? [X2] : 
% 19.74/3.00                (
% 19.74/3.00                  ( X0=sK0(sK0(sK0(k1_struct_0(X2)))) )
% 19.74/3.00                 &
% 19.74/3.00                  ( X1!=sK0(sK0(k1_struct_0(X1))) )
% 19.74/3.00                 &
% 19.74/3.00                  ( X1!=sK0(sK0(k1_struct_0(X2))) | X2!=X2 )
% 19.74/3.00                )
% 19.74/3.00  
% 19.74/3.00               | 
% 19.74/3.00              ? [X2] : 
% 19.74/3.00                (
% 19.74/3.00                  ( X0=sK0(sK0(sK0(k1_struct_0(X2)))) & X1=arAF0_k1_zfmisc_1_0 )
% 19.74/3.00                )
% 19.74/3.00  
% 19.74/3.00             )
% 19.74/3.00        )
% 19.74/3.00      )
% 19.74/3.00     ).
% 19.74/3.00  % SZS output end Model for theBenchmark.p
% 19.74/3.00  ------                               Statistics
% 19.74/3.00  
% 19.74/3.00  ------ Selected
% 19.74/3.00  
% 19.74/3.00  total_time:                             2.174
% 19.74/3.00  
%------------------------------------------------------------------------------
