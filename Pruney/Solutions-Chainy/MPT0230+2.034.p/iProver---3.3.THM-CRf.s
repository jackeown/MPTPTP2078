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
% DateTime   : Thu Dec  3 11:30:46 EST 2020

% Result     : Theorem 15.29s
% Output     : CNFRefutation 15.29s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 125 expanded)
%              Number of clauses        :   28 (  29 expanded)
%              Number of leaves         :   14 (  33 expanded)
%              Depth                    :   14
%              Number of atoms          :  216 ( 381 expanded)
%              Number of equality atoms :  168 ( 299 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f87,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k2_enumset1(X2,X2,X1,X0) ),
    inference(definition_unfolding,[],[f55,f59,f59])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f68,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f58,f59])).

fof(f69,plain,(
    ! [X0] : k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0) ),
    inference(definition_unfolding,[],[f57,f68])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k2_enumset1(X0,X0,X1,X2),k2_enumset1(X3,X3,X3,X3)) = k2_enumset1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f56,f59,f69])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f18,conjecture,(
    ! [X0,X1,X2] :
      ~ ( X0 != X2
        & X0 != X1
        & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( X0 != X2
          & X0 != X1
          & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( X0 != X2
      & X0 != X1
      & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f34,plain,
    ( ? [X0,X1,X2] :
        ( X0 != X2
        & X0 != X1
        & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) )
   => ( sK2 != sK4
      & sK2 != sK3
      & r1_tarski(k1_tarski(sK2),k2_tarski(sK3,sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( sK2 != sK4
    & sK2 != sK3
    & r1_tarski(k1_tarski(sK2),k2_tarski(sK3,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f23,f34])).

fof(f65,plain,(
    r1_tarski(k1_tarski(sK2),k2_tarski(sK3,sK4)) ),
    inference(cnf_transformation,[],[f35])).

fof(f90,plain,(
    r1_tarski(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK3,sK3,sK3,sK4)) ),
    inference(definition_unfolding,[],[f65,f69,f68])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f37,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f20])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(flattening,[],[f24])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(rectify,[],[f25])).

fof(f27,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ( X2 != X4
              & X1 != X4
              & X0 != X4 )
            | ~ r2_hidden(X4,X3) )
          & ( X2 = X4
            | X1 = X4
            | X0 = X4
            | r2_hidden(X4,X3) ) )
     => ( ( ( sK0(X0,X1,X2,X3) != X2
            & sK0(X0,X1,X2,X3) != X1
            & sK0(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK0(X0,X1,X2,X3),X3) )
        & ( sK0(X0,X1,X2,X3) = X2
          | sK0(X0,X1,X2,X3) = X1
          | sK0(X0,X1,X2,X3) = X0
          | r2_hidden(sK0(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK0(X0,X1,X2,X3) != X2
              & sK0(X0,X1,X2,X3) != X1
              & sK0(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK0(X0,X1,X2,X3),X3) )
          & ( sK0(X0,X1,X2,X3) = X2
            | sK0(X0,X1,X2,X3) = X1
            | sK0(X0,X1,X2,X3) = X0
            | r2_hidden(sK0(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).

fof(f44,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f77,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f44,f59])).

fof(f91,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k2_enumset1(X0,X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f77])).

fof(f92,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k2_enumset1(X0,X0,X1,X5)) ),
    inference(equality_resolution,[],[f91])).

fof(f41,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f80,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f41,f59])).

fof(f97,plain,(
    ! [X2,X0,X5,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,k2_enumset1(X0,X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f80])).

fof(f67,plain,(
    sK2 != sK4 ),
    inference(cnf_transformation,[],[f35])).

fof(f66,plain,(
    sK2 != sK3 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_20,plain,
    ( k2_enumset1(X0,X0,X1,X2) = k2_enumset1(X2,X2,X1,X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_0,plain,
    ( k2_xboole_0(k2_enumset1(X0,X0,X1,X2),k2_enumset1(X3,X3,X3,X3)) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_3891,plain,
    ( k2_xboole_0(k2_enumset1(X0,X0,X1,X2),k2_enumset1(X3,X3,X3,X3)) = k2_enumset1(X2,X1,X0,X3) ),
    inference(superposition,[status(thm)],[c_20,c_0])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_25,negated_conjecture,
    ( r1_tarski(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK3,sK3,sK3,sK4)) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_184,plain,
    ( k2_enumset1(sK3,sK3,sK3,sK4) != X0
    | k2_enumset1(sK2,sK2,sK2,sK2) != X1
    | k3_xboole_0(X1,X0) = X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_25])).

cnf(c_185,plain,
    ( k3_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK3,sK3,sK3,sK4)) = k2_enumset1(sK2,sK2,sK2,sK2) ),
    inference(unflattening,[status(thm)],[c_184])).

cnf(c_2198,plain,
    ( k3_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK4,sK4,sK3,sK3)) = k2_enumset1(sK2,sK2,sK2,sK2) ),
    inference(demodulation,[status(thm)],[c_20,c_185])).

cnf(c_1,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_2,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_4,plain,
    ( k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_2356,plain,
    ( k3_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_2,c_4])).

cnf(c_3,plain,
    ( k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_2374,plain,
    ( k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_2356,c_3])).

cnf(c_3925,plain,
    ( k2_xboole_0(X0,k3_xboole_0(X1,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_1,c_2374])).

cnf(c_4117,plain,
    ( k2_xboole_0(k2_enumset1(sK4,sK4,sK3,sK3),k2_enumset1(sK2,sK2,sK2,sK2)) = k2_enumset1(sK4,sK4,sK3,sK3) ),
    inference(superposition,[status(thm)],[c_2198,c_3925])).

cnf(c_39742,plain,
    ( k2_enumset1(sK4,sK4,sK3,sK3) = k2_enumset1(sK3,sK3,sK4,sK2) ),
    inference(superposition,[status(thm)],[c_3891,c_4117])).

cnf(c_10,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X2,X0)) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1839,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X2,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_41212,plain,
    ( r2_hidden(sK2,k2_enumset1(sK4,sK4,sK3,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_39742,c_1839])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X2,X3))
    | X0 = X1
    | X0 = X2
    | X0 = X3 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1992,plain,
    ( ~ r2_hidden(sK2,k2_enumset1(sK4,sK4,X0,X1))
    | sK2 = X0
    | sK2 = X1
    | sK2 = sK4 ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_2033,plain,
    ( ~ r2_hidden(sK2,k2_enumset1(sK4,sK4,sK3,X0))
    | sK2 = X0
    | sK2 = sK3
    | sK2 = sK4 ),
    inference(instantiation,[status(thm)],[c_1992])).

cnf(c_2153,plain,
    ( ~ r2_hidden(sK2,k2_enumset1(sK4,sK4,sK3,sK3))
    | sK2 = sK3
    | sK2 = sK4 ),
    inference(instantiation,[status(thm)],[c_2033])).

cnf(c_2154,plain,
    ( sK2 = sK3
    | sK2 = sK4
    | r2_hidden(sK2,k2_enumset1(sK4,sK4,sK3,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2153])).

cnf(c_23,negated_conjecture,
    ( sK2 != sK4 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_24,negated_conjecture,
    ( sK2 != sK3 ),
    inference(cnf_transformation,[],[f66])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_41212,c_2154,c_23,c_24])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:31:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 15.29/2.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.29/2.49  
% 15.29/2.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.29/2.49  
% 15.29/2.49  ------  iProver source info
% 15.29/2.49  
% 15.29/2.49  git: date: 2020-06-30 10:37:57 +0100
% 15.29/2.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.29/2.49  git: non_committed_changes: false
% 15.29/2.49  git: last_make_outside_of_git: false
% 15.29/2.49  
% 15.29/2.49  ------ 
% 15.29/2.49  
% 15.29/2.49  ------ Input Options
% 15.29/2.49  
% 15.29/2.49  --out_options                           all
% 15.29/2.49  --tptp_safe_out                         true
% 15.29/2.49  --problem_path                          ""
% 15.29/2.49  --include_path                          ""
% 15.29/2.49  --clausifier                            res/vclausify_rel
% 15.29/2.49  --clausifier_options                    --mode clausify
% 15.29/2.49  --stdin                                 false
% 15.29/2.49  --stats_out                             all
% 15.29/2.49  
% 15.29/2.49  ------ General Options
% 15.29/2.49  
% 15.29/2.49  --fof                                   false
% 15.29/2.49  --time_out_real                         305.
% 15.29/2.49  --time_out_virtual                      -1.
% 15.29/2.49  --symbol_type_check                     false
% 15.29/2.49  --clausify_out                          false
% 15.29/2.49  --sig_cnt_out                           false
% 15.29/2.49  --trig_cnt_out                          false
% 15.29/2.49  --trig_cnt_out_tolerance                1.
% 15.29/2.49  --trig_cnt_out_sk_spl                   false
% 15.29/2.49  --abstr_cl_out                          false
% 15.29/2.49  
% 15.29/2.49  ------ Global Options
% 15.29/2.49  
% 15.29/2.49  --schedule                              default
% 15.29/2.49  --add_important_lit                     false
% 15.29/2.49  --prop_solver_per_cl                    1000
% 15.29/2.49  --min_unsat_core                        false
% 15.29/2.49  --soft_assumptions                      false
% 15.29/2.49  --soft_lemma_size                       3
% 15.29/2.49  --prop_impl_unit_size                   0
% 15.29/2.49  --prop_impl_unit                        []
% 15.29/2.49  --share_sel_clauses                     true
% 15.29/2.49  --reset_solvers                         false
% 15.29/2.49  --bc_imp_inh                            [conj_cone]
% 15.29/2.49  --conj_cone_tolerance                   3.
% 15.29/2.49  --extra_neg_conj                        none
% 15.29/2.49  --large_theory_mode                     true
% 15.29/2.49  --prolific_symb_bound                   200
% 15.29/2.49  --lt_threshold                          2000
% 15.29/2.49  --clause_weak_htbl                      true
% 15.29/2.49  --gc_record_bc_elim                     false
% 15.29/2.49  
% 15.29/2.49  ------ Preprocessing Options
% 15.29/2.49  
% 15.29/2.49  --preprocessing_flag                    true
% 15.29/2.49  --time_out_prep_mult                    0.1
% 15.29/2.49  --splitting_mode                        input
% 15.29/2.49  --splitting_grd                         true
% 15.29/2.49  --splitting_cvd                         false
% 15.29/2.49  --splitting_cvd_svl                     false
% 15.29/2.49  --splitting_nvd                         32
% 15.29/2.49  --sub_typing                            true
% 15.29/2.49  --prep_gs_sim                           true
% 15.29/2.49  --prep_unflatten                        true
% 15.29/2.49  --prep_res_sim                          true
% 15.29/2.49  --prep_upred                            true
% 15.29/2.49  --prep_sem_filter                       exhaustive
% 15.29/2.49  --prep_sem_filter_out                   false
% 15.29/2.49  --pred_elim                             true
% 15.29/2.49  --res_sim_input                         true
% 15.29/2.49  --eq_ax_congr_red                       true
% 15.29/2.49  --pure_diseq_elim                       true
% 15.29/2.49  --brand_transform                       false
% 15.29/2.49  --non_eq_to_eq                          false
% 15.29/2.49  --prep_def_merge                        true
% 15.29/2.49  --prep_def_merge_prop_impl              false
% 15.29/2.49  --prep_def_merge_mbd                    true
% 15.29/2.49  --prep_def_merge_tr_red                 false
% 15.29/2.49  --prep_def_merge_tr_cl                  false
% 15.29/2.49  --smt_preprocessing                     true
% 15.29/2.49  --smt_ac_axioms                         fast
% 15.29/2.49  --preprocessed_out                      false
% 15.29/2.49  --preprocessed_stats                    false
% 15.29/2.49  
% 15.29/2.49  ------ Abstraction refinement Options
% 15.29/2.49  
% 15.29/2.49  --abstr_ref                             []
% 15.29/2.49  --abstr_ref_prep                        false
% 15.29/2.49  --abstr_ref_until_sat                   false
% 15.29/2.49  --abstr_ref_sig_restrict                funpre
% 15.29/2.49  --abstr_ref_af_restrict_to_split_sk     false
% 15.29/2.49  --abstr_ref_under                       []
% 15.29/2.49  
% 15.29/2.49  ------ SAT Options
% 15.29/2.49  
% 15.29/2.49  --sat_mode                              false
% 15.29/2.49  --sat_fm_restart_options                ""
% 15.29/2.49  --sat_gr_def                            false
% 15.29/2.49  --sat_epr_types                         true
% 15.29/2.49  --sat_non_cyclic_types                  false
% 15.29/2.49  --sat_finite_models                     false
% 15.29/2.49  --sat_fm_lemmas                         false
% 15.29/2.49  --sat_fm_prep                           false
% 15.29/2.49  --sat_fm_uc_incr                        true
% 15.29/2.49  --sat_out_model                         small
% 15.29/2.49  --sat_out_clauses                       false
% 15.29/2.49  
% 15.29/2.49  ------ QBF Options
% 15.29/2.49  
% 15.29/2.49  --qbf_mode                              false
% 15.29/2.49  --qbf_elim_univ                         false
% 15.29/2.49  --qbf_dom_inst                          none
% 15.29/2.49  --qbf_dom_pre_inst                      false
% 15.29/2.49  --qbf_sk_in                             false
% 15.29/2.49  --qbf_pred_elim                         true
% 15.29/2.49  --qbf_split                             512
% 15.29/2.49  
% 15.29/2.49  ------ BMC1 Options
% 15.29/2.49  
% 15.29/2.49  --bmc1_incremental                      false
% 15.29/2.49  --bmc1_axioms                           reachable_all
% 15.29/2.49  --bmc1_min_bound                        0
% 15.29/2.49  --bmc1_max_bound                        -1
% 15.29/2.49  --bmc1_max_bound_default                -1
% 15.29/2.49  --bmc1_symbol_reachability              true
% 15.29/2.49  --bmc1_property_lemmas                  false
% 15.29/2.49  --bmc1_k_induction                      false
% 15.29/2.49  --bmc1_non_equiv_states                 false
% 15.29/2.49  --bmc1_deadlock                         false
% 15.29/2.49  --bmc1_ucm                              false
% 15.29/2.49  --bmc1_add_unsat_core                   none
% 15.29/2.49  --bmc1_unsat_core_children              false
% 15.29/2.49  --bmc1_unsat_core_extrapolate_axioms    false
% 15.29/2.49  --bmc1_out_stat                         full
% 15.29/2.49  --bmc1_ground_init                      false
% 15.29/2.49  --bmc1_pre_inst_next_state              false
% 15.29/2.49  --bmc1_pre_inst_state                   false
% 15.29/2.49  --bmc1_pre_inst_reach_state             false
% 15.29/2.49  --bmc1_out_unsat_core                   false
% 15.29/2.49  --bmc1_aig_witness_out                  false
% 15.29/2.49  --bmc1_verbose                          false
% 15.29/2.49  --bmc1_dump_clauses_tptp                false
% 15.29/2.49  --bmc1_dump_unsat_core_tptp             false
% 15.29/2.49  --bmc1_dump_file                        -
% 15.29/2.49  --bmc1_ucm_expand_uc_limit              128
% 15.29/2.49  --bmc1_ucm_n_expand_iterations          6
% 15.29/2.49  --bmc1_ucm_extend_mode                  1
% 15.29/2.49  --bmc1_ucm_init_mode                    2
% 15.29/2.49  --bmc1_ucm_cone_mode                    none
% 15.29/2.49  --bmc1_ucm_reduced_relation_type        0
% 15.29/2.49  --bmc1_ucm_relax_model                  4
% 15.29/2.49  --bmc1_ucm_full_tr_after_sat            true
% 15.29/2.49  --bmc1_ucm_expand_neg_assumptions       false
% 15.29/2.49  --bmc1_ucm_layered_model                none
% 15.29/2.49  --bmc1_ucm_max_lemma_size               10
% 15.29/2.49  
% 15.29/2.49  ------ AIG Options
% 15.29/2.49  
% 15.29/2.49  --aig_mode                              false
% 15.29/2.49  
% 15.29/2.49  ------ Instantiation Options
% 15.29/2.49  
% 15.29/2.49  --instantiation_flag                    true
% 15.29/2.49  --inst_sos_flag                         false
% 15.29/2.49  --inst_sos_phase                        true
% 15.29/2.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.29/2.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.29/2.49  --inst_lit_sel_side                     num_symb
% 15.29/2.49  --inst_solver_per_active                1400
% 15.29/2.49  --inst_solver_calls_frac                1.
% 15.29/2.49  --inst_passive_queue_type               priority_queues
% 15.29/2.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.29/2.49  --inst_passive_queues_freq              [25;2]
% 15.29/2.49  --inst_dismatching                      true
% 15.29/2.49  --inst_eager_unprocessed_to_passive     true
% 15.29/2.49  --inst_prop_sim_given                   true
% 15.29/2.49  --inst_prop_sim_new                     false
% 15.29/2.49  --inst_subs_new                         false
% 15.29/2.49  --inst_eq_res_simp                      false
% 15.29/2.49  --inst_subs_given                       false
% 15.29/2.49  --inst_orphan_elimination               true
% 15.29/2.49  --inst_learning_loop_flag               true
% 15.29/2.49  --inst_learning_start                   3000
% 15.29/2.49  --inst_learning_factor                  2
% 15.29/2.49  --inst_start_prop_sim_after_learn       3
% 15.29/2.49  --inst_sel_renew                        solver
% 15.29/2.49  --inst_lit_activity_flag                true
% 15.29/2.49  --inst_restr_to_given                   false
% 15.29/2.49  --inst_activity_threshold               500
% 15.29/2.49  --inst_out_proof                        true
% 15.29/2.49  
% 15.29/2.49  ------ Resolution Options
% 15.29/2.49  
% 15.29/2.49  --resolution_flag                       true
% 15.29/2.49  --res_lit_sel                           adaptive
% 15.29/2.49  --res_lit_sel_side                      none
% 15.29/2.49  --res_ordering                          kbo
% 15.29/2.49  --res_to_prop_solver                    active
% 15.29/2.49  --res_prop_simpl_new                    false
% 15.29/2.49  --res_prop_simpl_given                  true
% 15.29/2.49  --res_passive_queue_type                priority_queues
% 15.29/2.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.29/2.49  --res_passive_queues_freq               [15;5]
% 15.29/2.49  --res_forward_subs                      full
% 15.29/2.49  --res_backward_subs                     full
% 15.29/2.49  --res_forward_subs_resolution           true
% 15.29/2.49  --res_backward_subs_resolution          true
% 15.29/2.49  --res_orphan_elimination                true
% 15.29/2.49  --res_time_limit                        2.
% 15.29/2.49  --res_out_proof                         true
% 15.29/2.49  
% 15.29/2.49  ------ Superposition Options
% 15.29/2.49  
% 15.29/2.49  --superposition_flag                    true
% 15.29/2.49  --sup_passive_queue_type                priority_queues
% 15.29/2.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.29/2.49  --sup_passive_queues_freq               [8;1;4]
% 15.29/2.49  --demod_completeness_check              fast
% 15.29/2.49  --demod_use_ground                      true
% 15.29/2.49  --sup_to_prop_solver                    passive
% 15.29/2.49  --sup_prop_simpl_new                    true
% 15.29/2.49  --sup_prop_simpl_given                  true
% 15.29/2.49  --sup_fun_splitting                     false
% 15.29/2.49  --sup_smt_interval                      50000
% 15.29/2.49  
% 15.29/2.49  ------ Superposition Simplification Setup
% 15.29/2.49  
% 15.29/2.49  --sup_indices_passive                   []
% 15.29/2.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.29/2.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.29/2.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.29/2.49  --sup_full_triv                         [TrivRules;PropSubs]
% 15.29/2.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.29/2.49  --sup_full_bw                           [BwDemod]
% 15.29/2.49  --sup_immed_triv                        [TrivRules]
% 15.29/2.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.29/2.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.29/2.49  --sup_immed_bw_main                     []
% 15.29/2.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.29/2.49  --sup_input_triv                        [Unflattening;TrivRules]
% 15.29/2.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.29/2.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.29/2.49  
% 15.29/2.49  ------ Combination Options
% 15.29/2.49  
% 15.29/2.49  --comb_res_mult                         3
% 15.29/2.49  --comb_sup_mult                         2
% 15.29/2.49  --comb_inst_mult                        10
% 15.29/2.49  
% 15.29/2.49  ------ Debug Options
% 15.29/2.49  
% 15.29/2.49  --dbg_backtrace                         false
% 15.29/2.49  --dbg_dump_prop_clauses                 false
% 15.29/2.49  --dbg_dump_prop_clauses_file            -
% 15.29/2.49  --dbg_out_stat                          false
% 15.29/2.49  ------ Parsing...
% 15.29/2.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.29/2.49  
% 15.29/2.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 15.29/2.49  
% 15.29/2.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.29/2.49  
% 15.29/2.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.29/2.49  ------ Proving...
% 15.29/2.49  ------ Problem Properties 
% 15.29/2.49  
% 15.29/2.49  
% 15.29/2.49  clauses                                 25
% 15.29/2.49  conjectures                             2
% 15.29/2.49  EPR                                     2
% 15.29/2.49  Horn                                    21
% 15.29/2.49  unary                                   16
% 15.29/2.49  binary                                  0
% 15.29/2.49  lits                                    47
% 15.29/2.49  lits eq                                 33
% 15.29/2.49  fd_pure                                 0
% 15.29/2.49  fd_pseudo                               0
% 15.29/2.49  fd_cond                                 0
% 15.29/2.49  fd_pseudo_cond                          7
% 15.29/2.49  AC symbols                              0
% 15.29/2.49  
% 15.29/2.49  ------ Schedule dynamic 5 is on 
% 15.29/2.49  
% 15.29/2.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 15.29/2.49  
% 15.29/2.49  
% 15.29/2.49  ------ 
% 15.29/2.49  Current options:
% 15.29/2.49  ------ 
% 15.29/2.49  
% 15.29/2.49  ------ Input Options
% 15.29/2.49  
% 15.29/2.49  --out_options                           all
% 15.29/2.49  --tptp_safe_out                         true
% 15.29/2.49  --problem_path                          ""
% 15.29/2.49  --include_path                          ""
% 15.29/2.49  --clausifier                            res/vclausify_rel
% 15.29/2.49  --clausifier_options                    --mode clausify
% 15.29/2.49  --stdin                                 false
% 15.29/2.49  --stats_out                             all
% 15.29/2.49  
% 15.29/2.49  ------ General Options
% 15.29/2.49  
% 15.29/2.49  --fof                                   false
% 15.29/2.49  --time_out_real                         305.
% 15.29/2.49  --time_out_virtual                      -1.
% 15.29/2.49  --symbol_type_check                     false
% 15.29/2.49  --clausify_out                          false
% 15.29/2.49  --sig_cnt_out                           false
% 15.29/2.49  --trig_cnt_out                          false
% 15.29/2.49  --trig_cnt_out_tolerance                1.
% 15.29/2.49  --trig_cnt_out_sk_spl                   false
% 15.29/2.49  --abstr_cl_out                          false
% 15.29/2.49  
% 15.29/2.49  ------ Global Options
% 15.29/2.49  
% 15.29/2.49  --schedule                              default
% 15.29/2.49  --add_important_lit                     false
% 15.29/2.49  --prop_solver_per_cl                    1000
% 15.29/2.49  --min_unsat_core                        false
% 15.29/2.49  --soft_assumptions                      false
% 15.29/2.49  --soft_lemma_size                       3
% 15.29/2.49  --prop_impl_unit_size                   0
% 15.29/2.49  --prop_impl_unit                        []
% 15.29/2.49  --share_sel_clauses                     true
% 15.29/2.49  --reset_solvers                         false
% 15.29/2.49  --bc_imp_inh                            [conj_cone]
% 15.29/2.49  --conj_cone_tolerance                   3.
% 15.29/2.49  --extra_neg_conj                        none
% 15.29/2.49  --large_theory_mode                     true
% 15.29/2.49  --prolific_symb_bound                   200
% 15.29/2.49  --lt_threshold                          2000
% 15.29/2.49  --clause_weak_htbl                      true
% 15.29/2.49  --gc_record_bc_elim                     false
% 15.29/2.49  
% 15.29/2.49  ------ Preprocessing Options
% 15.29/2.49  
% 15.29/2.49  --preprocessing_flag                    true
% 15.29/2.49  --time_out_prep_mult                    0.1
% 15.29/2.49  --splitting_mode                        input
% 15.29/2.49  --splitting_grd                         true
% 15.29/2.49  --splitting_cvd                         false
% 15.29/2.49  --splitting_cvd_svl                     false
% 15.29/2.49  --splitting_nvd                         32
% 15.29/2.49  --sub_typing                            true
% 15.29/2.49  --prep_gs_sim                           true
% 15.29/2.49  --prep_unflatten                        true
% 15.29/2.49  --prep_res_sim                          true
% 15.29/2.49  --prep_upred                            true
% 15.29/2.49  --prep_sem_filter                       exhaustive
% 15.29/2.49  --prep_sem_filter_out                   false
% 15.29/2.49  --pred_elim                             true
% 15.29/2.49  --res_sim_input                         true
% 15.29/2.49  --eq_ax_congr_red                       true
% 15.29/2.49  --pure_diseq_elim                       true
% 15.29/2.49  --brand_transform                       false
% 15.29/2.49  --non_eq_to_eq                          false
% 15.29/2.49  --prep_def_merge                        true
% 15.29/2.49  --prep_def_merge_prop_impl              false
% 15.29/2.49  --prep_def_merge_mbd                    true
% 15.29/2.49  --prep_def_merge_tr_red                 false
% 15.29/2.49  --prep_def_merge_tr_cl                  false
% 15.29/2.49  --smt_preprocessing                     true
% 15.29/2.49  --smt_ac_axioms                         fast
% 15.29/2.49  --preprocessed_out                      false
% 15.29/2.49  --preprocessed_stats                    false
% 15.29/2.49  
% 15.29/2.49  ------ Abstraction refinement Options
% 15.29/2.49  
% 15.29/2.49  --abstr_ref                             []
% 15.29/2.49  --abstr_ref_prep                        false
% 15.29/2.49  --abstr_ref_until_sat                   false
% 15.29/2.49  --abstr_ref_sig_restrict                funpre
% 15.29/2.49  --abstr_ref_af_restrict_to_split_sk     false
% 15.29/2.49  --abstr_ref_under                       []
% 15.29/2.49  
% 15.29/2.49  ------ SAT Options
% 15.29/2.49  
% 15.29/2.49  --sat_mode                              false
% 15.29/2.49  --sat_fm_restart_options                ""
% 15.29/2.49  --sat_gr_def                            false
% 15.29/2.49  --sat_epr_types                         true
% 15.29/2.49  --sat_non_cyclic_types                  false
% 15.29/2.49  --sat_finite_models                     false
% 15.29/2.49  --sat_fm_lemmas                         false
% 15.29/2.49  --sat_fm_prep                           false
% 15.29/2.49  --sat_fm_uc_incr                        true
% 15.29/2.49  --sat_out_model                         small
% 15.29/2.49  --sat_out_clauses                       false
% 15.29/2.49  
% 15.29/2.49  ------ QBF Options
% 15.29/2.49  
% 15.29/2.49  --qbf_mode                              false
% 15.29/2.49  --qbf_elim_univ                         false
% 15.29/2.49  --qbf_dom_inst                          none
% 15.29/2.49  --qbf_dom_pre_inst                      false
% 15.29/2.49  --qbf_sk_in                             false
% 15.29/2.49  --qbf_pred_elim                         true
% 15.29/2.49  --qbf_split                             512
% 15.29/2.49  
% 15.29/2.49  ------ BMC1 Options
% 15.29/2.49  
% 15.29/2.49  --bmc1_incremental                      false
% 15.29/2.49  --bmc1_axioms                           reachable_all
% 15.29/2.49  --bmc1_min_bound                        0
% 15.29/2.49  --bmc1_max_bound                        -1
% 15.29/2.49  --bmc1_max_bound_default                -1
% 15.29/2.49  --bmc1_symbol_reachability              true
% 15.29/2.49  --bmc1_property_lemmas                  false
% 15.29/2.49  --bmc1_k_induction                      false
% 15.29/2.49  --bmc1_non_equiv_states                 false
% 15.29/2.49  --bmc1_deadlock                         false
% 15.29/2.49  --bmc1_ucm                              false
% 15.29/2.49  --bmc1_add_unsat_core                   none
% 15.29/2.49  --bmc1_unsat_core_children              false
% 15.29/2.49  --bmc1_unsat_core_extrapolate_axioms    false
% 15.29/2.49  --bmc1_out_stat                         full
% 15.29/2.49  --bmc1_ground_init                      false
% 15.29/2.49  --bmc1_pre_inst_next_state              false
% 15.29/2.49  --bmc1_pre_inst_state                   false
% 15.29/2.49  --bmc1_pre_inst_reach_state             false
% 15.29/2.49  --bmc1_out_unsat_core                   false
% 15.29/2.49  --bmc1_aig_witness_out                  false
% 15.29/2.49  --bmc1_verbose                          false
% 15.29/2.49  --bmc1_dump_clauses_tptp                false
% 15.29/2.49  --bmc1_dump_unsat_core_tptp             false
% 15.29/2.49  --bmc1_dump_file                        -
% 15.29/2.49  --bmc1_ucm_expand_uc_limit              128
% 15.29/2.49  --bmc1_ucm_n_expand_iterations          6
% 15.29/2.49  --bmc1_ucm_extend_mode                  1
% 15.29/2.49  --bmc1_ucm_init_mode                    2
% 15.29/2.49  --bmc1_ucm_cone_mode                    none
% 15.29/2.49  --bmc1_ucm_reduced_relation_type        0
% 15.29/2.49  --bmc1_ucm_relax_model                  4
% 15.29/2.49  --bmc1_ucm_full_tr_after_sat            true
% 15.29/2.49  --bmc1_ucm_expand_neg_assumptions       false
% 15.29/2.49  --bmc1_ucm_layered_model                none
% 15.29/2.49  --bmc1_ucm_max_lemma_size               10
% 15.29/2.49  
% 15.29/2.49  ------ AIG Options
% 15.29/2.49  
% 15.29/2.49  --aig_mode                              false
% 15.29/2.49  
% 15.29/2.49  ------ Instantiation Options
% 15.29/2.49  
% 15.29/2.49  --instantiation_flag                    true
% 15.29/2.49  --inst_sos_flag                         false
% 15.29/2.49  --inst_sos_phase                        true
% 15.29/2.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.29/2.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.29/2.49  --inst_lit_sel_side                     none
% 15.29/2.49  --inst_solver_per_active                1400
% 15.29/2.49  --inst_solver_calls_frac                1.
% 15.29/2.49  --inst_passive_queue_type               priority_queues
% 15.29/2.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.29/2.49  --inst_passive_queues_freq              [25;2]
% 15.29/2.49  --inst_dismatching                      true
% 15.29/2.49  --inst_eager_unprocessed_to_passive     true
% 15.29/2.49  --inst_prop_sim_given                   true
% 15.29/2.49  --inst_prop_sim_new                     false
% 15.29/2.49  --inst_subs_new                         false
% 15.29/2.49  --inst_eq_res_simp                      false
% 15.29/2.49  --inst_subs_given                       false
% 15.29/2.49  --inst_orphan_elimination               true
% 15.29/2.49  --inst_learning_loop_flag               true
% 15.29/2.49  --inst_learning_start                   3000
% 15.29/2.49  --inst_learning_factor                  2
% 15.29/2.49  --inst_start_prop_sim_after_learn       3
% 15.29/2.49  --inst_sel_renew                        solver
% 15.29/2.49  --inst_lit_activity_flag                true
% 15.29/2.49  --inst_restr_to_given                   false
% 15.29/2.49  --inst_activity_threshold               500
% 15.29/2.49  --inst_out_proof                        true
% 15.29/2.49  
% 15.29/2.49  ------ Resolution Options
% 15.29/2.49  
% 15.29/2.49  --resolution_flag                       false
% 15.29/2.49  --res_lit_sel                           adaptive
% 15.29/2.49  --res_lit_sel_side                      none
% 15.29/2.49  --res_ordering                          kbo
% 15.29/2.49  --res_to_prop_solver                    active
% 15.29/2.49  --res_prop_simpl_new                    false
% 15.29/2.49  --res_prop_simpl_given                  true
% 15.29/2.49  --res_passive_queue_type                priority_queues
% 15.29/2.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.29/2.49  --res_passive_queues_freq               [15;5]
% 15.29/2.49  --res_forward_subs                      full
% 15.29/2.49  --res_backward_subs                     full
% 15.29/2.49  --res_forward_subs_resolution           true
% 15.29/2.49  --res_backward_subs_resolution          true
% 15.29/2.49  --res_orphan_elimination                true
% 15.29/2.49  --res_time_limit                        2.
% 15.29/2.49  --res_out_proof                         true
% 15.29/2.49  
% 15.29/2.49  ------ Superposition Options
% 15.29/2.49  
% 15.29/2.49  --superposition_flag                    true
% 15.29/2.49  --sup_passive_queue_type                priority_queues
% 15.29/2.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.29/2.49  --sup_passive_queues_freq               [8;1;4]
% 15.29/2.49  --demod_completeness_check              fast
% 15.29/2.49  --demod_use_ground                      true
% 15.29/2.49  --sup_to_prop_solver                    passive
% 15.29/2.49  --sup_prop_simpl_new                    true
% 15.29/2.49  --sup_prop_simpl_given                  true
% 15.29/2.49  --sup_fun_splitting                     false
% 15.29/2.49  --sup_smt_interval                      50000
% 15.29/2.49  
% 15.29/2.49  ------ Superposition Simplification Setup
% 15.29/2.49  
% 15.29/2.49  --sup_indices_passive                   []
% 15.29/2.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.29/2.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.29/2.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.29/2.49  --sup_full_triv                         [TrivRules;PropSubs]
% 15.29/2.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.29/2.49  --sup_full_bw                           [BwDemod]
% 15.29/2.49  --sup_immed_triv                        [TrivRules]
% 15.29/2.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.29/2.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.29/2.49  --sup_immed_bw_main                     []
% 15.29/2.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.29/2.49  --sup_input_triv                        [Unflattening;TrivRules]
% 15.29/2.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.29/2.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.29/2.49  
% 15.29/2.49  ------ Combination Options
% 15.29/2.49  
% 15.29/2.49  --comb_res_mult                         3
% 15.29/2.49  --comb_sup_mult                         2
% 15.29/2.49  --comb_inst_mult                        10
% 15.29/2.49  
% 15.29/2.49  ------ Debug Options
% 15.29/2.49  
% 15.29/2.49  --dbg_backtrace                         false
% 15.29/2.49  --dbg_dump_prop_clauses                 false
% 15.29/2.49  --dbg_dump_prop_clauses_file            -
% 15.29/2.49  --dbg_out_stat                          false
% 15.29/2.49  
% 15.29/2.49  
% 15.29/2.49  
% 15.29/2.49  
% 15.29/2.49  ------ Proving...
% 15.29/2.49  
% 15.29/2.49  
% 15.29/2.49  % SZS status Theorem for theBenchmark.p
% 15.29/2.49  
% 15.29/2.49  % SZS output start CNFRefutation for theBenchmark.p
% 15.29/2.49  
% 15.29/2.49  fof(f8,axiom,(
% 15.29/2.49    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0)),
% 15.29/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.29/2.49  
% 15.29/2.49  fof(f55,plain,(
% 15.29/2.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0)) )),
% 15.29/2.49    inference(cnf_transformation,[],[f8])).
% 15.29/2.49  
% 15.29/2.49  fof(f12,axiom,(
% 15.29/2.49    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 15.29/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.29/2.49  
% 15.29/2.49  fof(f59,plain,(
% 15.29/2.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 15.29/2.49    inference(cnf_transformation,[],[f12])).
% 15.29/2.49  
% 15.29/2.49  fof(f87,plain,(
% 15.29/2.49    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k2_enumset1(X2,X2,X1,X0)) )),
% 15.29/2.49    inference(definition_unfolding,[],[f55,f59,f59])).
% 15.29/2.49  
% 15.29/2.49  fof(f9,axiom,(
% 15.29/2.49    ! [X0,X1,X2,X3] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) = k2_enumset1(X0,X1,X2,X3)),
% 15.29/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.29/2.49  
% 15.29/2.49  fof(f56,plain,(
% 15.29/2.49    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) = k2_enumset1(X0,X1,X2,X3)) )),
% 15.29/2.49    inference(cnf_transformation,[],[f9])).
% 15.29/2.49  
% 15.29/2.49  fof(f10,axiom,(
% 15.29/2.49    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 15.29/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.29/2.49  
% 15.29/2.49  fof(f57,plain,(
% 15.29/2.49    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 15.29/2.49    inference(cnf_transformation,[],[f10])).
% 15.29/2.49  
% 15.29/2.49  fof(f11,axiom,(
% 15.29/2.49    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 15.29/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.29/2.49  
% 15.29/2.49  fof(f58,plain,(
% 15.29/2.49    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 15.29/2.49    inference(cnf_transformation,[],[f11])).
% 15.29/2.49  
% 15.29/2.49  fof(f68,plain,(
% 15.29/2.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 15.29/2.49    inference(definition_unfolding,[],[f58,f59])).
% 15.29/2.49  
% 15.29/2.49  fof(f69,plain,(
% 15.29/2.49    ( ! [X0] : (k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0)) )),
% 15.29/2.49    inference(definition_unfolding,[],[f57,f68])).
% 15.29/2.49  
% 15.29/2.49  fof(f72,plain,(
% 15.29/2.49    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k2_enumset1(X0,X0,X1,X2),k2_enumset1(X3,X3,X3,X3)) = k2_enumset1(X0,X1,X2,X3)) )),
% 15.29/2.49    inference(definition_unfolding,[],[f56,f59,f69])).
% 15.29/2.49  
% 15.29/2.49  fof(f5,axiom,(
% 15.29/2.49    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 15.29/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.29/2.49  
% 15.29/2.49  fof(f21,plain,(
% 15.29/2.49    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 15.29/2.49    inference(ennf_transformation,[],[f5])).
% 15.29/2.49  
% 15.29/2.49  fof(f40,plain,(
% 15.29/2.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 15.29/2.49    inference(cnf_transformation,[],[f21])).
% 15.29/2.49  
% 15.29/2.49  fof(f18,conjecture,(
% 15.29/2.49    ! [X0,X1,X2] : ~(X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 15.29/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.29/2.49  
% 15.29/2.49  fof(f19,negated_conjecture,(
% 15.29/2.49    ~! [X0,X1,X2] : ~(X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 15.29/2.49    inference(negated_conjecture,[],[f18])).
% 15.29/2.49  
% 15.29/2.49  fof(f23,plain,(
% 15.29/2.49    ? [X0,X1,X2] : (X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 15.29/2.49    inference(ennf_transformation,[],[f19])).
% 15.29/2.49  
% 15.29/2.49  fof(f34,plain,(
% 15.29/2.49    ? [X0,X1,X2] : (X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2))) => (sK2 != sK4 & sK2 != sK3 & r1_tarski(k1_tarski(sK2),k2_tarski(sK3,sK4)))),
% 15.29/2.49    introduced(choice_axiom,[])).
% 15.29/2.49  
% 15.29/2.49  fof(f35,plain,(
% 15.29/2.49    sK2 != sK4 & sK2 != sK3 & r1_tarski(k1_tarski(sK2),k2_tarski(sK3,sK4))),
% 15.29/2.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f23,f34])).
% 15.29/2.49  
% 15.29/2.49  fof(f65,plain,(
% 15.29/2.49    r1_tarski(k1_tarski(sK2),k2_tarski(sK3,sK4))),
% 15.29/2.49    inference(cnf_transformation,[],[f35])).
% 15.29/2.49  
% 15.29/2.49  fof(f90,plain,(
% 15.29/2.49    r1_tarski(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK3,sK3,sK3,sK4))),
% 15.29/2.49    inference(definition_unfolding,[],[f65,f69,f68])).
% 15.29/2.49  
% 15.29/2.49  fof(f1,axiom,(
% 15.29/2.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 15.29/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.29/2.49  
% 15.29/2.49  fof(f36,plain,(
% 15.29/2.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 15.29/2.49    inference(cnf_transformation,[],[f1])).
% 15.29/2.49  
% 15.29/2.49  fof(f2,axiom,(
% 15.29/2.49    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 15.29/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.29/2.49  
% 15.29/2.49  fof(f20,plain,(
% 15.29/2.49    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 15.29/2.49    inference(rectify,[],[f2])).
% 15.29/2.49  
% 15.29/2.49  fof(f37,plain,(
% 15.29/2.49    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 15.29/2.49    inference(cnf_transformation,[],[f20])).
% 15.29/2.49  
% 15.29/2.49  fof(f4,axiom,(
% 15.29/2.49    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 15.29/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.29/2.49  
% 15.29/2.49  fof(f39,plain,(
% 15.29/2.49    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 15.29/2.49    inference(cnf_transformation,[],[f4])).
% 15.29/2.49  
% 15.29/2.49  fof(f3,axiom,(
% 15.29/2.49    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 15.29/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.29/2.49  
% 15.29/2.49  fof(f38,plain,(
% 15.29/2.49    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 15.29/2.49    inference(cnf_transformation,[],[f3])).
% 15.29/2.49  
% 15.29/2.49  fof(f6,axiom,(
% 15.29/2.49    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 15.29/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.29/2.49  
% 15.29/2.49  fof(f22,plain,(
% 15.29/2.49    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 15.29/2.49    inference(ennf_transformation,[],[f6])).
% 15.29/2.49  
% 15.29/2.49  fof(f24,plain,(
% 15.29/2.49    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 15.29/2.49    inference(nnf_transformation,[],[f22])).
% 15.29/2.49  
% 15.29/2.49  fof(f25,plain,(
% 15.29/2.49    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 15.29/2.49    inference(flattening,[],[f24])).
% 15.29/2.49  
% 15.29/2.49  fof(f26,plain,(
% 15.29/2.49    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 15.29/2.49    inference(rectify,[],[f25])).
% 15.29/2.49  
% 15.29/2.49  fof(f27,plain,(
% 15.29/2.49    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3))))),
% 15.29/2.49    introduced(choice_axiom,[])).
% 15.29/2.49  
% 15.29/2.49  fof(f28,plain,(
% 15.29/2.49    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 15.29/2.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).
% 15.29/2.49  
% 15.29/2.49  fof(f44,plain,(
% 15.29/2.49    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 15.29/2.49    inference(cnf_transformation,[],[f28])).
% 15.29/2.49  
% 15.29/2.49  fof(f77,plain,(
% 15.29/2.49    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 15.29/2.49    inference(definition_unfolding,[],[f44,f59])).
% 15.29/2.49  
% 15.29/2.49  fof(f91,plain,(
% 15.29/2.49    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k2_enumset1(X0,X0,X1,X5) != X3) )),
% 15.29/2.49    inference(equality_resolution,[],[f77])).
% 15.29/2.49  
% 15.29/2.49  fof(f92,plain,(
% 15.29/2.49    ( ! [X0,X5,X1] : (r2_hidden(X5,k2_enumset1(X0,X0,X1,X5))) )),
% 15.29/2.49    inference(equality_resolution,[],[f91])).
% 15.29/2.49  
% 15.29/2.49  fof(f41,plain,(
% 15.29/2.49    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 15.29/2.49    inference(cnf_transformation,[],[f28])).
% 15.29/2.49  
% 15.29/2.49  fof(f80,plain,(
% 15.29/2.49    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 15.29/2.49    inference(definition_unfolding,[],[f41,f59])).
% 15.29/2.49  
% 15.29/2.49  fof(f97,plain,(
% 15.29/2.49    ( ! [X2,X0,X5,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,k2_enumset1(X0,X0,X1,X2))) )),
% 15.29/2.49    inference(equality_resolution,[],[f80])).
% 15.29/2.49  
% 15.29/2.49  fof(f67,plain,(
% 15.29/2.49    sK2 != sK4),
% 15.29/2.49    inference(cnf_transformation,[],[f35])).
% 15.29/2.49  
% 15.29/2.49  fof(f66,plain,(
% 15.29/2.49    sK2 != sK3),
% 15.29/2.49    inference(cnf_transformation,[],[f35])).
% 15.29/2.49  
% 15.29/2.49  cnf(c_20,plain,
% 15.29/2.49      ( k2_enumset1(X0,X0,X1,X2) = k2_enumset1(X2,X2,X1,X0) ),
% 15.29/2.49      inference(cnf_transformation,[],[f87]) ).
% 15.29/2.49  
% 15.29/2.49  cnf(c_0,plain,
% 15.29/2.49      ( k2_xboole_0(k2_enumset1(X0,X0,X1,X2),k2_enumset1(X3,X3,X3,X3)) = k2_enumset1(X0,X1,X2,X3) ),
% 15.29/2.49      inference(cnf_transformation,[],[f72]) ).
% 15.29/2.49  
% 15.29/2.49  cnf(c_3891,plain,
% 15.29/2.49      ( k2_xboole_0(k2_enumset1(X0,X0,X1,X2),k2_enumset1(X3,X3,X3,X3)) = k2_enumset1(X2,X1,X0,X3) ),
% 15.29/2.49      inference(superposition,[status(thm)],[c_20,c_0]) ).
% 15.29/2.49  
% 15.29/2.49  cnf(c_5,plain,
% 15.29/2.49      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 15.29/2.49      inference(cnf_transformation,[],[f40]) ).
% 15.29/2.49  
% 15.29/2.49  cnf(c_25,negated_conjecture,
% 15.29/2.49      ( r1_tarski(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK3,sK3,sK3,sK4)) ),
% 15.29/2.49      inference(cnf_transformation,[],[f90]) ).
% 15.29/2.49  
% 15.29/2.49  cnf(c_184,plain,
% 15.29/2.49      ( k2_enumset1(sK3,sK3,sK3,sK4) != X0
% 15.29/2.49      | k2_enumset1(sK2,sK2,sK2,sK2) != X1
% 15.29/2.49      | k3_xboole_0(X1,X0) = X1 ),
% 15.29/2.49      inference(resolution_lifted,[status(thm)],[c_5,c_25]) ).
% 15.29/2.49  
% 15.29/2.49  cnf(c_185,plain,
% 15.29/2.49      ( k3_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK3,sK3,sK3,sK4)) = k2_enumset1(sK2,sK2,sK2,sK2) ),
% 15.29/2.49      inference(unflattening,[status(thm)],[c_184]) ).
% 15.29/2.49  
% 15.29/2.49  cnf(c_2198,plain,
% 15.29/2.49      ( k3_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK4,sK4,sK3,sK3)) = k2_enumset1(sK2,sK2,sK2,sK2) ),
% 15.29/2.49      inference(demodulation,[status(thm)],[c_20,c_185]) ).
% 15.29/2.49  
% 15.29/2.49  cnf(c_1,plain,
% 15.29/2.49      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 15.29/2.49      inference(cnf_transformation,[],[f36]) ).
% 15.29/2.49  
% 15.29/2.49  cnf(c_2,plain,
% 15.29/2.49      ( k3_xboole_0(X0,X0) = X0 ),
% 15.29/2.49      inference(cnf_transformation,[],[f37]) ).
% 15.29/2.49  
% 15.29/2.49  cnf(c_4,plain,
% 15.29/2.49      ( k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 15.29/2.49      inference(cnf_transformation,[],[f39]) ).
% 15.29/2.49  
% 15.29/2.49  cnf(c_2356,plain,
% 15.29/2.49      ( k3_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,k3_xboole_0(X0,X1)) ),
% 15.29/2.49      inference(superposition,[status(thm)],[c_2,c_4]) ).
% 15.29/2.49  
% 15.29/2.49  cnf(c_3,plain,
% 15.29/2.49      ( k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
% 15.29/2.49      inference(cnf_transformation,[],[f38]) ).
% 15.29/2.49  
% 15.29/2.49  cnf(c_2374,plain,
% 15.29/2.49      ( k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
% 15.29/2.49      inference(light_normalisation,[status(thm)],[c_2356,c_3]) ).
% 15.29/2.49  
% 15.29/2.49  cnf(c_3925,plain,
% 15.29/2.49      ( k2_xboole_0(X0,k3_xboole_0(X1,X0)) = X0 ),
% 15.29/2.49      inference(superposition,[status(thm)],[c_1,c_2374]) ).
% 15.29/2.49  
% 15.29/2.49  cnf(c_4117,plain,
% 15.29/2.49      ( k2_xboole_0(k2_enumset1(sK4,sK4,sK3,sK3),k2_enumset1(sK2,sK2,sK2,sK2)) = k2_enumset1(sK4,sK4,sK3,sK3) ),
% 15.29/2.49      inference(superposition,[status(thm)],[c_2198,c_3925]) ).
% 15.29/2.49  
% 15.29/2.49  cnf(c_39742,plain,
% 15.29/2.49      ( k2_enumset1(sK4,sK4,sK3,sK3) = k2_enumset1(sK3,sK3,sK4,sK2) ),
% 15.29/2.49      inference(superposition,[status(thm)],[c_3891,c_4117]) ).
% 15.29/2.49  
% 15.29/2.49  cnf(c_10,plain,
% 15.29/2.49      ( r2_hidden(X0,k2_enumset1(X1,X1,X2,X0)) ),
% 15.29/2.49      inference(cnf_transformation,[],[f92]) ).
% 15.29/2.49  
% 15.29/2.49  cnf(c_1839,plain,
% 15.29/2.49      ( r2_hidden(X0,k2_enumset1(X1,X1,X2,X0)) = iProver_top ),
% 15.29/2.49      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 15.29/2.49  
% 15.29/2.49  cnf(c_41212,plain,
% 15.29/2.49      ( r2_hidden(sK2,k2_enumset1(sK4,sK4,sK3,sK3)) = iProver_top ),
% 15.29/2.49      inference(superposition,[status(thm)],[c_39742,c_1839]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_13,plain,
% 15.29/2.50      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X2,X3))
% 15.29/2.50      | X0 = X1
% 15.29/2.50      | X0 = X2
% 15.29/2.50      | X0 = X3 ),
% 15.29/2.50      inference(cnf_transformation,[],[f97]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_1992,plain,
% 15.29/2.50      ( ~ r2_hidden(sK2,k2_enumset1(sK4,sK4,X0,X1))
% 15.29/2.50      | sK2 = X0
% 15.29/2.50      | sK2 = X1
% 15.29/2.50      | sK2 = sK4 ),
% 15.29/2.50      inference(instantiation,[status(thm)],[c_13]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_2033,plain,
% 15.29/2.50      ( ~ r2_hidden(sK2,k2_enumset1(sK4,sK4,sK3,X0))
% 15.29/2.50      | sK2 = X0
% 15.29/2.50      | sK2 = sK3
% 15.29/2.50      | sK2 = sK4 ),
% 15.29/2.50      inference(instantiation,[status(thm)],[c_1992]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_2153,plain,
% 15.29/2.50      ( ~ r2_hidden(sK2,k2_enumset1(sK4,sK4,sK3,sK3))
% 15.29/2.50      | sK2 = sK3
% 15.29/2.50      | sK2 = sK4 ),
% 15.29/2.50      inference(instantiation,[status(thm)],[c_2033]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_2154,plain,
% 15.29/2.50      ( sK2 = sK3
% 15.29/2.50      | sK2 = sK4
% 15.29/2.50      | r2_hidden(sK2,k2_enumset1(sK4,sK4,sK3,sK3)) != iProver_top ),
% 15.29/2.50      inference(predicate_to_equality,[status(thm)],[c_2153]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_23,negated_conjecture,
% 15.29/2.50      ( sK2 != sK4 ),
% 15.29/2.50      inference(cnf_transformation,[],[f67]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_24,negated_conjecture,
% 15.29/2.50      ( sK2 != sK3 ),
% 15.29/2.50      inference(cnf_transformation,[],[f66]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(contradiction,plain,
% 15.29/2.50      ( $false ),
% 15.29/2.50      inference(minisat,[status(thm)],[c_41212,c_2154,c_23,c_24]) ).
% 15.29/2.50  
% 15.29/2.50  
% 15.29/2.50  % SZS output end CNFRefutation for theBenchmark.p
% 15.29/2.50  
% 15.29/2.50  ------                               Statistics
% 15.29/2.50  
% 15.29/2.50  ------ General
% 15.29/2.50  
% 15.29/2.50  abstr_ref_over_cycles:                  0
% 15.29/2.50  abstr_ref_under_cycles:                 0
% 15.29/2.50  gc_basic_clause_elim:                   0
% 15.29/2.50  forced_gc_time:                         0
% 15.29/2.50  parsing_time:                           0.009
% 15.29/2.50  unif_index_cands_time:                  0.
% 15.29/2.50  unif_index_add_time:                    0.
% 15.29/2.50  orderings_time:                         0.
% 15.29/2.50  out_proof_time:                         0.01
% 15.29/2.50  total_time:                             1.735
% 15.29/2.50  num_of_symbols:                         42
% 15.29/2.50  num_of_terms:                           56221
% 15.29/2.50  
% 15.29/2.50  ------ Preprocessing
% 15.29/2.50  
% 15.29/2.50  num_of_splits:                          0
% 15.29/2.50  num_of_split_atoms:                     0
% 15.29/2.50  num_of_reused_defs:                     0
% 15.29/2.50  num_eq_ax_congr_red:                    46
% 15.29/2.50  num_of_sem_filtered_clauses:            1
% 15.29/2.50  num_of_subtypes:                        0
% 15.29/2.50  monotx_restored_types:                  0
% 15.29/2.50  sat_num_of_epr_types:                   0
% 15.29/2.50  sat_num_of_non_cyclic_types:            0
% 15.29/2.50  sat_guarded_non_collapsed_types:        0
% 15.29/2.50  num_pure_diseq_elim:                    0
% 15.29/2.50  simp_replaced_by:                       0
% 15.29/2.50  res_preprocessed:                       114
% 15.29/2.50  prep_upred:                             0
% 15.29/2.50  prep_unflattend:                        98
% 15.29/2.50  smt_new_axioms:                         0
% 15.29/2.50  pred_elim_cands:                        1
% 15.29/2.50  pred_elim:                              1
% 15.29/2.50  pred_elim_cl:                           1
% 15.29/2.50  pred_elim_cycles:                       3
% 15.29/2.50  merged_defs:                            0
% 15.29/2.50  merged_defs_ncl:                        0
% 15.29/2.50  bin_hyper_res:                          0
% 15.29/2.50  prep_cycles:                            4
% 15.29/2.50  pred_elim_time:                         0.019
% 15.29/2.50  splitting_time:                         0.
% 15.29/2.50  sem_filter_time:                        0.
% 15.29/2.50  monotx_time:                            0.
% 15.29/2.50  subtype_inf_time:                       0.
% 15.29/2.50  
% 15.29/2.50  ------ Problem properties
% 15.29/2.50  
% 15.29/2.50  clauses:                                25
% 15.29/2.50  conjectures:                            2
% 15.29/2.50  epr:                                    2
% 15.29/2.50  horn:                                   21
% 15.29/2.50  ground:                                 3
% 15.29/2.50  unary:                                  16
% 15.29/2.50  binary:                                 0
% 15.29/2.50  lits:                                   47
% 15.29/2.50  lits_eq:                                33
% 15.29/2.50  fd_pure:                                0
% 15.29/2.50  fd_pseudo:                              0
% 15.29/2.50  fd_cond:                                0
% 15.29/2.50  fd_pseudo_cond:                         7
% 15.29/2.50  ac_symbols:                             0
% 15.29/2.50  
% 15.29/2.50  ------ Propositional Solver
% 15.29/2.50  
% 15.29/2.50  prop_solver_calls:                      31
% 15.29/2.50  prop_fast_solver_calls:                 1004
% 15.29/2.50  smt_solver_calls:                       0
% 15.29/2.50  smt_fast_solver_calls:                  0
% 15.29/2.50  prop_num_of_clauses:                    13046
% 15.29/2.50  prop_preprocess_simplified:             23158
% 15.29/2.50  prop_fo_subsumed:                       0
% 15.29/2.50  prop_solver_time:                       0.
% 15.29/2.50  smt_solver_time:                        0.
% 15.29/2.50  smt_fast_solver_time:                   0.
% 15.29/2.50  prop_fast_solver_time:                  0.
% 15.29/2.50  prop_unsat_core_time:                   0.001
% 15.29/2.50  
% 15.29/2.50  ------ QBF
% 15.29/2.50  
% 15.29/2.50  qbf_q_res:                              0
% 15.29/2.50  qbf_num_tautologies:                    0
% 15.29/2.50  qbf_prep_cycles:                        0
% 15.29/2.50  
% 15.29/2.50  ------ BMC1
% 15.29/2.50  
% 15.29/2.50  bmc1_current_bound:                     -1
% 15.29/2.50  bmc1_last_solved_bound:                 -1
% 15.29/2.50  bmc1_unsat_core_size:                   -1
% 15.29/2.50  bmc1_unsat_core_parents_size:           -1
% 15.29/2.50  bmc1_merge_next_fun:                    0
% 15.29/2.50  bmc1_unsat_core_clauses_time:           0.
% 15.29/2.50  
% 15.29/2.50  ------ Instantiation
% 15.29/2.50  
% 15.29/2.50  inst_num_of_clauses:                    2632
% 15.29/2.50  inst_num_in_passive:                    1974
% 15.29/2.50  inst_num_in_active:                     542
% 15.29/2.50  inst_num_in_unprocessed:                116
% 15.29/2.50  inst_num_of_loops:                      870
% 15.29/2.50  inst_num_of_learning_restarts:          0
% 15.29/2.50  inst_num_moves_active_passive:          327
% 15.29/2.50  inst_lit_activity:                      0
% 15.29/2.50  inst_lit_activity_moves:                0
% 15.29/2.50  inst_num_tautologies:                   0
% 15.29/2.50  inst_num_prop_implied:                  0
% 15.29/2.50  inst_num_existing_simplified:           0
% 15.29/2.50  inst_num_eq_res_simplified:             0
% 15.29/2.50  inst_num_child_elim:                    0
% 15.29/2.50  inst_num_of_dismatching_blockings:      2167
% 15.29/2.50  inst_num_of_non_proper_insts:           3392
% 15.29/2.50  inst_num_of_duplicates:                 0
% 15.29/2.50  inst_inst_num_from_inst_to_res:         0
% 15.29/2.50  inst_dismatching_checking_time:         0.
% 15.29/2.50  
% 15.29/2.50  ------ Resolution
% 15.29/2.50  
% 15.29/2.50  res_num_of_clauses:                     0
% 15.29/2.50  res_num_in_passive:                     0
% 15.29/2.50  res_num_in_active:                      0
% 15.29/2.50  res_num_of_loops:                       118
% 15.29/2.50  res_forward_subset_subsumed:            1061
% 15.29/2.50  res_backward_subset_subsumed:           0
% 15.29/2.50  res_forward_subsumed:                   16
% 15.29/2.50  res_backward_subsumed:                  0
% 15.29/2.50  res_forward_subsumption_resolution:     0
% 15.29/2.50  res_backward_subsumption_resolution:    0
% 15.29/2.50  res_clause_to_clause_subsumption:       52986
% 15.29/2.50  res_orphan_elimination:                 0
% 15.29/2.50  res_tautology_del:                      36
% 15.29/2.50  res_num_eq_res_simplified:              0
% 15.29/2.50  res_num_sel_changes:                    0
% 15.29/2.50  res_moves_from_active_to_pass:          0
% 15.29/2.50  
% 15.29/2.50  ------ Superposition
% 15.29/2.50  
% 15.29/2.50  sup_time_total:                         0.
% 15.29/2.50  sup_time_generating:                    0.
% 15.29/2.50  sup_time_sim_full:                      0.
% 15.29/2.50  sup_time_sim_immed:                     0.
% 15.29/2.50  
% 15.29/2.50  sup_num_of_clauses:                     3242
% 15.29/2.50  sup_num_in_active:                      148
% 15.29/2.50  sup_num_in_passive:                     3094
% 15.29/2.50  sup_num_of_loops:                       173
% 15.29/2.50  sup_fw_superposition:                   4397
% 15.29/2.50  sup_bw_superposition:                   3348
% 15.29/2.50  sup_immediate_simplified:               2856
% 15.29/2.50  sup_given_eliminated:                   11
% 15.29/2.50  comparisons_done:                       0
% 15.29/2.50  comparisons_avoided:                    10
% 15.29/2.50  
% 15.29/2.50  ------ Simplifications
% 15.29/2.50  
% 15.29/2.50  
% 15.29/2.50  sim_fw_subset_subsumed:                 0
% 15.29/2.50  sim_bw_subset_subsumed:                 0
% 15.29/2.50  sim_fw_subsumed:                        463
% 15.29/2.50  sim_bw_subsumed:                        130
% 15.29/2.50  sim_fw_subsumption_res:                 0
% 15.29/2.50  sim_bw_subsumption_res:                 0
% 15.29/2.50  sim_tautology_del:                      0
% 15.29/2.50  sim_eq_tautology_del:                   591
% 15.29/2.50  sim_eq_res_simp:                        0
% 15.29/2.50  sim_fw_demodulated:                     1479
% 15.29/2.50  sim_bw_demodulated:                     464
% 15.29/2.50  sim_light_normalised:                   1410
% 15.29/2.50  sim_joinable_taut:                      0
% 15.29/2.50  sim_joinable_simp:                      0
% 15.29/2.50  sim_ac_normalised:                      0
% 15.29/2.50  sim_smt_subsumption:                    0
% 15.29/2.50  
%------------------------------------------------------------------------------
