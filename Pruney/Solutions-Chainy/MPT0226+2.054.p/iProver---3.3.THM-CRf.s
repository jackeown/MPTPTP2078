%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:30:23 EST 2020

% Result     : Theorem 1.55s
% Output     : CNFRefutation 1.55s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 196 expanded)
%              Number of clauses        :   24 (  28 expanded)
%              Number of leaves         :   12 (  58 expanded)
%              Depth                    :   15
%              Number of atoms          :  205 ( 627 expanded)
%              Number of equality atoms :  166 ( 518 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,conjecture,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_xboole_0
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_xboole_0
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f9])).

fof(f12,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_xboole_0 ) ),
    inference(ennf_transformation,[],[f10])).

fof(f18,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_xboole_0 )
   => ( sK1 != sK2
      & k4_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) = k1_xboole_0 ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( sK1 != sK2
    & k4_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) = k1_xboole_0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f12,f18])).

fof(f35,plain,(
    k4_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f19])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f6,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f49,plain,(
    k5_xboole_0(k2_tarski(sK1,sK1),k3_xboole_0(k2_tarski(sK1,sK1),k2_tarski(sK2,sK2))) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f35,f20,f32,f32])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f3,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f37,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f22,f20])).

fof(f38,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))) = k1_enumset1(X0,X1,X2) ),
    inference(definition_unfolding,[],[f31,f37,f32])).

fof(f48,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))) = k2_enumset1(X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f34,f38])).

fof(f2,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f13,plain,(
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
    inference(nnf_transformation,[],[f11])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f15,plain,(
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
    inference(rectify,[],[f14])).

fof(f16,plain,(
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

fof(f17,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f16])).

fof(f26,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f44,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))) != X3 ) ),
    inference(definition_unfolding,[],[f26,f38])).

fof(f50,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X5),k3_xboole_0(k2_tarski(X1,X5),k2_tarski(X0,X0)))) != X3 ) ),
    inference(equality_resolution,[],[f44])).

fof(f51,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X5),k3_xboole_0(k2_tarski(X1,X5),k2_tarski(X0,X0))))) ),
    inference(equality_resolution,[],[f50])).

fof(f7,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f39,plain,(
    ! [X0,X1] : k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X0,X1),k3_xboole_0(k2_tarski(X0,X1),k2_tarski(X0,X0)))) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f33,f38])).

fof(f23,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f47,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))) != X3 ) ),
    inference(definition_unfolding,[],[f23,f38])).

fof(f56,plain,(
    ! [X2,X0,X5,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0))))) ) ),
    inference(equality_resolution,[],[f47])).

fof(f24,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f46,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))) != X3 ) ),
    inference(definition_unfolding,[],[f24,f38])).

fof(f54,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k5_xboole_0(k2_tarski(X5,X5),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X5,X5)))) != X3 ) ),
    inference(equality_resolution,[],[f46])).

fof(f55,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k5_xboole_0(k2_tarski(X5,X5),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X5,X5))))) ),
    inference(equality_resolution,[],[f54])).

fof(f36,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f19])).

cnf(c_12,negated_conjecture,
    ( k5_xboole_0(k2_tarski(sK1,sK1),k3_xboole_0(k2_tarski(sK1,sK1),k2_tarski(sK2,sK2))) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_10,plain,
    ( k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_792,plain,
    ( k2_enumset1(sK2,sK2,sK1,sK1) = k5_xboole_0(k2_tarski(sK2,sK2),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_12,c_10])).

cnf(c_1,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f21])).

cnf(c_797,plain,
    ( k2_enumset1(sK2,sK2,sK1,sK1) = k2_tarski(sK2,sK2) ),
    inference(demodulation,[status(thm)],[c_792,c_1])).

cnf(c_6,plain,
    ( r2_hidden(X0,k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X0),k3_xboole_0(k2_tarski(X2,X0),k2_tarski(X1,X1))))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_454,plain,
    ( r2_hidden(X0,k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X0),k3_xboole_0(k2_tarski(X2,X0),k2_tarski(X1,X1))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_475,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X2,X0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_10,c_454])).

cnf(c_961,plain,
    ( r2_hidden(sK1,k2_tarski(sK2,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_797,c_475])).

cnf(c_0,plain,
    ( k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X0,X1),k3_xboole_0(k2_tarski(X0,X1),k2_tarski(X0,X0)))) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_793,plain,
    ( k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(superposition,[status(thm)],[c_10,c_0])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X3),k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1)))))
    | X0 = X1
    | X0 = X2
    | X0 = X3 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_451,plain,
    ( X0 = X1
    | X0 = X2
    | X0 = X3
    | r2_hidden(X0,k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X3),k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1))))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_484,plain,
    ( X0 = X1
    | X2 = X1
    | X3 = X1
    | r2_hidden(X1,k2_enumset1(X3,X3,X0,X2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_451,c_10])).

cnf(c_1092,plain,
    ( X0 = X1
    | X2 = X1
    | r2_hidden(X1,k2_tarski(X2,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_793,c_484])).

cnf(c_2015,plain,
    ( sK2 = sK1 ),
    inference(superposition,[status(thm)],[c_961,c_1092])).

cnf(c_315,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_548,plain,
    ( sK2 != X0
    | sK1 != X0
    | sK1 = sK2 ),
    inference(instantiation,[status(thm)],[c_315])).

cnf(c_549,plain,
    ( sK2 != sK1
    | sK1 = sK2
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_548])).

cnf(c_8,plain,
    ( r2_hidden(X0,k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0))))) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_18,plain,
    ( r2_hidden(sK1,k5_xboole_0(k2_tarski(sK1,sK1),k5_xboole_0(k2_tarski(sK1,sK1),k3_xboole_0(k2_tarski(sK1,sK1),k2_tarski(sK1,sK1))))) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_15,plain,
    ( ~ r2_hidden(sK1,k5_xboole_0(k2_tarski(sK1,sK1),k5_xboole_0(k2_tarski(sK1,sK1),k3_xboole_0(k2_tarski(sK1,sK1),k2_tarski(sK1,sK1)))))
    | sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_11,negated_conjecture,
    ( sK1 != sK2 ),
    inference(cnf_transformation,[],[f36])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2015,c_549,c_18,c_15,c_11])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.33  % Computer   : n021.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % WCLimit    : 600
% 0.14/0.33  % DateTime   : Tue Dec  1 18:15:04 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 1.55/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.55/1.00  
% 1.55/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.55/1.00  
% 1.55/1.00  ------  iProver source info
% 1.55/1.00  
% 1.55/1.00  git: date: 2020-06-30 10:37:57 +0100
% 1.55/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.55/1.00  git: non_committed_changes: false
% 1.55/1.00  git: last_make_outside_of_git: false
% 1.55/1.00  
% 1.55/1.00  ------ 
% 1.55/1.00  
% 1.55/1.00  ------ Input Options
% 1.55/1.00  
% 1.55/1.00  --out_options                           all
% 1.55/1.00  --tptp_safe_out                         true
% 1.55/1.00  --problem_path                          ""
% 1.55/1.00  --include_path                          ""
% 1.55/1.00  --clausifier                            res/vclausify_rel
% 1.55/1.00  --clausifier_options                    --mode clausify
% 1.55/1.00  --stdin                                 false
% 1.55/1.00  --stats_out                             all
% 1.55/1.00  
% 1.55/1.00  ------ General Options
% 1.55/1.00  
% 1.55/1.00  --fof                                   false
% 1.55/1.00  --time_out_real                         305.
% 1.55/1.00  --time_out_virtual                      -1.
% 1.55/1.00  --symbol_type_check                     false
% 1.55/1.00  --clausify_out                          false
% 1.55/1.00  --sig_cnt_out                           false
% 1.55/1.00  --trig_cnt_out                          false
% 1.55/1.00  --trig_cnt_out_tolerance                1.
% 1.55/1.00  --trig_cnt_out_sk_spl                   false
% 1.55/1.00  --abstr_cl_out                          false
% 1.55/1.00  
% 1.55/1.00  ------ Global Options
% 1.55/1.00  
% 1.55/1.00  --schedule                              default
% 1.55/1.00  --add_important_lit                     false
% 1.55/1.00  --prop_solver_per_cl                    1000
% 1.55/1.00  --min_unsat_core                        false
% 1.55/1.00  --soft_assumptions                      false
% 1.55/1.00  --soft_lemma_size                       3
% 1.55/1.00  --prop_impl_unit_size                   0
% 1.55/1.00  --prop_impl_unit                        []
% 1.55/1.00  --share_sel_clauses                     true
% 1.55/1.00  --reset_solvers                         false
% 1.55/1.00  --bc_imp_inh                            [conj_cone]
% 1.55/1.00  --conj_cone_tolerance                   3.
% 1.55/1.00  --extra_neg_conj                        none
% 1.55/1.00  --large_theory_mode                     true
% 1.55/1.00  --prolific_symb_bound                   200
% 1.55/1.00  --lt_threshold                          2000
% 1.55/1.00  --clause_weak_htbl                      true
% 1.55/1.00  --gc_record_bc_elim                     false
% 1.55/1.00  
% 1.55/1.00  ------ Preprocessing Options
% 1.55/1.00  
% 1.55/1.00  --preprocessing_flag                    true
% 1.55/1.00  --time_out_prep_mult                    0.1
% 1.55/1.00  --splitting_mode                        input
% 1.55/1.00  --splitting_grd                         true
% 1.55/1.00  --splitting_cvd                         false
% 1.55/1.00  --splitting_cvd_svl                     false
% 1.55/1.00  --splitting_nvd                         32
% 1.55/1.00  --sub_typing                            true
% 1.55/1.00  --prep_gs_sim                           true
% 1.55/1.00  --prep_unflatten                        true
% 1.55/1.00  --prep_res_sim                          true
% 1.55/1.00  --prep_upred                            true
% 1.55/1.00  --prep_sem_filter                       exhaustive
% 1.55/1.00  --prep_sem_filter_out                   false
% 1.55/1.00  --pred_elim                             true
% 1.55/1.00  --res_sim_input                         true
% 1.55/1.00  --eq_ax_congr_red                       true
% 1.55/1.00  --pure_diseq_elim                       true
% 1.55/1.00  --brand_transform                       false
% 1.55/1.00  --non_eq_to_eq                          false
% 1.55/1.00  --prep_def_merge                        true
% 1.55/1.00  --prep_def_merge_prop_impl              false
% 1.55/1.00  --prep_def_merge_mbd                    true
% 1.55/1.00  --prep_def_merge_tr_red                 false
% 1.55/1.00  --prep_def_merge_tr_cl                  false
% 1.55/1.00  --smt_preprocessing                     true
% 1.55/1.00  --smt_ac_axioms                         fast
% 1.55/1.00  --preprocessed_out                      false
% 1.55/1.00  --preprocessed_stats                    false
% 1.55/1.00  
% 1.55/1.00  ------ Abstraction refinement Options
% 1.55/1.00  
% 1.55/1.00  --abstr_ref                             []
% 1.55/1.00  --abstr_ref_prep                        false
% 1.55/1.00  --abstr_ref_until_sat                   false
% 1.55/1.00  --abstr_ref_sig_restrict                funpre
% 1.55/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.55/1.00  --abstr_ref_under                       []
% 1.55/1.00  
% 1.55/1.00  ------ SAT Options
% 1.55/1.00  
% 1.55/1.00  --sat_mode                              false
% 1.55/1.00  --sat_fm_restart_options                ""
% 1.55/1.00  --sat_gr_def                            false
% 1.55/1.00  --sat_epr_types                         true
% 1.55/1.00  --sat_non_cyclic_types                  false
% 1.55/1.00  --sat_finite_models                     false
% 1.55/1.00  --sat_fm_lemmas                         false
% 1.55/1.00  --sat_fm_prep                           false
% 1.55/1.00  --sat_fm_uc_incr                        true
% 1.55/1.00  --sat_out_model                         small
% 1.55/1.00  --sat_out_clauses                       false
% 1.55/1.00  
% 1.55/1.00  ------ QBF Options
% 1.55/1.00  
% 1.55/1.00  --qbf_mode                              false
% 1.55/1.00  --qbf_elim_univ                         false
% 1.55/1.00  --qbf_dom_inst                          none
% 1.55/1.00  --qbf_dom_pre_inst                      false
% 1.55/1.00  --qbf_sk_in                             false
% 1.55/1.00  --qbf_pred_elim                         true
% 1.55/1.00  --qbf_split                             512
% 1.55/1.00  
% 1.55/1.00  ------ BMC1 Options
% 1.55/1.00  
% 1.55/1.00  --bmc1_incremental                      false
% 1.55/1.00  --bmc1_axioms                           reachable_all
% 1.55/1.00  --bmc1_min_bound                        0
% 1.55/1.00  --bmc1_max_bound                        -1
% 1.55/1.00  --bmc1_max_bound_default                -1
% 1.55/1.00  --bmc1_symbol_reachability              true
% 1.55/1.00  --bmc1_property_lemmas                  false
% 1.55/1.00  --bmc1_k_induction                      false
% 1.55/1.00  --bmc1_non_equiv_states                 false
% 1.55/1.00  --bmc1_deadlock                         false
% 1.55/1.00  --bmc1_ucm                              false
% 1.55/1.00  --bmc1_add_unsat_core                   none
% 1.55/1.00  --bmc1_unsat_core_children              false
% 1.55/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.55/1.00  --bmc1_out_stat                         full
% 1.55/1.00  --bmc1_ground_init                      false
% 1.55/1.00  --bmc1_pre_inst_next_state              false
% 1.55/1.00  --bmc1_pre_inst_state                   false
% 1.55/1.00  --bmc1_pre_inst_reach_state             false
% 1.55/1.00  --bmc1_out_unsat_core                   false
% 1.55/1.00  --bmc1_aig_witness_out                  false
% 1.55/1.00  --bmc1_verbose                          false
% 1.55/1.00  --bmc1_dump_clauses_tptp                false
% 1.55/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.55/1.00  --bmc1_dump_file                        -
% 1.55/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.55/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.55/1.00  --bmc1_ucm_extend_mode                  1
% 1.55/1.00  --bmc1_ucm_init_mode                    2
% 1.55/1.00  --bmc1_ucm_cone_mode                    none
% 1.55/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.55/1.00  --bmc1_ucm_relax_model                  4
% 1.55/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.55/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.55/1.00  --bmc1_ucm_layered_model                none
% 1.55/1.00  --bmc1_ucm_max_lemma_size               10
% 1.55/1.00  
% 1.55/1.00  ------ AIG Options
% 1.55/1.00  
% 1.55/1.00  --aig_mode                              false
% 1.55/1.00  
% 1.55/1.00  ------ Instantiation Options
% 1.55/1.00  
% 1.55/1.00  --instantiation_flag                    true
% 1.55/1.00  --inst_sos_flag                         false
% 1.55/1.00  --inst_sos_phase                        true
% 1.55/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.55/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.55/1.00  --inst_lit_sel_side                     num_symb
% 1.55/1.00  --inst_solver_per_active                1400
% 1.55/1.00  --inst_solver_calls_frac                1.
% 1.55/1.00  --inst_passive_queue_type               priority_queues
% 1.55/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.55/1.00  --inst_passive_queues_freq              [25;2]
% 1.55/1.00  --inst_dismatching                      true
% 1.55/1.00  --inst_eager_unprocessed_to_passive     true
% 1.55/1.00  --inst_prop_sim_given                   true
% 1.55/1.00  --inst_prop_sim_new                     false
% 1.55/1.00  --inst_subs_new                         false
% 1.55/1.00  --inst_eq_res_simp                      false
% 1.55/1.00  --inst_subs_given                       false
% 1.55/1.00  --inst_orphan_elimination               true
% 1.55/1.00  --inst_learning_loop_flag               true
% 1.55/1.00  --inst_learning_start                   3000
% 1.55/1.00  --inst_learning_factor                  2
% 1.55/1.00  --inst_start_prop_sim_after_learn       3
% 1.55/1.00  --inst_sel_renew                        solver
% 1.55/1.00  --inst_lit_activity_flag                true
% 1.55/1.00  --inst_restr_to_given                   false
% 1.55/1.00  --inst_activity_threshold               500
% 1.55/1.00  --inst_out_proof                        true
% 1.55/1.00  
% 1.55/1.00  ------ Resolution Options
% 1.55/1.00  
% 1.55/1.00  --resolution_flag                       true
% 1.55/1.00  --res_lit_sel                           adaptive
% 1.55/1.00  --res_lit_sel_side                      none
% 1.55/1.00  --res_ordering                          kbo
% 1.55/1.00  --res_to_prop_solver                    active
% 1.55/1.00  --res_prop_simpl_new                    false
% 1.55/1.00  --res_prop_simpl_given                  true
% 1.55/1.00  --res_passive_queue_type                priority_queues
% 1.55/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.55/1.00  --res_passive_queues_freq               [15;5]
% 1.55/1.00  --res_forward_subs                      full
% 1.55/1.00  --res_backward_subs                     full
% 1.55/1.00  --res_forward_subs_resolution           true
% 1.55/1.00  --res_backward_subs_resolution          true
% 1.55/1.00  --res_orphan_elimination                true
% 1.55/1.00  --res_time_limit                        2.
% 1.55/1.00  --res_out_proof                         true
% 1.55/1.00  
% 1.55/1.00  ------ Superposition Options
% 1.55/1.00  
% 1.55/1.00  --superposition_flag                    true
% 1.55/1.00  --sup_passive_queue_type                priority_queues
% 1.55/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.55/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.55/1.00  --demod_completeness_check              fast
% 1.55/1.00  --demod_use_ground                      true
% 1.55/1.00  --sup_to_prop_solver                    passive
% 1.55/1.00  --sup_prop_simpl_new                    true
% 1.55/1.00  --sup_prop_simpl_given                  true
% 1.55/1.00  --sup_fun_splitting                     false
% 1.55/1.00  --sup_smt_interval                      50000
% 1.55/1.00  
% 1.55/1.00  ------ Superposition Simplification Setup
% 1.55/1.00  
% 1.55/1.00  --sup_indices_passive                   []
% 1.55/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.55/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.55/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.55/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.55/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.55/1.00  --sup_full_bw                           [BwDemod]
% 1.55/1.00  --sup_immed_triv                        [TrivRules]
% 1.55/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.55/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.55/1.00  --sup_immed_bw_main                     []
% 1.55/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.55/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.55/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.55/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.55/1.00  
% 1.55/1.00  ------ Combination Options
% 1.55/1.00  
% 1.55/1.00  --comb_res_mult                         3
% 1.55/1.00  --comb_sup_mult                         2
% 1.55/1.00  --comb_inst_mult                        10
% 1.55/1.00  
% 1.55/1.00  ------ Debug Options
% 1.55/1.00  
% 1.55/1.00  --dbg_backtrace                         false
% 1.55/1.00  --dbg_dump_prop_clauses                 false
% 1.55/1.00  --dbg_dump_prop_clauses_file            -
% 1.55/1.00  --dbg_out_stat                          false
% 1.55/1.00  ------ Parsing...
% 1.55/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.55/1.00  
% 1.55/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 1.55/1.00  
% 1.55/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.55/1.00  
% 1.55/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.55/1.00  ------ Proving...
% 1.55/1.00  ------ Problem Properties 
% 1.55/1.00  
% 1.55/1.00  
% 1.55/1.00  clauses                                 13
% 1.55/1.00  conjectures                             2
% 1.55/1.00  EPR                                     1
% 1.55/1.00  Horn                                    11
% 1.55/1.00  unary                                   8
% 1.55/1.00  binary                                  0
% 1.55/1.00  lits                                    26
% 1.55/1.00  lits eq                                 18
% 1.55/1.00  fd_pure                                 0
% 1.55/1.00  fd_pseudo                               0
% 1.55/1.00  fd_cond                                 0
% 1.55/1.00  fd_pseudo_cond                          4
% 1.55/1.00  AC symbols                              0
% 1.55/1.00  
% 1.55/1.00  ------ Schedule dynamic 5 is on 
% 1.55/1.00  
% 1.55/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.55/1.00  
% 1.55/1.00  
% 1.55/1.00  ------ 
% 1.55/1.00  Current options:
% 1.55/1.00  ------ 
% 1.55/1.00  
% 1.55/1.00  ------ Input Options
% 1.55/1.00  
% 1.55/1.00  --out_options                           all
% 1.55/1.00  --tptp_safe_out                         true
% 1.55/1.00  --problem_path                          ""
% 1.55/1.00  --include_path                          ""
% 1.55/1.00  --clausifier                            res/vclausify_rel
% 1.55/1.00  --clausifier_options                    --mode clausify
% 1.55/1.00  --stdin                                 false
% 1.55/1.00  --stats_out                             all
% 1.55/1.00  
% 1.55/1.00  ------ General Options
% 1.55/1.00  
% 1.55/1.00  --fof                                   false
% 1.55/1.00  --time_out_real                         305.
% 1.55/1.00  --time_out_virtual                      -1.
% 1.55/1.00  --symbol_type_check                     false
% 1.55/1.00  --clausify_out                          false
% 1.55/1.00  --sig_cnt_out                           false
% 1.55/1.00  --trig_cnt_out                          false
% 1.55/1.00  --trig_cnt_out_tolerance                1.
% 1.55/1.00  --trig_cnt_out_sk_spl                   false
% 1.55/1.00  --abstr_cl_out                          false
% 1.55/1.00  
% 1.55/1.00  ------ Global Options
% 1.55/1.00  
% 1.55/1.00  --schedule                              default
% 1.55/1.00  --add_important_lit                     false
% 1.55/1.00  --prop_solver_per_cl                    1000
% 1.55/1.00  --min_unsat_core                        false
% 1.55/1.00  --soft_assumptions                      false
% 1.55/1.00  --soft_lemma_size                       3
% 1.55/1.00  --prop_impl_unit_size                   0
% 1.55/1.00  --prop_impl_unit                        []
% 1.55/1.00  --share_sel_clauses                     true
% 1.55/1.00  --reset_solvers                         false
% 1.55/1.00  --bc_imp_inh                            [conj_cone]
% 1.55/1.00  --conj_cone_tolerance                   3.
% 1.55/1.00  --extra_neg_conj                        none
% 1.55/1.00  --large_theory_mode                     true
% 1.55/1.00  --prolific_symb_bound                   200
% 1.55/1.00  --lt_threshold                          2000
% 1.55/1.00  --clause_weak_htbl                      true
% 1.55/1.00  --gc_record_bc_elim                     false
% 1.55/1.00  
% 1.55/1.00  ------ Preprocessing Options
% 1.55/1.00  
% 1.55/1.00  --preprocessing_flag                    true
% 1.55/1.00  --time_out_prep_mult                    0.1
% 1.55/1.00  --splitting_mode                        input
% 1.55/1.00  --splitting_grd                         true
% 1.55/1.00  --splitting_cvd                         false
% 1.55/1.00  --splitting_cvd_svl                     false
% 1.55/1.00  --splitting_nvd                         32
% 1.55/1.00  --sub_typing                            true
% 1.55/1.00  --prep_gs_sim                           true
% 1.55/1.00  --prep_unflatten                        true
% 1.55/1.00  --prep_res_sim                          true
% 1.55/1.00  --prep_upred                            true
% 1.55/1.00  --prep_sem_filter                       exhaustive
% 1.55/1.00  --prep_sem_filter_out                   false
% 1.55/1.00  --pred_elim                             true
% 1.55/1.00  --res_sim_input                         true
% 1.55/1.00  --eq_ax_congr_red                       true
% 1.55/1.00  --pure_diseq_elim                       true
% 1.55/1.00  --brand_transform                       false
% 1.55/1.00  --non_eq_to_eq                          false
% 1.55/1.00  --prep_def_merge                        true
% 1.55/1.00  --prep_def_merge_prop_impl              false
% 1.55/1.00  --prep_def_merge_mbd                    true
% 1.55/1.00  --prep_def_merge_tr_red                 false
% 1.55/1.00  --prep_def_merge_tr_cl                  false
% 1.55/1.00  --smt_preprocessing                     true
% 1.55/1.00  --smt_ac_axioms                         fast
% 1.55/1.00  --preprocessed_out                      false
% 1.55/1.00  --preprocessed_stats                    false
% 1.55/1.00  
% 1.55/1.00  ------ Abstraction refinement Options
% 1.55/1.00  
% 1.55/1.00  --abstr_ref                             []
% 1.55/1.00  --abstr_ref_prep                        false
% 1.55/1.00  --abstr_ref_until_sat                   false
% 1.55/1.00  --abstr_ref_sig_restrict                funpre
% 1.55/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.55/1.00  --abstr_ref_under                       []
% 1.55/1.00  
% 1.55/1.00  ------ SAT Options
% 1.55/1.00  
% 1.55/1.00  --sat_mode                              false
% 1.55/1.00  --sat_fm_restart_options                ""
% 1.55/1.00  --sat_gr_def                            false
% 1.55/1.00  --sat_epr_types                         true
% 1.55/1.00  --sat_non_cyclic_types                  false
% 1.55/1.00  --sat_finite_models                     false
% 1.55/1.00  --sat_fm_lemmas                         false
% 1.55/1.00  --sat_fm_prep                           false
% 1.55/1.00  --sat_fm_uc_incr                        true
% 1.55/1.00  --sat_out_model                         small
% 1.55/1.00  --sat_out_clauses                       false
% 1.55/1.00  
% 1.55/1.00  ------ QBF Options
% 1.55/1.00  
% 1.55/1.00  --qbf_mode                              false
% 1.55/1.00  --qbf_elim_univ                         false
% 1.55/1.00  --qbf_dom_inst                          none
% 1.55/1.00  --qbf_dom_pre_inst                      false
% 1.55/1.00  --qbf_sk_in                             false
% 1.55/1.00  --qbf_pred_elim                         true
% 1.55/1.00  --qbf_split                             512
% 1.55/1.00  
% 1.55/1.00  ------ BMC1 Options
% 1.55/1.00  
% 1.55/1.00  --bmc1_incremental                      false
% 1.55/1.00  --bmc1_axioms                           reachable_all
% 1.55/1.00  --bmc1_min_bound                        0
% 1.55/1.00  --bmc1_max_bound                        -1
% 1.55/1.00  --bmc1_max_bound_default                -1
% 1.55/1.00  --bmc1_symbol_reachability              true
% 1.55/1.00  --bmc1_property_lemmas                  false
% 1.55/1.01  --bmc1_k_induction                      false
% 1.55/1.01  --bmc1_non_equiv_states                 false
% 1.55/1.01  --bmc1_deadlock                         false
% 1.55/1.01  --bmc1_ucm                              false
% 1.55/1.01  --bmc1_add_unsat_core                   none
% 1.55/1.01  --bmc1_unsat_core_children              false
% 1.55/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 1.55/1.01  --bmc1_out_stat                         full
% 1.55/1.01  --bmc1_ground_init                      false
% 1.55/1.01  --bmc1_pre_inst_next_state              false
% 1.55/1.01  --bmc1_pre_inst_state                   false
% 1.55/1.01  --bmc1_pre_inst_reach_state             false
% 1.55/1.01  --bmc1_out_unsat_core                   false
% 1.55/1.01  --bmc1_aig_witness_out                  false
% 1.55/1.01  --bmc1_verbose                          false
% 1.55/1.01  --bmc1_dump_clauses_tptp                false
% 1.55/1.01  --bmc1_dump_unsat_core_tptp             false
% 1.55/1.01  --bmc1_dump_file                        -
% 1.55/1.01  --bmc1_ucm_expand_uc_limit              128
% 1.55/1.01  --bmc1_ucm_n_expand_iterations          6
% 1.55/1.01  --bmc1_ucm_extend_mode                  1
% 1.55/1.01  --bmc1_ucm_init_mode                    2
% 1.55/1.01  --bmc1_ucm_cone_mode                    none
% 1.55/1.01  --bmc1_ucm_reduced_relation_type        0
% 1.55/1.01  --bmc1_ucm_relax_model                  4
% 1.55/1.01  --bmc1_ucm_full_tr_after_sat            true
% 1.55/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 1.55/1.01  --bmc1_ucm_layered_model                none
% 1.55/1.01  --bmc1_ucm_max_lemma_size               10
% 1.55/1.01  
% 1.55/1.01  ------ AIG Options
% 1.55/1.01  
% 1.55/1.01  --aig_mode                              false
% 1.55/1.01  
% 1.55/1.01  ------ Instantiation Options
% 1.55/1.01  
% 1.55/1.01  --instantiation_flag                    true
% 1.55/1.01  --inst_sos_flag                         false
% 1.55/1.01  --inst_sos_phase                        true
% 1.55/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.55/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.55/1.01  --inst_lit_sel_side                     none
% 1.55/1.01  --inst_solver_per_active                1400
% 1.55/1.01  --inst_solver_calls_frac                1.
% 1.55/1.01  --inst_passive_queue_type               priority_queues
% 1.55/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.55/1.01  --inst_passive_queues_freq              [25;2]
% 1.55/1.01  --inst_dismatching                      true
% 1.55/1.01  --inst_eager_unprocessed_to_passive     true
% 1.55/1.01  --inst_prop_sim_given                   true
% 1.55/1.01  --inst_prop_sim_new                     false
% 1.55/1.01  --inst_subs_new                         false
% 1.55/1.01  --inst_eq_res_simp                      false
% 1.55/1.01  --inst_subs_given                       false
% 1.55/1.01  --inst_orphan_elimination               true
% 1.55/1.01  --inst_learning_loop_flag               true
% 1.55/1.01  --inst_learning_start                   3000
% 1.55/1.01  --inst_learning_factor                  2
% 1.55/1.01  --inst_start_prop_sim_after_learn       3
% 1.55/1.01  --inst_sel_renew                        solver
% 1.55/1.01  --inst_lit_activity_flag                true
% 1.55/1.01  --inst_restr_to_given                   false
% 1.55/1.01  --inst_activity_threshold               500
% 1.55/1.01  --inst_out_proof                        true
% 1.55/1.01  
% 1.55/1.01  ------ Resolution Options
% 1.55/1.01  
% 1.55/1.01  --resolution_flag                       false
% 1.55/1.01  --res_lit_sel                           adaptive
% 1.55/1.01  --res_lit_sel_side                      none
% 1.55/1.01  --res_ordering                          kbo
% 1.55/1.01  --res_to_prop_solver                    active
% 1.55/1.01  --res_prop_simpl_new                    false
% 1.55/1.01  --res_prop_simpl_given                  true
% 1.55/1.01  --res_passive_queue_type                priority_queues
% 1.55/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.55/1.01  --res_passive_queues_freq               [15;5]
% 1.55/1.01  --res_forward_subs                      full
% 1.55/1.01  --res_backward_subs                     full
% 1.55/1.01  --res_forward_subs_resolution           true
% 1.55/1.01  --res_backward_subs_resolution          true
% 1.55/1.01  --res_orphan_elimination                true
% 1.55/1.01  --res_time_limit                        2.
% 1.55/1.01  --res_out_proof                         true
% 1.55/1.01  
% 1.55/1.01  ------ Superposition Options
% 1.55/1.01  
% 1.55/1.01  --superposition_flag                    true
% 1.55/1.01  --sup_passive_queue_type                priority_queues
% 1.55/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.55/1.01  --sup_passive_queues_freq               [8;1;4]
% 1.55/1.01  --demod_completeness_check              fast
% 1.55/1.01  --demod_use_ground                      true
% 1.55/1.01  --sup_to_prop_solver                    passive
% 1.55/1.01  --sup_prop_simpl_new                    true
% 1.55/1.01  --sup_prop_simpl_given                  true
% 1.55/1.01  --sup_fun_splitting                     false
% 1.55/1.01  --sup_smt_interval                      50000
% 1.55/1.01  
% 1.55/1.01  ------ Superposition Simplification Setup
% 1.55/1.01  
% 1.55/1.01  --sup_indices_passive                   []
% 1.55/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.55/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.55/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.55/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 1.55/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.55/1.01  --sup_full_bw                           [BwDemod]
% 1.55/1.01  --sup_immed_triv                        [TrivRules]
% 1.55/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.55/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.55/1.01  --sup_immed_bw_main                     []
% 1.55/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.55/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 1.55/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.55/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.55/1.01  
% 1.55/1.01  ------ Combination Options
% 1.55/1.01  
% 1.55/1.01  --comb_res_mult                         3
% 1.55/1.01  --comb_sup_mult                         2
% 1.55/1.01  --comb_inst_mult                        10
% 1.55/1.01  
% 1.55/1.01  ------ Debug Options
% 1.55/1.01  
% 1.55/1.01  --dbg_backtrace                         false
% 1.55/1.01  --dbg_dump_prop_clauses                 false
% 1.55/1.01  --dbg_dump_prop_clauses_file            -
% 1.55/1.01  --dbg_out_stat                          false
% 1.55/1.01  
% 1.55/1.01  
% 1.55/1.01  
% 1.55/1.01  
% 1.55/1.01  ------ Proving...
% 1.55/1.01  
% 1.55/1.01  
% 1.55/1.01  % SZS status Theorem for theBenchmark.p
% 1.55/1.01  
% 1.55/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 1.55/1.01  
% 1.55/1.01  fof(f9,conjecture,(
% 1.55/1.01    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_xboole_0 => X0 = X1)),
% 1.55/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.55/1.01  
% 1.55/1.01  fof(f10,negated_conjecture,(
% 1.55/1.01    ~! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_xboole_0 => X0 = X1)),
% 1.55/1.01    inference(negated_conjecture,[],[f9])).
% 1.55/1.01  
% 1.55/1.01  fof(f12,plain,(
% 1.55/1.01    ? [X0,X1] : (X0 != X1 & k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_xboole_0)),
% 1.55/1.01    inference(ennf_transformation,[],[f10])).
% 1.55/1.01  
% 1.55/1.01  fof(f18,plain,(
% 1.55/1.01    ? [X0,X1] : (X0 != X1 & k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_xboole_0) => (sK1 != sK2 & k4_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) = k1_xboole_0)),
% 1.55/1.01    introduced(choice_axiom,[])).
% 1.55/1.01  
% 1.55/1.01  fof(f19,plain,(
% 1.55/1.01    sK1 != sK2 & k4_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) = k1_xboole_0),
% 1.55/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f12,f18])).
% 1.55/1.01  
% 1.55/1.01  fof(f35,plain,(
% 1.55/1.01    k4_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) = k1_xboole_0),
% 1.55/1.01    inference(cnf_transformation,[],[f19])).
% 1.55/1.01  
% 1.55/1.01  fof(f1,axiom,(
% 1.55/1.01    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.55/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.55/1.01  
% 1.55/1.01  fof(f20,plain,(
% 1.55/1.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.55/1.01    inference(cnf_transformation,[],[f1])).
% 1.55/1.01  
% 1.55/1.01  fof(f6,axiom,(
% 1.55/1.01    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.55/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.55/1.01  
% 1.55/1.01  fof(f32,plain,(
% 1.55/1.01    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.55/1.01    inference(cnf_transformation,[],[f6])).
% 1.55/1.01  
% 1.55/1.01  fof(f49,plain,(
% 1.55/1.01    k5_xboole_0(k2_tarski(sK1,sK1),k3_xboole_0(k2_tarski(sK1,sK1),k2_tarski(sK2,sK2))) = k1_xboole_0),
% 1.55/1.01    inference(definition_unfolding,[],[f35,f20,f32,f32])).
% 1.55/1.01  
% 1.55/1.01  fof(f8,axiom,(
% 1.55/1.01    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.55/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.55/1.01  
% 1.55/1.01  fof(f34,plain,(
% 1.55/1.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.55/1.01    inference(cnf_transformation,[],[f8])).
% 1.55/1.01  
% 1.55/1.01  fof(f5,axiom,(
% 1.55/1.01    ! [X0,X1,X2] : k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2)),
% 1.55/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.55/1.01  
% 1.55/1.01  fof(f31,plain,(
% 1.55/1.01    ( ! [X2,X0,X1] : (k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2)) )),
% 1.55/1.01    inference(cnf_transformation,[],[f5])).
% 1.55/1.01  
% 1.55/1.01  fof(f3,axiom,(
% 1.55/1.01    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 1.55/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.55/1.01  
% 1.55/1.01  fof(f22,plain,(
% 1.55/1.01    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 1.55/1.01    inference(cnf_transformation,[],[f3])).
% 1.55/1.01  
% 1.55/1.01  fof(f37,plain,(
% 1.55/1.01    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 1.55/1.01    inference(definition_unfolding,[],[f22,f20])).
% 1.55/1.01  
% 1.55/1.01  fof(f38,plain,(
% 1.55/1.01    ( ! [X2,X0,X1] : (k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))) = k1_enumset1(X0,X1,X2)) )),
% 1.55/1.01    inference(definition_unfolding,[],[f31,f37,f32])).
% 1.55/1.01  
% 1.55/1.01  fof(f48,plain,(
% 1.55/1.01    ( ! [X2,X0,X1] : (k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.55/1.01    inference(definition_unfolding,[],[f34,f38])).
% 1.55/1.01  
% 1.55/1.01  fof(f2,axiom,(
% 1.55/1.01    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.55/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.55/1.01  
% 1.55/1.01  fof(f21,plain,(
% 1.55/1.01    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.55/1.01    inference(cnf_transformation,[],[f2])).
% 1.55/1.01  
% 1.55/1.01  fof(f4,axiom,(
% 1.55/1.01    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.55/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.55/1.01  
% 1.55/1.01  fof(f11,plain,(
% 1.55/1.01    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.55/1.01    inference(ennf_transformation,[],[f4])).
% 1.55/1.01  
% 1.55/1.01  fof(f13,plain,(
% 1.55/1.01    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.55/1.01    inference(nnf_transformation,[],[f11])).
% 1.55/1.01  
% 1.55/1.01  fof(f14,plain,(
% 1.55/1.01    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.55/1.01    inference(flattening,[],[f13])).
% 1.55/1.01  
% 1.55/1.01  fof(f15,plain,(
% 1.55/1.01    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.55/1.01    inference(rectify,[],[f14])).
% 1.55/1.01  
% 1.55/1.01  fof(f16,plain,(
% 1.55/1.01    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3))))),
% 1.55/1.01    introduced(choice_axiom,[])).
% 1.55/1.01  
% 1.55/1.01  fof(f17,plain,(
% 1.55/1.01    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.55/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f16])).
% 1.55/1.01  
% 1.55/1.01  fof(f26,plain,(
% 1.55/1.01    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 1.55/1.01    inference(cnf_transformation,[],[f17])).
% 1.55/1.01  
% 1.55/1.01  fof(f44,plain,(
% 1.55/1.01    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))) != X3) )),
% 1.55/1.01    inference(definition_unfolding,[],[f26,f38])).
% 1.55/1.01  
% 1.55/1.01  fof(f50,plain,(
% 1.55/1.01    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X5),k3_xboole_0(k2_tarski(X1,X5),k2_tarski(X0,X0)))) != X3) )),
% 1.55/1.01    inference(equality_resolution,[],[f44])).
% 1.55/1.01  
% 1.55/1.01  fof(f51,plain,(
% 1.55/1.01    ( ! [X0,X5,X1] : (r2_hidden(X5,k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X5),k3_xboole_0(k2_tarski(X1,X5),k2_tarski(X0,X0)))))) )),
% 1.55/1.01    inference(equality_resolution,[],[f50])).
% 1.55/1.01  
% 1.55/1.01  fof(f7,axiom,(
% 1.55/1.01    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.55/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.55/1.01  
% 1.55/1.01  fof(f33,plain,(
% 1.55/1.01    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.55/1.01    inference(cnf_transformation,[],[f7])).
% 1.55/1.01  
% 1.55/1.01  fof(f39,plain,(
% 1.55/1.01    ( ! [X0,X1] : (k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X0,X1),k3_xboole_0(k2_tarski(X0,X1),k2_tarski(X0,X0)))) = k2_tarski(X0,X1)) )),
% 1.55/1.01    inference(definition_unfolding,[],[f33,f38])).
% 1.55/1.01  
% 1.55/1.01  fof(f23,plain,(
% 1.55/1.01    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 1.55/1.01    inference(cnf_transformation,[],[f17])).
% 1.55/1.01  
% 1.55/1.01  fof(f47,plain,(
% 1.55/1.01    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))) != X3) )),
% 1.55/1.01    inference(definition_unfolding,[],[f23,f38])).
% 1.55/1.01  
% 1.55/1.01  fof(f56,plain,(
% 1.55/1.01    ( ! [X2,X0,X5,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))))) )),
% 1.55/1.01    inference(equality_resolution,[],[f47])).
% 1.55/1.01  
% 1.55/1.01  fof(f24,plain,(
% 1.55/1.01    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 1.55/1.01    inference(cnf_transformation,[],[f17])).
% 1.55/1.01  
% 1.55/1.01  fof(f46,plain,(
% 1.55/1.01    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))) != X3) )),
% 1.55/1.01    inference(definition_unfolding,[],[f24,f38])).
% 1.55/1.01  
% 1.55/1.01  fof(f54,plain,(
% 1.55/1.01    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k5_xboole_0(k2_tarski(X5,X5),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X5,X5)))) != X3) )),
% 1.55/1.01    inference(equality_resolution,[],[f46])).
% 1.55/1.01  
% 1.55/1.01  fof(f55,plain,(
% 1.55/1.01    ( ! [X2,X5,X1] : (r2_hidden(X5,k5_xboole_0(k2_tarski(X5,X5),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X5,X5)))))) )),
% 1.55/1.01    inference(equality_resolution,[],[f54])).
% 1.55/1.01  
% 1.55/1.01  fof(f36,plain,(
% 1.55/1.01    sK1 != sK2),
% 1.55/1.01    inference(cnf_transformation,[],[f19])).
% 1.55/1.01  
% 1.55/1.01  cnf(c_12,negated_conjecture,
% 1.55/1.01      ( k5_xboole_0(k2_tarski(sK1,sK1),k3_xboole_0(k2_tarski(sK1,sK1),k2_tarski(sK2,sK2))) = k1_xboole_0 ),
% 1.55/1.01      inference(cnf_transformation,[],[f49]) ).
% 1.55/1.01  
% 1.55/1.01  cnf(c_10,plain,
% 1.55/1.01      ( k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))) = k2_enumset1(X0,X0,X1,X2) ),
% 1.55/1.01      inference(cnf_transformation,[],[f48]) ).
% 1.55/1.01  
% 1.55/1.01  cnf(c_792,plain,
% 1.55/1.01      ( k2_enumset1(sK2,sK2,sK1,sK1) = k5_xboole_0(k2_tarski(sK2,sK2),k1_xboole_0) ),
% 1.55/1.01      inference(superposition,[status(thm)],[c_12,c_10]) ).
% 1.55/1.01  
% 1.55/1.01  cnf(c_1,plain,
% 1.55/1.01      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 1.55/1.01      inference(cnf_transformation,[],[f21]) ).
% 1.55/1.01  
% 1.55/1.01  cnf(c_797,plain,
% 1.55/1.01      ( k2_enumset1(sK2,sK2,sK1,sK1) = k2_tarski(sK2,sK2) ),
% 1.55/1.01      inference(demodulation,[status(thm)],[c_792,c_1]) ).
% 1.55/1.01  
% 1.55/1.01  cnf(c_6,plain,
% 1.55/1.01      ( r2_hidden(X0,k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X0),k3_xboole_0(k2_tarski(X2,X0),k2_tarski(X1,X1))))) ),
% 1.55/1.01      inference(cnf_transformation,[],[f51]) ).
% 1.55/1.01  
% 1.55/1.01  cnf(c_454,plain,
% 1.55/1.01      ( r2_hidden(X0,k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X0),k3_xboole_0(k2_tarski(X2,X0),k2_tarski(X1,X1))))) = iProver_top ),
% 1.55/1.01      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 1.55/1.01  
% 1.55/1.01  cnf(c_475,plain,
% 1.55/1.01      ( r2_hidden(X0,k2_enumset1(X1,X1,X2,X0)) = iProver_top ),
% 1.55/1.01      inference(demodulation,[status(thm)],[c_10,c_454]) ).
% 1.55/1.01  
% 1.55/1.01  cnf(c_961,plain,
% 1.55/1.01      ( r2_hidden(sK1,k2_tarski(sK2,sK2)) = iProver_top ),
% 1.55/1.01      inference(superposition,[status(thm)],[c_797,c_475]) ).
% 1.55/1.01  
% 1.55/1.01  cnf(c_0,plain,
% 1.55/1.01      ( k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X0,X1),k3_xboole_0(k2_tarski(X0,X1),k2_tarski(X0,X0)))) = k2_tarski(X0,X1) ),
% 1.55/1.01      inference(cnf_transformation,[],[f39]) ).
% 1.55/1.01  
% 1.55/1.01  cnf(c_793,plain,
% 1.55/1.01      ( k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1) ),
% 1.55/1.01      inference(superposition,[status(thm)],[c_10,c_0]) ).
% 1.55/1.01  
% 1.55/1.01  cnf(c_9,plain,
% 1.55/1.01      ( ~ r2_hidden(X0,k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X3),k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1)))))
% 1.55/1.01      | X0 = X1
% 1.55/1.01      | X0 = X2
% 1.55/1.01      | X0 = X3 ),
% 1.55/1.01      inference(cnf_transformation,[],[f56]) ).
% 1.55/1.01  
% 1.55/1.01  cnf(c_451,plain,
% 1.55/1.01      ( X0 = X1
% 1.55/1.01      | X0 = X2
% 1.55/1.01      | X0 = X3
% 1.55/1.01      | r2_hidden(X0,k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X3),k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1))))) != iProver_top ),
% 1.55/1.01      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 1.55/1.01  
% 1.55/1.01  cnf(c_484,plain,
% 1.55/1.01      ( X0 = X1
% 1.55/1.01      | X2 = X1
% 1.55/1.01      | X3 = X1
% 1.55/1.01      | r2_hidden(X1,k2_enumset1(X3,X3,X0,X2)) != iProver_top ),
% 1.55/1.01      inference(demodulation,[status(thm)],[c_451,c_10]) ).
% 1.55/1.01  
% 1.55/1.01  cnf(c_1092,plain,
% 1.55/1.01      ( X0 = X1
% 1.55/1.01      | X2 = X1
% 1.55/1.01      | r2_hidden(X1,k2_tarski(X2,X0)) != iProver_top ),
% 1.55/1.01      inference(superposition,[status(thm)],[c_793,c_484]) ).
% 1.55/1.01  
% 1.55/1.01  cnf(c_2015,plain,
% 1.55/1.01      ( sK2 = sK1 ),
% 1.55/1.01      inference(superposition,[status(thm)],[c_961,c_1092]) ).
% 1.55/1.01  
% 1.55/1.01  cnf(c_315,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 1.55/1.01  
% 1.55/1.01  cnf(c_548,plain,
% 1.55/1.01      ( sK2 != X0 | sK1 != X0 | sK1 = sK2 ),
% 1.55/1.01      inference(instantiation,[status(thm)],[c_315]) ).
% 1.55/1.01  
% 1.55/1.01  cnf(c_549,plain,
% 1.55/1.01      ( sK2 != sK1 | sK1 = sK2 | sK1 != sK1 ),
% 1.55/1.01      inference(instantiation,[status(thm)],[c_548]) ).
% 1.55/1.01  
% 1.55/1.01  cnf(c_8,plain,
% 1.55/1.01      ( r2_hidden(X0,k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0))))) ),
% 1.55/1.01      inference(cnf_transformation,[],[f55]) ).
% 1.55/1.01  
% 1.55/1.01  cnf(c_18,plain,
% 1.55/1.01      ( r2_hidden(sK1,k5_xboole_0(k2_tarski(sK1,sK1),k5_xboole_0(k2_tarski(sK1,sK1),k3_xboole_0(k2_tarski(sK1,sK1),k2_tarski(sK1,sK1))))) ),
% 1.55/1.01      inference(instantiation,[status(thm)],[c_8]) ).
% 1.55/1.01  
% 1.55/1.01  cnf(c_15,plain,
% 1.55/1.01      ( ~ r2_hidden(sK1,k5_xboole_0(k2_tarski(sK1,sK1),k5_xboole_0(k2_tarski(sK1,sK1),k3_xboole_0(k2_tarski(sK1,sK1),k2_tarski(sK1,sK1)))))
% 1.55/1.01      | sK1 = sK1 ),
% 1.55/1.01      inference(instantiation,[status(thm)],[c_9]) ).
% 1.55/1.01  
% 1.55/1.01  cnf(c_11,negated_conjecture,
% 1.55/1.01      ( sK1 != sK2 ),
% 1.55/1.01      inference(cnf_transformation,[],[f36]) ).
% 1.55/1.01  
% 1.55/1.01  cnf(contradiction,plain,
% 1.55/1.01      ( $false ),
% 1.55/1.01      inference(minisat,[status(thm)],[c_2015,c_549,c_18,c_15,c_11]) ).
% 1.55/1.01  
% 1.55/1.01  
% 1.55/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 1.55/1.01  
% 1.55/1.01  ------                               Statistics
% 1.55/1.01  
% 1.55/1.01  ------ General
% 1.55/1.01  
% 1.55/1.01  abstr_ref_over_cycles:                  0
% 1.55/1.01  abstr_ref_under_cycles:                 0
% 1.55/1.01  gc_basic_clause_elim:                   0
% 1.55/1.01  forced_gc_time:                         0
% 1.55/1.01  parsing_time:                           0.006
% 1.55/1.01  unif_index_cands_time:                  0.
% 1.55/1.01  unif_index_add_time:                    0.
% 1.55/1.01  orderings_time:                         0.
% 1.55/1.01  out_proof_time:                         0.005
% 1.55/1.01  total_time:                             0.155
% 1.55/1.01  num_of_symbols:                         40
% 1.55/1.01  num_of_terms:                           4438
% 1.55/1.01  
% 1.55/1.01  ------ Preprocessing
% 1.55/1.01  
% 1.55/1.01  num_of_splits:                          0
% 1.55/1.01  num_of_split_atoms:                     0
% 1.55/1.01  num_of_reused_defs:                     0
% 1.55/1.01  num_eq_ax_congr_red:                    16
% 1.55/1.01  num_of_sem_filtered_clauses:            1
% 1.55/1.01  num_of_subtypes:                        0
% 1.55/1.01  monotx_restored_types:                  0
% 1.55/1.01  sat_num_of_epr_types:                   0
% 1.55/1.01  sat_num_of_non_cyclic_types:            0
% 1.55/1.01  sat_guarded_non_collapsed_types:        0
% 1.55/1.01  num_pure_diseq_elim:                    0
% 1.55/1.01  simp_replaced_by:                       0
% 1.55/1.01  res_preprocessed:                       52
% 1.55/1.01  prep_upred:                             0
% 1.55/1.01  prep_unflattend:                        14
% 1.55/1.01  smt_new_axioms:                         0
% 1.55/1.01  pred_elim_cands:                        1
% 1.55/1.01  pred_elim:                              0
% 1.55/1.01  pred_elim_cl:                           0
% 1.55/1.01  pred_elim_cycles:                       1
% 1.55/1.01  merged_defs:                            0
% 1.55/1.01  merged_defs_ncl:                        0
% 1.55/1.01  bin_hyper_res:                          0
% 1.55/1.01  prep_cycles:                            3
% 1.55/1.01  pred_elim_time:                         0.005
% 1.55/1.01  splitting_time:                         0.004
% 1.55/1.01  sem_filter_time:                        0.
% 1.55/1.01  monotx_time:                            0.
% 1.55/1.01  subtype_inf_time:                       0.
% 1.55/1.01  
% 1.55/1.01  ------ Problem properties
% 1.55/1.01  
% 1.55/1.01  clauses:                                13
% 1.55/1.01  conjectures:                            2
% 1.55/1.01  epr:                                    1
% 1.55/1.01  horn:                                   11
% 1.55/1.01  ground:                                 2
% 1.55/1.01  unary:                                  8
% 1.55/1.01  binary:                                 0
% 1.55/1.01  lits:                                   26
% 1.55/1.01  lits_eq:                                18
% 1.55/1.01  fd_pure:                                0
% 1.55/1.01  fd_pseudo:                              0
% 1.55/1.01  fd_cond:                                0
% 1.55/1.01  fd_pseudo_cond:                         4
% 1.55/1.01  ac_symbols:                             0
% 1.55/1.01  
% 1.55/1.01  ------ Propositional Solver
% 1.55/1.01  
% 1.55/1.01  prop_solver_calls:                      22
% 1.55/1.01  prop_fast_solver_calls:                 305
% 1.55/1.01  smt_solver_calls:                       0
% 1.55/1.01  smt_fast_solver_calls:                  0
% 1.55/1.01  prop_num_of_clauses:                    734
% 1.55/1.01  prop_preprocess_simplified:             2696
% 1.55/1.01  prop_fo_subsumed:                       0
% 1.55/1.01  prop_solver_time:                       0.
% 1.55/1.01  smt_solver_time:                        0.
% 1.55/1.01  smt_fast_solver_time:                   0.
% 1.55/1.01  prop_fast_solver_time:                  0.
% 1.55/1.01  prop_unsat_core_time:                   0.
% 1.55/1.01  
% 1.55/1.01  ------ QBF
% 1.55/1.01  
% 1.55/1.01  qbf_q_res:                              0
% 1.55/1.01  qbf_num_tautologies:                    0
% 1.55/1.01  qbf_prep_cycles:                        0
% 1.55/1.01  
% 1.55/1.01  ------ BMC1
% 1.55/1.01  
% 1.55/1.01  bmc1_current_bound:                     -1
% 1.55/1.01  bmc1_last_solved_bound:                 -1
% 1.55/1.01  bmc1_unsat_core_size:                   -1
% 1.55/1.01  bmc1_unsat_core_parents_size:           -1
% 1.55/1.01  bmc1_merge_next_fun:                    0
% 1.55/1.01  bmc1_unsat_core_clauses_time:           0.
% 1.55/1.01  
% 1.55/1.01  ------ Instantiation
% 1.55/1.01  
% 1.55/1.01  inst_num_of_clauses:                    266
% 1.55/1.01  inst_num_in_passive:                    79
% 1.55/1.01  inst_num_in_active:                     98
% 1.55/1.01  inst_num_in_unprocessed:                89
% 1.55/1.01  inst_num_of_loops:                      100
% 1.55/1.01  inst_num_of_learning_restarts:          0
% 1.55/1.01  inst_num_moves_active_passive:          0
% 1.55/1.01  inst_lit_activity:                      0
% 1.55/1.01  inst_lit_activity_moves:                0
% 1.55/1.01  inst_num_tautologies:                   0
% 1.55/1.01  inst_num_prop_implied:                  0
% 1.55/1.01  inst_num_existing_simplified:           0
% 1.55/1.01  inst_num_eq_res_simplified:             0
% 1.55/1.01  inst_num_child_elim:                    0
% 1.55/1.01  inst_num_of_dismatching_blockings:      126
% 1.55/1.01  inst_num_of_non_proper_insts:           265
% 1.55/1.01  inst_num_of_duplicates:                 0
% 1.55/1.01  inst_inst_num_from_inst_to_res:         0
% 1.55/1.01  inst_dismatching_checking_time:         0.
% 1.55/1.01  
% 1.55/1.01  ------ Resolution
% 1.55/1.01  
% 1.55/1.01  res_num_of_clauses:                     0
% 1.55/1.01  res_num_in_passive:                     0
% 1.55/1.01  res_num_in_active:                      0
% 1.55/1.01  res_num_of_loops:                       55
% 1.55/1.01  res_forward_subset_subsumed:            23
% 1.55/1.01  res_backward_subset_subsumed:           0
% 1.55/1.01  res_forward_subsumed:                   0
% 1.55/1.01  res_backward_subsumed:                  0
% 1.55/1.01  res_forward_subsumption_resolution:     0
% 1.55/1.01  res_backward_subsumption_resolution:    0
% 1.55/1.01  res_clause_to_clause_subsumption:       62
% 1.55/1.01  res_orphan_elimination:                 0
% 1.55/1.01  res_tautology_del:                      11
% 1.55/1.01  res_num_eq_res_simplified:              0
% 1.55/1.01  res_num_sel_changes:                    0
% 1.55/1.01  res_moves_from_active_to_pass:          0
% 1.55/1.01  
% 1.55/1.01  ------ Superposition
% 1.55/1.01  
% 1.55/1.01  sup_time_total:                         0.
% 1.55/1.01  sup_time_generating:                    0.
% 1.55/1.01  sup_time_sim_full:                      0.
% 1.55/1.01  sup_time_sim_immed:                     0.
% 1.55/1.01  
% 1.55/1.01  sup_num_of_clauses:                     23
% 1.55/1.01  sup_num_in_active:                      20
% 1.55/1.01  sup_num_in_passive:                     3
% 1.55/1.01  sup_num_of_loops:                       19
% 1.55/1.01  sup_fw_superposition:                   13
% 1.55/1.01  sup_bw_superposition:                   9
% 1.55/1.01  sup_immediate_simplified:               1
% 1.55/1.01  sup_given_eliminated:                   0
% 1.55/1.01  comparisons_done:                       0
% 1.55/1.01  comparisons_avoided:                    0
% 1.55/1.01  
% 1.55/1.01  ------ Simplifications
% 1.55/1.01  
% 1.55/1.01  
% 1.55/1.01  sim_fw_subset_subsumed:                 0
% 1.55/1.01  sim_bw_subset_subsumed:                 0
% 1.55/1.01  sim_fw_subsumed:                        0
% 1.55/1.01  sim_bw_subsumed:                        0
% 1.55/1.01  sim_fw_subsumption_res:                 0
% 1.55/1.01  sim_bw_subsumption_res:                 0
% 1.55/1.01  sim_tautology_del:                      0
% 1.55/1.01  sim_eq_tautology_del:                   8
% 1.55/1.01  sim_eq_res_simp:                        0
% 1.55/1.01  sim_fw_demodulated:                     6
% 1.55/1.01  sim_bw_demodulated:                     3
% 1.55/1.01  sim_light_normalised:                   0
% 1.55/1.01  sim_joinable_taut:                      0
% 1.55/1.01  sim_joinable_simp:                      0
% 1.55/1.01  sim_ac_normalised:                      0
% 1.55/1.01  sim_smt_subsumption:                    0
% 1.55/1.01  
%------------------------------------------------------------------------------
