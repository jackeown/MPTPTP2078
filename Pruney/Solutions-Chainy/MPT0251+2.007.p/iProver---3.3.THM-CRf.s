%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:33:02 EST 2020

% Result     : Theorem 11.99s
% Output     : CNFRefutation 11.99s
% Verified   : 
% Statistics : Number of formulae       :  122 (1089 expanded)
%              Number of clauses        :   56 ( 162 expanded)
%              Number of leaves         :   19 ( 334 expanded)
%              Depth                    :   19
%              Number of atoms          :  219 (1347 expanded)
%              Number of equality atoms :  114 (1069 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f20,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    inference(negated_conjecture,[],[f20])).

fof(f26,plain,(
    ? [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) != X1
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f39,plain,
    ( ? [X0,X1] :
        ( k2_xboole_0(k1_tarski(X0),X1) != X1
        & r2_hidden(X0,X1) )
   => ( k2_xboole_0(k1_tarski(sK2),sK3) != sK3
      & r2_hidden(sK2,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( k2_xboole_0(k1_tarski(sK2),sK3) != sK3
    & r2_hidden(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f26,f39])).

fof(f71,plain,(
    r2_hidden(sK2,sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f37])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f15,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f17])).

fof(f73,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f65,f66])).

fof(f74,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f64,f73])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f70,f74])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f13,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f83,plain,(
    ! [X0,X1] : k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f62,f74,f74])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f18,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f75,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f67,f74])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f78,plain,(
    ! [X0,X1] : k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f57,f75,f75,f54])).

fof(f10,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f79,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X1)) ),
    inference(definition_unfolding,[],[f58,f54,f54,f75])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f24,f32])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f81,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X0 ) ),
    inference(definition_unfolding,[],[f61,f54])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f82,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f60,f54])).

fof(f7,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f77,plain,(
    ! [X0] : k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f55,f75])).

fof(f11,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f80,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f59,f75])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f34])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f91,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f52])).

fof(f72,plain,(
    k2_xboole_0(k1_tarski(sK2),sK3) != sK3 ),
    inference(cnf_transformation,[],[f40])).

fof(f14,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f76,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f63,f74])).

fof(f87,plain,(
    k3_tarski(k3_enumset1(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK3)) != sK3 ),
    inference(definition_unfolding,[],[f72,f75,f76])).

cnf(c_25,negated_conjecture,
    ( r2_hidden(sK2,sK3) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1054,plain,
    ( r2_hidden(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_21,plain,
    ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1057,plain,
    ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2) = iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_14,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1061,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3481,plain,
    ( k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),X2) = k3_enumset1(X0,X0,X0,X0,X1)
    | r2_hidden(X1,X2) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1057,c_1061])).

cnf(c_46178,plain,
    ( k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,X0),sK3) = k3_enumset1(sK2,sK2,sK2,sK2,X0)
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1054,c_3481])).

cnf(c_48120,plain,
    ( k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK3) = k3_enumset1(sK2,sK2,sK2,sK2,sK2) ),
    inference(superposition,[status(thm)],[c_1054,c_46178])).

cnf(c_20,plain,
    ( k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_15,plain,
    ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_16,plain,
    ( k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X1)) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1662,plain,
    ( k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    inference(superposition,[status(thm)],[c_15,c_16])).

cnf(c_9,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1064,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_8,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK1(X0,X1),X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1065,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1663,plain,
    ( k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X0)) = k5_xboole_0(X1,k3_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_20,c_16])).

cnf(c_14754,plain,
    ( k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X0)) = k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),X0)) ),
    inference(superposition,[status(thm)],[c_15,c_1663])).

cnf(c_14783,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_14754,c_1663])).

cnf(c_18,plain,
    ( r1_xboole_0(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X0 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1059,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X0
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_15658,plain,
    ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_14783,c_1059])).

cnf(c_7,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X2,X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1066,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(X2,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_15697,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_15658,c_1066])).

cnf(c_16307,plain,
    ( r1_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = iProver_top
    | r2_hidden(sK1(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))),X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1065,c_15697])).

cnf(c_16335,plain,
    ( r1_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1064,c_16307])).

cnf(c_19,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1058,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_16681,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
    inference(superposition,[status(thm)],[c_16335,c_1058])).

cnf(c_28417,plain,
    ( k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1662,c_1662,c_16681])).

cnf(c_28439,plain,
    ( k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = X1 ),
    inference(superposition,[status(thm)],[c_20,c_28417])).

cnf(c_49378,plain,
    ( k5_xboole_0(k3_tarski(k3_enumset1(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK3)),k3_xboole_0(k3_tarski(k3_enumset1(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK3)),k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2)))) = sK3 ),
    inference(superposition,[status(thm)],[c_48120,c_28439])).

cnf(c_13,plain,
    ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1607,plain,
    ( k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_20,c_13])).

cnf(c_1704,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[status(thm)],[c_1607,c_16])).

cnf(c_17,plain,
    ( r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1060,plain,
    ( r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1390,plain,
    ( k3_xboole_0(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) = X0 ),
    inference(superposition,[status(thm)],[c_1060,c_1061])).

cnf(c_1706,plain,
    ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1607,c_1390])).

cnf(c_1708,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_1704,c_1706])).

cnf(c_11,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1062,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1389,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_1062,c_1061])).

cnf(c_1709,plain,
    ( k5_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_1708,c_1389])).

cnf(c_1971,plain,
    ( k5_xboole_0(X0,X0) = k5_xboole_0(X1,X1) ),
    inference(superposition,[status(thm)],[c_1709,c_1709])).

cnf(c_1973,plain,
    ( k5_xboole_0(X0,X0) = sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_1971])).

cnf(c_1703,plain,
    ( k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_1607,c_15])).

cnf(c_1710,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(demodulation,[status(thm)],[c_1703,c_1607])).

cnf(c_2064,plain,
    ( k5_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1389,c_1710])).

cnf(c_2068,plain,
    ( sP0_iProver_split = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2064,c_1973])).

cnf(c_2069,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,sP0_iProver_split)) = X0 ),
    inference(demodulation,[status(thm)],[c_2068,c_1710])).

cnf(c_49442,plain,
    ( k3_tarski(k3_enumset1(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK3)) = sK3 ),
    inference(demodulation,[status(thm)],[c_49378,c_1973,c_2069])).

cnf(c_24,negated_conjecture,
    ( k3_tarski(k3_enumset1(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK3)) != sK3 ),
    inference(cnf_transformation,[],[f87])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_49442,c_24])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:18:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 11.99/2.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.99/2.00  
% 11.99/2.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.99/2.00  
% 11.99/2.00  ------  iProver source info
% 11.99/2.00  
% 11.99/2.00  git: date: 2020-06-30 10:37:57 +0100
% 11.99/2.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.99/2.00  git: non_committed_changes: false
% 11.99/2.00  git: last_make_outside_of_git: false
% 11.99/2.00  
% 11.99/2.00  ------ 
% 11.99/2.00  
% 11.99/2.00  ------ Input Options
% 11.99/2.00  
% 11.99/2.00  --out_options                           all
% 11.99/2.00  --tptp_safe_out                         true
% 11.99/2.00  --problem_path                          ""
% 11.99/2.00  --include_path                          ""
% 11.99/2.00  --clausifier                            res/vclausify_rel
% 11.99/2.00  --clausifier_options                    ""
% 11.99/2.00  --stdin                                 false
% 11.99/2.00  --stats_out                             all
% 11.99/2.00  
% 11.99/2.00  ------ General Options
% 11.99/2.00  
% 11.99/2.00  --fof                                   false
% 11.99/2.00  --time_out_real                         305.
% 11.99/2.00  --time_out_virtual                      -1.
% 11.99/2.00  --symbol_type_check                     false
% 11.99/2.00  --clausify_out                          false
% 11.99/2.00  --sig_cnt_out                           false
% 11.99/2.00  --trig_cnt_out                          false
% 11.99/2.00  --trig_cnt_out_tolerance                1.
% 11.99/2.00  --trig_cnt_out_sk_spl                   false
% 11.99/2.00  --abstr_cl_out                          false
% 11.99/2.00  
% 11.99/2.00  ------ Global Options
% 11.99/2.00  
% 11.99/2.00  --schedule                              default
% 11.99/2.00  --add_important_lit                     false
% 11.99/2.00  --prop_solver_per_cl                    1000
% 11.99/2.00  --min_unsat_core                        false
% 11.99/2.00  --soft_assumptions                      false
% 11.99/2.00  --soft_lemma_size                       3
% 11.99/2.00  --prop_impl_unit_size                   0
% 11.99/2.00  --prop_impl_unit                        []
% 11.99/2.00  --share_sel_clauses                     true
% 11.99/2.00  --reset_solvers                         false
% 11.99/2.00  --bc_imp_inh                            [conj_cone]
% 11.99/2.00  --conj_cone_tolerance                   3.
% 11.99/2.00  --extra_neg_conj                        none
% 11.99/2.00  --large_theory_mode                     true
% 11.99/2.00  --prolific_symb_bound                   200
% 11.99/2.00  --lt_threshold                          2000
% 11.99/2.00  --clause_weak_htbl                      true
% 11.99/2.00  --gc_record_bc_elim                     false
% 11.99/2.00  
% 11.99/2.00  ------ Preprocessing Options
% 11.99/2.00  
% 11.99/2.00  --preprocessing_flag                    true
% 11.99/2.00  --time_out_prep_mult                    0.1
% 11.99/2.00  --splitting_mode                        input
% 11.99/2.00  --splitting_grd                         true
% 11.99/2.00  --splitting_cvd                         false
% 11.99/2.00  --splitting_cvd_svl                     false
% 11.99/2.00  --splitting_nvd                         32
% 11.99/2.00  --sub_typing                            true
% 11.99/2.00  --prep_gs_sim                           true
% 11.99/2.00  --prep_unflatten                        true
% 11.99/2.00  --prep_res_sim                          true
% 11.99/2.00  --prep_upred                            true
% 11.99/2.00  --prep_sem_filter                       exhaustive
% 11.99/2.00  --prep_sem_filter_out                   false
% 11.99/2.00  --pred_elim                             true
% 11.99/2.00  --res_sim_input                         true
% 11.99/2.00  --eq_ax_congr_red                       true
% 11.99/2.00  --pure_diseq_elim                       true
% 11.99/2.00  --brand_transform                       false
% 11.99/2.00  --non_eq_to_eq                          false
% 11.99/2.00  --prep_def_merge                        true
% 11.99/2.00  --prep_def_merge_prop_impl              false
% 11.99/2.00  --prep_def_merge_mbd                    true
% 11.99/2.00  --prep_def_merge_tr_red                 false
% 11.99/2.00  --prep_def_merge_tr_cl                  false
% 11.99/2.00  --smt_preprocessing                     true
% 11.99/2.00  --smt_ac_axioms                         fast
% 11.99/2.00  --preprocessed_out                      false
% 11.99/2.00  --preprocessed_stats                    false
% 11.99/2.00  
% 11.99/2.00  ------ Abstraction refinement Options
% 11.99/2.00  
% 11.99/2.00  --abstr_ref                             []
% 11.99/2.00  --abstr_ref_prep                        false
% 11.99/2.00  --abstr_ref_until_sat                   false
% 11.99/2.00  --abstr_ref_sig_restrict                funpre
% 11.99/2.00  --abstr_ref_af_restrict_to_split_sk     false
% 11.99/2.00  --abstr_ref_under                       []
% 11.99/2.00  
% 11.99/2.00  ------ SAT Options
% 11.99/2.00  
% 11.99/2.00  --sat_mode                              false
% 11.99/2.00  --sat_fm_restart_options                ""
% 11.99/2.00  --sat_gr_def                            false
% 11.99/2.00  --sat_epr_types                         true
% 11.99/2.00  --sat_non_cyclic_types                  false
% 11.99/2.00  --sat_finite_models                     false
% 11.99/2.00  --sat_fm_lemmas                         false
% 11.99/2.00  --sat_fm_prep                           false
% 11.99/2.00  --sat_fm_uc_incr                        true
% 11.99/2.00  --sat_out_model                         small
% 11.99/2.00  --sat_out_clauses                       false
% 11.99/2.00  
% 11.99/2.00  ------ QBF Options
% 11.99/2.00  
% 11.99/2.00  --qbf_mode                              false
% 11.99/2.00  --qbf_elim_univ                         false
% 11.99/2.00  --qbf_dom_inst                          none
% 11.99/2.00  --qbf_dom_pre_inst                      false
% 11.99/2.00  --qbf_sk_in                             false
% 11.99/2.00  --qbf_pred_elim                         true
% 11.99/2.00  --qbf_split                             512
% 11.99/2.00  
% 11.99/2.00  ------ BMC1 Options
% 11.99/2.00  
% 11.99/2.00  --bmc1_incremental                      false
% 11.99/2.00  --bmc1_axioms                           reachable_all
% 11.99/2.00  --bmc1_min_bound                        0
% 11.99/2.00  --bmc1_max_bound                        -1
% 11.99/2.00  --bmc1_max_bound_default                -1
% 11.99/2.00  --bmc1_symbol_reachability              true
% 11.99/2.00  --bmc1_property_lemmas                  false
% 11.99/2.00  --bmc1_k_induction                      false
% 11.99/2.00  --bmc1_non_equiv_states                 false
% 11.99/2.00  --bmc1_deadlock                         false
% 11.99/2.00  --bmc1_ucm                              false
% 11.99/2.00  --bmc1_add_unsat_core                   none
% 11.99/2.00  --bmc1_unsat_core_children              false
% 11.99/2.00  --bmc1_unsat_core_extrapolate_axioms    false
% 11.99/2.00  --bmc1_out_stat                         full
% 11.99/2.00  --bmc1_ground_init                      false
% 11.99/2.00  --bmc1_pre_inst_next_state              false
% 11.99/2.00  --bmc1_pre_inst_state                   false
% 11.99/2.00  --bmc1_pre_inst_reach_state             false
% 11.99/2.00  --bmc1_out_unsat_core                   false
% 11.99/2.00  --bmc1_aig_witness_out                  false
% 11.99/2.00  --bmc1_verbose                          false
% 11.99/2.00  --bmc1_dump_clauses_tptp                false
% 11.99/2.00  --bmc1_dump_unsat_core_tptp             false
% 11.99/2.00  --bmc1_dump_file                        -
% 11.99/2.00  --bmc1_ucm_expand_uc_limit              128
% 11.99/2.00  --bmc1_ucm_n_expand_iterations          6
% 11.99/2.00  --bmc1_ucm_extend_mode                  1
% 11.99/2.00  --bmc1_ucm_init_mode                    2
% 11.99/2.00  --bmc1_ucm_cone_mode                    none
% 11.99/2.00  --bmc1_ucm_reduced_relation_type        0
% 11.99/2.00  --bmc1_ucm_relax_model                  4
% 11.99/2.00  --bmc1_ucm_full_tr_after_sat            true
% 11.99/2.00  --bmc1_ucm_expand_neg_assumptions       false
% 11.99/2.00  --bmc1_ucm_layered_model                none
% 11.99/2.00  --bmc1_ucm_max_lemma_size               10
% 11.99/2.00  
% 11.99/2.00  ------ AIG Options
% 11.99/2.00  
% 11.99/2.00  --aig_mode                              false
% 11.99/2.00  
% 11.99/2.00  ------ Instantiation Options
% 11.99/2.00  
% 11.99/2.00  --instantiation_flag                    true
% 11.99/2.00  --inst_sos_flag                         true
% 11.99/2.00  --inst_sos_phase                        true
% 11.99/2.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.99/2.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.99/2.00  --inst_lit_sel_side                     num_symb
% 11.99/2.00  --inst_solver_per_active                1400
% 11.99/2.00  --inst_solver_calls_frac                1.
% 11.99/2.00  --inst_passive_queue_type               priority_queues
% 11.99/2.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.99/2.00  --inst_passive_queues_freq              [25;2]
% 11.99/2.00  --inst_dismatching                      true
% 11.99/2.00  --inst_eager_unprocessed_to_passive     true
% 11.99/2.00  --inst_prop_sim_given                   true
% 11.99/2.00  --inst_prop_sim_new                     false
% 11.99/2.00  --inst_subs_new                         false
% 11.99/2.00  --inst_eq_res_simp                      false
% 11.99/2.00  --inst_subs_given                       false
% 11.99/2.00  --inst_orphan_elimination               true
% 11.99/2.00  --inst_learning_loop_flag               true
% 11.99/2.00  --inst_learning_start                   3000
% 11.99/2.00  --inst_learning_factor                  2
% 11.99/2.00  --inst_start_prop_sim_after_learn       3
% 11.99/2.00  --inst_sel_renew                        solver
% 11.99/2.00  --inst_lit_activity_flag                true
% 11.99/2.00  --inst_restr_to_given                   false
% 11.99/2.00  --inst_activity_threshold               500
% 11.99/2.00  --inst_out_proof                        true
% 11.99/2.00  
% 11.99/2.00  ------ Resolution Options
% 11.99/2.00  
% 11.99/2.00  --resolution_flag                       true
% 11.99/2.00  --res_lit_sel                           adaptive
% 11.99/2.00  --res_lit_sel_side                      none
% 11.99/2.00  --res_ordering                          kbo
% 11.99/2.00  --res_to_prop_solver                    active
% 11.99/2.00  --res_prop_simpl_new                    false
% 11.99/2.00  --res_prop_simpl_given                  true
% 11.99/2.00  --res_passive_queue_type                priority_queues
% 11.99/2.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.99/2.00  --res_passive_queues_freq               [15;5]
% 11.99/2.00  --res_forward_subs                      full
% 11.99/2.00  --res_backward_subs                     full
% 11.99/2.00  --res_forward_subs_resolution           true
% 11.99/2.00  --res_backward_subs_resolution          true
% 11.99/2.00  --res_orphan_elimination                true
% 11.99/2.00  --res_time_limit                        2.
% 11.99/2.00  --res_out_proof                         true
% 11.99/2.00  
% 11.99/2.00  ------ Superposition Options
% 11.99/2.00  
% 11.99/2.00  --superposition_flag                    true
% 11.99/2.00  --sup_passive_queue_type                priority_queues
% 11.99/2.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.99/2.00  --sup_passive_queues_freq               [8;1;4]
% 11.99/2.00  --demod_completeness_check              fast
% 11.99/2.00  --demod_use_ground                      true
% 11.99/2.00  --sup_to_prop_solver                    passive
% 11.99/2.00  --sup_prop_simpl_new                    true
% 11.99/2.00  --sup_prop_simpl_given                  true
% 11.99/2.00  --sup_fun_splitting                     true
% 11.99/2.00  --sup_smt_interval                      50000
% 11.99/2.00  
% 11.99/2.00  ------ Superposition Simplification Setup
% 11.99/2.00  
% 11.99/2.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.99/2.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.99/2.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.99/2.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.99/2.00  --sup_full_triv                         [TrivRules;PropSubs]
% 11.99/2.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.99/2.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.99/2.00  --sup_immed_triv                        [TrivRules]
% 11.99/2.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.99/2.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.99/2.00  --sup_immed_bw_main                     []
% 11.99/2.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.99/2.00  --sup_input_triv                        [Unflattening;TrivRules]
% 11.99/2.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.99/2.00  --sup_input_bw                          []
% 11.99/2.00  
% 11.99/2.00  ------ Combination Options
% 11.99/2.00  
% 11.99/2.00  --comb_res_mult                         3
% 11.99/2.00  --comb_sup_mult                         2
% 11.99/2.00  --comb_inst_mult                        10
% 11.99/2.00  
% 11.99/2.00  ------ Debug Options
% 11.99/2.00  
% 11.99/2.00  --dbg_backtrace                         false
% 11.99/2.00  --dbg_dump_prop_clauses                 false
% 11.99/2.00  --dbg_dump_prop_clauses_file            -
% 11.99/2.00  --dbg_out_stat                          false
% 11.99/2.00  ------ Parsing...
% 11.99/2.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.99/2.00  
% 11.99/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 11.99/2.00  
% 11.99/2.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.99/2.00  
% 11.99/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.99/2.00  ------ Proving...
% 11.99/2.00  ------ Problem Properties 
% 11.99/2.00  
% 11.99/2.00  
% 11.99/2.00  clauses                                 25
% 11.99/2.00  conjectures                             2
% 11.99/2.00  EPR                                     5
% 11.99/2.00  Horn                                    21
% 11.99/2.00  unary                                   8
% 11.99/2.00  binary                                  10
% 11.99/2.00  lits                                    50
% 11.99/2.00  lits eq                                 12
% 11.99/2.00  fd_pure                                 0
% 11.99/2.00  fd_pseudo                               0
% 11.99/2.00  fd_cond                                 0
% 11.99/2.00  fd_pseudo_cond                          4
% 11.99/2.00  AC symbols                              0
% 11.99/2.00  
% 11.99/2.00  ------ Schedule dynamic 5 is on 
% 11.99/2.00  
% 11.99/2.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.99/2.00  
% 11.99/2.00  
% 11.99/2.00  ------ 
% 11.99/2.00  Current options:
% 11.99/2.00  ------ 
% 11.99/2.00  
% 11.99/2.00  ------ Input Options
% 11.99/2.00  
% 11.99/2.00  --out_options                           all
% 11.99/2.00  --tptp_safe_out                         true
% 11.99/2.00  --problem_path                          ""
% 11.99/2.00  --include_path                          ""
% 11.99/2.00  --clausifier                            res/vclausify_rel
% 11.99/2.00  --clausifier_options                    ""
% 11.99/2.00  --stdin                                 false
% 11.99/2.00  --stats_out                             all
% 11.99/2.00  
% 11.99/2.00  ------ General Options
% 11.99/2.00  
% 11.99/2.00  --fof                                   false
% 11.99/2.00  --time_out_real                         305.
% 11.99/2.00  --time_out_virtual                      -1.
% 11.99/2.00  --symbol_type_check                     false
% 11.99/2.00  --clausify_out                          false
% 11.99/2.00  --sig_cnt_out                           false
% 11.99/2.00  --trig_cnt_out                          false
% 11.99/2.00  --trig_cnt_out_tolerance                1.
% 11.99/2.00  --trig_cnt_out_sk_spl                   false
% 11.99/2.00  --abstr_cl_out                          false
% 11.99/2.00  
% 11.99/2.00  ------ Global Options
% 11.99/2.00  
% 11.99/2.00  --schedule                              default
% 11.99/2.00  --add_important_lit                     false
% 11.99/2.00  --prop_solver_per_cl                    1000
% 11.99/2.00  --min_unsat_core                        false
% 11.99/2.00  --soft_assumptions                      false
% 11.99/2.00  --soft_lemma_size                       3
% 11.99/2.00  --prop_impl_unit_size                   0
% 11.99/2.00  --prop_impl_unit                        []
% 11.99/2.00  --share_sel_clauses                     true
% 11.99/2.00  --reset_solvers                         false
% 11.99/2.00  --bc_imp_inh                            [conj_cone]
% 11.99/2.00  --conj_cone_tolerance                   3.
% 11.99/2.00  --extra_neg_conj                        none
% 11.99/2.00  --large_theory_mode                     true
% 11.99/2.00  --prolific_symb_bound                   200
% 11.99/2.00  --lt_threshold                          2000
% 11.99/2.00  --clause_weak_htbl                      true
% 11.99/2.00  --gc_record_bc_elim                     false
% 11.99/2.00  
% 11.99/2.00  ------ Preprocessing Options
% 11.99/2.00  
% 11.99/2.00  --preprocessing_flag                    true
% 11.99/2.00  --time_out_prep_mult                    0.1
% 11.99/2.00  --splitting_mode                        input
% 11.99/2.00  --splitting_grd                         true
% 11.99/2.00  --splitting_cvd                         false
% 11.99/2.00  --splitting_cvd_svl                     false
% 11.99/2.00  --splitting_nvd                         32
% 11.99/2.00  --sub_typing                            true
% 11.99/2.00  --prep_gs_sim                           true
% 11.99/2.00  --prep_unflatten                        true
% 11.99/2.00  --prep_res_sim                          true
% 11.99/2.00  --prep_upred                            true
% 11.99/2.00  --prep_sem_filter                       exhaustive
% 11.99/2.00  --prep_sem_filter_out                   false
% 11.99/2.00  --pred_elim                             true
% 11.99/2.00  --res_sim_input                         true
% 11.99/2.00  --eq_ax_congr_red                       true
% 11.99/2.00  --pure_diseq_elim                       true
% 11.99/2.00  --brand_transform                       false
% 11.99/2.00  --non_eq_to_eq                          false
% 11.99/2.00  --prep_def_merge                        true
% 11.99/2.00  --prep_def_merge_prop_impl              false
% 11.99/2.00  --prep_def_merge_mbd                    true
% 11.99/2.00  --prep_def_merge_tr_red                 false
% 11.99/2.00  --prep_def_merge_tr_cl                  false
% 11.99/2.00  --smt_preprocessing                     true
% 11.99/2.00  --smt_ac_axioms                         fast
% 11.99/2.00  --preprocessed_out                      false
% 11.99/2.00  --preprocessed_stats                    false
% 11.99/2.00  
% 11.99/2.00  ------ Abstraction refinement Options
% 11.99/2.00  
% 11.99/2.00  --abstr_ref                             []
% 11.99/2.00  --abstr_ref_prep                        false
% 11.99/2.00  --abstr_ref_until_sat                   false
% 11.99/2.00  --abstr_ref_sig_restrict                funpre
% 11.99/2.00  --abstr_ref_af_restrict_to_split_sk     false
% 11.99/2.00  --abstr_ref_under                       []
% 11.99/2.00  
% 11.99/2.00  ------ SAT Options
% 11.99/2.00  
% 11.99/2.00  --sat_mode                              false
% 11.99/2.00  --sat_fm_restart_options                ""
% 11.99/2.00  --sat_gr_def                            false
% 11.99/2.00  --sat_epr_types                         true
% 11.99/2.00  --sat_non_cyclic_types                  false
% 11.99/2.00  --sat_finite_models                     false
% 11.99/2.00  --sat_fm_lemmas                         false
% 11.99/2.00  --sat_fm_prep                           false
% 11.99/2.00  --sat_fm_uc_incr                        true
% 11.99/2.00  --sat_out_model                         small
% 11.99/2.00  --sat_out_clauses                       false
% 11.99/2.00  
% 11.99/2.00  ------ QBF Options
% 11.99/2.00  
% 11.99/2.00  --qbf_mode                              false
% 11.99/2.00  --qbf_elim_univ                         false
% 11.99/2.00  --qbf_dom_inst                          none
% 11.99/2.00  --qbf_dom_pre_inst                      false
% 11.99/2.00  --qbf_sk_in                             false
% 11.99/2.00  --qbf_pred_elim                         true
% 11.99/2.00  --qbf_split                             512
% 11.99/2.00  
% 11.99/2.00  ------ BMC1 Options
% 11.99/2.00  
% 11.99/2.00  --bmc1_incremental                      false
% 11.99/2.00  --bmc1_axioms                           reachable_all
% 11.99/2.00  --bmc1_min_bound                        0
% 11.99/2.00  --bmc1_max_bound                        -1
% 11.99/2.00  --bmc1_max_bound_default                -1
% 11.99/2.00  --bmc1_symbol_reachability              true
% 11.99/2.00  --bmc1_property_lemmas                  false
% 11.99/2.00  --bmc1_k_induction                      false
% 11.99/2.00  --bmc1_non_equiv_states                 false
% 11.99/2.00  --bmc1_deadlock                         false
% 11.99/2.00  --bmc1_ucm                              false
% 11.99/2.00  --bmc1_add_unsat_core                   none
% 11.99/2.00  --bmc1_unsat_core_children              false
% 11.99/2.00  --bmc1_unsat_core_extrapolate_axioms    false
% 11.99/2.00  --bmc1_out_stat                         full
% 11.99/2.00  --bmc1_ground_init                      false
% 11.99/2.00  --bmc1_pre_inst_next_state              false
% 11.99/2.00  --bmc1_pre_inst_state                   false
% 11.99/2.00  --bmc1_pre_inst_reach_state             false
% 11.99/2.00  --bmc1_out_unsat_core                   false
% 11.99/2.00  --bmc1_aig_witness_out                  false
% 11.99/2.00  --bmc1_verbose                          false
% 11.99/2.00  --bmc1_dump_clauses_tptp                false
% 11.99/2.00  --bmc1_dump_unsat_core_tptp             false
% 11.99/2.00  --bmc1_dump_file                        -
% 11.99/2.00  --bmc1_ucm_expand_uc_limit              128
% 11.99/2.00  --bmc1_ucm_n_expand_iterations          6
% 11.99/2.00  --bmc1_ucm_extend_mode                  1
% 11.99/2.00  --bmc1_ucm_init_mode                    2
% 11.99/2.00  --bmc1_ucm_cone_mode                    none
% 11.99/2.00  --bmc1_ucm_reduced_relation_type        0
% 11.99/2.00  --bmc1_ucm_relax_model                  4
% 11.99/2.00  --bmc1_ucm_full_tr_after_sat            true
% 11.99/2.00  --bmc1_ucm_expand_neg_assumptions       false
% 11.99/2.00  --bmc1_ucm_layered_model                none
% 11.99/2.00  --bmc1_ucm_max_lemma_size               10
% 11.99/2.00  
% 11.99/2.00  ------ AIG Options
% 11.99/2.00  
% 11.99/2.00  --aig_mode                              false
% 11.99/2.00  
% 11.99/2.00  ------ Instantiation Options
% 11.99/2.00  
% 11.99/2.00  --instantiation_flag                    true
% 11.99/2.00  --inst_sos_flag                         true
% 11.99/2.00  --inst_sos_phase                        true
% 11.99/2.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.99/2.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.99/2.00  --inst_lit_sel_side                     none
% 11.99/2.00  --inst_solver_per_active                1400
% 11.99/2.00  --inst_solver_calls_frac                1.
% 11.99/2.00  --inst_passive_queue_type               priority_queues
% 11.99/2.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.99/2.00  --inst_passive_queues_freq              [25;2]
% 11.99/2.00  --inst_dismatching                      true
% 11.99/2.00  --inst_eager_unprocessed_to_passive     true
% 11.99/2.00  --inst_prop_sim_given                   true
% 11.99/2.00  --inst_prop_sim_new                     false
% 11.99/2.00  --inst_subs_new                         false
% 11.99/2.00  --inst_eq_res_simp                      false
% 11.99/2.00  --inst_subs_given                       false
% 11.99/2.00  --inst_orphan_elimination               true
% 11.99/2.00  --inst_learning_loop_flag               true
% 11.99/2.00  --inst_learning_start                   3000
% 11.99/2.00  --inst_learning_factor                  2
% 11.99/2.00  --inst_start_prop_sim_after_learn       3
% 11.99/2.00  --inst_sel_renew                        solver
% 11.99/2.00  --inst_lit_activity_flag                true
% 11.99/2.00  --inst_restr_to_given                   false
% 11.99/2.00  --inst_activity_threshold               500
% 11.99/2.00  --inst_out_proof                        true
% 11.99/2.00  
% 11.99/2.00  ------ Resolution Options
% 11.99/2.00  
% 11.99/2.00  --resolution_flag                       false
% 11.99/2.00  --res_lit_sel                           adaptive
% 11.99/2.00  --res_lit_sel_side                      none
% 11.99/2.00  --res_ordering                          kbo
% 11.99/2.00  --res_to_prop_solver                    active
% 11.99/2.00  --res_prop_simpl_new                    false
% 11.99/2.00  --res_prop_simpl_given                  true
% 11.99/2.00  --res_passive_queue_type                priority_queues
% 11.99/2.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.99/2.00  --res_passive_queues_freq               [15;5]
% 11.99/2.00  --res_forward_subs                      full
% 11.99/2.00  --res_backward_subs                     full
% 11.99/2.00  --res_forward_subs_resolution           true
% 11.99/2.00  --res_backward_subs_resolution          true
% 11.99/2.00  --res_orphan_elimination                true
% 11.99/2.00  --res_time_limit                        2.
% 11.99/2.00  --res_out_proof                         true
% 11.99/2.00  
% 11.99/2.00  ------ Superposition Options
% 11.99/2.00  
% 11.99/2.00  --superposition_flag                    true
% 11.99/2.00  --sup_passive_queue_type                priority_queues
% 11.99/2.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.99/2.00  --sup_passive_queues_freq               [8;1;4]
% 11.99/2.00  --demod_completeness_check              fast
% 11.99/2.00  --demod_use_ground                      true
% 11.99/2.00  --sup_to_prop_solver                    passive
% 11.99/2.00  --sup_prop_simpl_new                    true
% 11.99/2.00  --sup_prop_simpl_given                  true
% 11.99/2.00  --sup_fun_splitting                     true
% 11.99/2.00  --sup_smt_interval                      50000
% 11.99/2.00  
% 11.99/2.00  ------ Superposition Simplification Setup
% 11.99/2.00  
% 11.99/2.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.99/2.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.99/2.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.99/2.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.99/2.00  --sup_full_triv                         [TrivRules;PropSubs]
% 11.99/2.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.99/2.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.99/2.00  --sup_immed_triv                        [TrivRules]
% 11.99/2.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.99/2.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.99/2.00  --sup_immed_bw_main                     []
% 11.99/2.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.99/2.00  --sup_input_triv                        [Unflattening;TrivRules]
% 11.99/2.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.99/2.00  --sup_input_bw                          []
% 11.99/2.00  
% 11.99/2.00  ------ Combination Options
% 11.99/2.00  
% 11.99/2.00  --comb_res_mult                         3
% 11.99/2.00  --comb_sup_mult                         2
% 11.99/2.00  --comb_inst_mult                        10
% 11.99/2.00  
% 11.99/2.00  ------ Debug Options
% 11.99/2.00  
% 11.99/2.00  --dbg_backtrace                         false
% 11.99/2.00  --dbg_dump_prop_clauses                 false
% 11.99/2.00  --dbg_dump_prop_clauses_file            -
% 11.99/2.00  --dbg_out_stat                          false
% 11.99/2.00  
% 11.99/2.00  
% 11.99/2.00  
% 11.99/2.00  
% 11.99/2.00  ------ Proving...
% 11.99/2.00  
% 11.99/2.00  
% 11.99/2.00  % SZS status Theorem for theBenchmark.p
% 11.99/2.00  
% 11.99/2.00  % SZS output start CNFRefutation for theBenchmark.p
% 11.99/2.00  
% 11.99/2.00  fof(f20,conjecture,(
% 11.99/2.00    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 11.99/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.99/2.00  
% 11.99/2.00  fof(f21,negated_conjecture,(
% 11.99/2.00    ~! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 11.99/2.00    inference(negated_conjecture,[],[f20])).
% 11.99/2.00  
% 11.99/2.00  fof(f26,plain,(
% 11.99/2.00    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1))),
% 11.99/2.00    inference(ennf_transformation,[],[f21])).
% 11.99/2.00  
% 11.99/2.00  fof(f39,plain,(
% 11.99/2.00    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1)) => (k2_xboole_0(k1_tarski(sK2),sK3) != sK3 & r2_hidden(sK2,sK3))),
% 11.99/2.00    introduced(choice_axiom,[])).
% 11.99/2.00  
% 11.99/2.00  fof(f40,plain,(
% 11.99/2.00    k2_xboole_0(k1_tarski(sK2),sK3) != sK3 & r2_hidden(sK2,sK3)),
% 11.99/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f26,f39])).
% 11.99/2.00  
% 11.99/2.00  fof(f71,plain,(
% 11.99/2.00    r2_hidden(sK2,sK3)),
% 11.99/2.00    inference(cnf_transformation,[],[f40])).
% 11.99/2.00  
% 11.99/2.00  fof(f19,axiom,(
% 11.99/2.00    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 11.99/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.99/2.00  
% 11.99/2.00  fof(f37,plain,(
% 11.99/2.00    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 11.99/2.00    inference(nnf_transformation,[],[f19])).
% 11.99/2.00  
% 11.99/2.00  fof(f38,plain,(
% 11.99/2.00    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 11.99/2.00    inference(flattening,[],[f37])).
% 11.99/2.00  
% 11.99/2.00  fof(f70,plain,(
% 11.99/2.00    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 11.99/2.00    inference(cnf_transformation,[],[f38])).
% 11.99/2.00  
% 11.99/2.00  fof(f15,axiom,(
% 11.99/2.00    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 11.99/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.99/2.00  
% 11.99/2.00  fof(f64,plain,(
% 11.99/2.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 11.99/2.00    inference(cnf_transformation,[],[f15])).
% 11.99/2.00  
% 11.99/2.00  fof(f16,axiom,(
% 11.99/2.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 11.99/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.99/2.00  
% 11.99/2.00  fof(f65,plain,(
% 11.99/2.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 11.99/2.00    inference(cnf_transformation,[],[f16])).
% 11.99/2.00  
% 11.99/2.00  fof(f17,axiom,(
% 11.99/2.00    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 11.99/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.99/2.00  
% 11.99/2.00  fof(f66,plain,(
% 11.99/2.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 11.99/2.00    inference(cnf_transformation,[],[f17])).
% 11.99/2.00  
% 11.99/2.00  fof(f73,plain,(
% 11.99/2.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 11.99/2.00    inference(definition_unfolding,[],[f65,f66])).
% 11.99/2.00  
% 11.99/2.00  fof(f74,plain,(
% 11.99/2.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 11.99/2.00    inference(definition_unfolding,[],[f64,f73])).
% 11.99/2.00  
% 11.99/2.00  fof(f84,plain,(
% 11.99/2.00    ( ! [X2,X0,X1] : (r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 11.99/2.00    inference(definition_unfolding,[],[f70,f74])).
% 11.99/2.00  
% 11.99/2.00  fof(f8,axiom,(
% 11.99/2.00    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 11.99/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.99/2.00  
% 11.99/2.00  fof(f25,plain,(
% 11.99/2.00    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 11.99/2.00    inference(ennf_transformation,[],[f8])).
% 11.99/2.00  
% 11.99/2.00  fof(f56,plain,(
% 11.99/2.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 11.99/2.00    inference(cnf_transformation,[],[f25])).
% 11.99/2.00  
% 11.99/2.00  fof(f13,axiom,(
% 11.99/2.00    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 11.99/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.99/2.00  
% 11.99/2.00  fof(f62,plain,(
% 11.99/2.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 11.99/2.00    inference(cnf_transformation,[],[f13])).
% 11.99/2.00  
% 11.99/2.00  fof(f83,plain,(
% 11.99/2.00    ( ! [X0,X1] : (k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0)) )),
% 11.99/2.00    inference(definition_unfolding,[],[f62,f74,f74])).
% 11.99/2.00  
% 11.99/2.00  fof(f9,axiom,(
% 11.99/2.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 11.99/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.99/2.00  
% 11.99/2.00  fof(f57,plain,(
% 11.99/2.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 11.99/2.00    inference(cnf_transformation,[],[f9])).
% 11.99/2.00  
% 11.99/2.00  fof(f18,axiom,(
% 11.99/2.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 11.99/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.99/2.00  
% 11.99/2.00  fof(f67,plain,(
% 11.99/2.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 11.99/2.00    inference(cnf_transformation,[],[f18])).
% 11.99/2.00  
% 11.99/2.00  fof(f75,plain,(
% 11.99/2.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 11.99/2.00    inference(definition_unfolding,[],[f67,f74])).
% 11.99/2.00  
% 11.99/2.00  fof(f6,axiom,(
% 11.99/2.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 11.99/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.99/2.00  
% 11.99/2.00  fof(f54,plain,(
% 11.99/2.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 11.99/2.00    inference(cnf_transformation,[],[f6])).
% 11.99/2.00  
% 11.99/2.00  fof(f78,plain,(
% 11.99/2.00    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) )),
% 11.99/2.00    inference(definition_unfolding,[],[f57,f75,f75,f54])).
% 11.99/2.00  
% 11.99/2.00  fof(f10,axiom,(
% 11.99/2.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 11.99/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.99/2.00  
% 11.99/2.00  fof(f58,plain,(
% 11.99/2.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 11.99/2.00    inference(cnf_transformation,[],[f10])).
% 11.99/2.00  
% 11.99/2.00  fof(f79,plain,(
% 11.99/2.00    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X1))) )),
% 11.99/2.00    inference(definition_unfolding,[],[f58,f54,f54,f75])).
% 11.99/2.00  
% 11.99/2.00  fof(f4,axiom,(
% 11.99/2.00    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 11.99/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.99/2.00  
% 11.99/2.00  fof(f22,plain,(
% 11.99/2.00    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 11.99/2.00    inference(rectify,[],[f4])).
% 11.99/2.00  
% 11.99/2.00  fof(f24,plain,(
% 11.99/2.00    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 11.99/2.00    inference(ennf_transformation,[],[f22])).
% 11.99/2.00  
% 11.99/2.00  fof(f32,plain,(
% 11.99/2.00    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 11.99/2.00    introduced(choice_axiom,[])).
% 11.99/2.00  
% 11.99/2.00  fof(f33,plain,(
% 11.99/2.00    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 11.99/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f24,f32])).
% 11.99/2.00  
% 11.99/2.00  fof(f48,plain,(
% 11.99/2.00    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 11.99/2.00    inference(cnf_transformation,[],[f33])).
% 11.99/2.00  
% 11.99/2.00  fof(f49,plain,(
% 11.99/2.00    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 11.99/2.00    inference(cnf_transformation,[],[f33])).
% 11.99/2.00  
% 11.99/2.00  fof(f12,axiom,(
% 11.99/2.00    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 11.99/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.99/2.00  
% 11.99/2.00  fof(f36,plain,(
% 11.99/2.00    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 11.99/2.00    inference(nnf_transformation,[],[f12])).
% 11.99/2.00  
% 11.99/2.00  fof(f61,plain,(
% 11.99/2.00    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 11.99/2.00    inference(cnf_transformation,[],[f36])).
% 11.99/2.00  
% 11.99/2.00  fof(f81,plain,(
% 11.99/2.00    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X0) )),
% 11.99/2.00    inference(definition_unfolding,[],[f61,f54])).
% 11.99/2.00  
% 11.99/2.00  fof(f50,plain,(
% 11.99/2.00    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 11.99/2.00    inference(cnf_transformation,[],[f33])).
% 11.99/2.00  
% 11.99/2.00  fof(f60,plain,(
% 11.99/2.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 11.99/2.00    inference(cnf_transformation,[],[f36])).
% 11.99/2.00  
% 11.99/2.00  fof(f82,plain,(
% 11.99/2.00    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 | ~r1_xboole_0(X0,X1)) )),
% 11.99/2.00    inference(definition_unfolding,[],[f60,f54])).
% 11.99/2.00  
% 11.99/2.00  fof(f7,axiom,(
% 11.99/2.00    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 11.99/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.99/2.00  
% 11.99/2.00  fof(f55,plain,(
% 11.99/2.00    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 11.99/2.00    inference(cnf_transformation,[],[f7])).
% 11.99/2.00  
% 11.99/2.00  fof(f77,plain,(
% 11.99/2.00    ( ! [X0] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0) )),
% 11.99/2.00    inference(definition_unfolding,[],[f55,f75])).
% 11.99/2.00  
% 11.99/2.00  fof(f11,axiom,(
% 11.99/2.00    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 11.99/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.99/2.00  
% 11.99/2.00  fof(f59,plain,(
% 11.99/2.00    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 11.99/2.00    inference(cnf_transformation,[],[f11])).
% 11.99/2.00  
% 11.99/2.00  fof(f80,plain,(
% 11.99/2.00    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))) )),
% 11.99/2.00    inference(definition_unfolding,[],[f59,f75])).
% 11.99/2.00  
% 11.99/2.00  fof(f5,axiom,(
% 11.99/2.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 11.99/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.99/2.00  
% 11.99/2.00  fof(f34,plain,(
% 11.99/2.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.99/2.00    inference(nnf_transformation,[],[f5])).
% 11.99/2.00  
% 11.99/2.00  fof(f35,plain,(
% 11.99/2.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.99/2.00    inference(flattening,[],[f34])).
% 11.99/2.00  
% 11.99/2.00  fof(f52,plain,(
% 11.99/2.00    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 11.99/2.00    inference(cnf_transformation,[],[f35])).
% 11.99/2.00  
% 11.99/2.00  fof(f91,plain,(
% 11.99/2.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 11.99/2.00    inference(equality_resolution,[],[f52])).
% 11.99/2.00  
% 11.99/2.00  fof(f72,plain,(
% 11.99/2.00    k2_xboole_0(k1_tarski(sK2),sK3) != sK3),
% 11.99/2.00    inference(cnf_transformation,[],[f40])).
% 11.99/2.00  
% 11.99/2.00  fof(f14,axiom,(
% 11.99/2.00    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 11.99/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.99/2.00  
% 11.99/2.00  fof(f63,plain,(
% 11.99/2.00    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 11.99/2.00    inference(cnf_transformation,[],[f14])).
% 11.99/2.00  
% 11.99/2.00  fof(f76,plain,(
% 11.99/2.00    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 11.99/2.00    inference(definition_unfolding,[],[f63,f74])).
% 11.99/2.00  
% 11.99/2.00  fof(f87,plain,(
% 11.99/2.00    k3_tarski(k3_enumset1(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK3)) != sK3),
% 11.99/2.00    inference(definition_unfolding,[],[f72,f75,f76])).
% 11.99/2.00  
% 11.99/2.00  cnf(c_25,negated_conjecture,
% 11.99/2.00      ( r2_hidden(sK2,sK3) ),
% 11.99/2.00      inference(cnf_transformation,[],[f71]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_1054,plain,
% 11.99/2.00      ( r2_hidden(sK2,sK3) = iProver_top ),
% 11.99/2.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_21,plain,
% 11.99/2.00      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2)
% 11.99/2.00      | ~ r2_hidden(X1,X2)
% 11.99/2.00      | ~ r2_hidden(X0,X2) ),
% 11.99/2.00      inference(cnf_transformation,[],[f84]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_1057,plain,
% 11.99/2.00      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2) = iProver_top
% 11.99/2.00      | r2_hidden(X0,X2) != iProver_top
% 11.99/2.00      | r2_hidden(X1,X2) != iProver_top ),
% 11.99/2.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_14,plain,
% 11.99/2.00      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 11.99/2.00      inference(cnf_transformation,[],[f56]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_1061,plain,
% 11.99/2.00      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 11.99/2.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_3481,plain,
% 11.99/2.00      ( k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),X2) = k3_enumset1(X0,X0,X0,X0,X1)
% 11.99/2.00      | r2_hidden(X1,X2) != iProver_top
% 11.99/2.00      | r2_hidden(X0,X2) != iProver_top ),
% 11.99/2.00      inference(superposition,[status(thm)],[c_1057,c_1061]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_46178,plain,
% 11.99/2.00      ( k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,X0),sK3) = k3_enumset1(sK2,sK2,sK2,sK2,X0)
% 11.99/2.00      | r2_hidden(X0,sK3) != iProver_top ),
% 11.99/2.00      inference(superposition,[status(thm)],[c_1054,c_3481]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_48120,plain,
% 11.99/2.00      ( k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK3) = k3_enumset1(sK2,sK2,sK2,sK2,sK2) ),
% 11.99/2.00      inference(superposition,[status(thm)],[c_1054,c_46178]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_20,plain,
% 11.99/2.00      ( k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) ),
% 11.99/2.00      inference(cnf_transformation,[],[f83]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_15,plain,
% 11.99/2.00      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
% 11.99/2.00      inference(cnf_transformation,[],[f78]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_16,plain,
% 11.99/2.00      ( k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X1)) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
% 11.99/2.00      inference(cnf_transformation,[],[f79]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_1662,plain,
% 11.99/2.00      ( k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
% 11.99/2.00      inference(superposition,[status(thm)],[c_15,c_16]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_9,plain,
% 11.99/2.00      ( r1_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 11.99/2.00      inference(cnf_transformation,[],[f48]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_1064,plain,
% 11.99/2.00      ( r1_xboole_0(X0,X1) = iProver_top
% 11.99/2.00      | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
% 11.99/2.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_8,plain,
% 11.99/2.00      ( r1_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),X1) ),
% 11.99/2.00      inference(cnf_transformation,[],[f49]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_1065,plain,
% 11.99/2.00      ( r1_xboole_0(X0,X1) = iProver_top
% 11.99/2.00      | r2_hidden(sK1(X0,X1),X1) = iProver_top ),
% 11.99/2.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_1663,plain,
% 11.99/2.00      ( k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X0)) = k5_xboole_0(X1,k3_xboole_0(X1,X0)) ),
% 11.99/2.00      inference(superposition,[status(thm)],[c_20,c_16]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_14754,plain,
% 11.99/2.00      ( k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X0)) = k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),X0)) ),
% 11.99/2.00      inference(superposition,[status(thm)],[c_15,c_1663]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_14783,plain,
% 11.99/2.00      ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
% 11.99/2.00      inference(demodulation,[status(thm)],[c_14754,c_1663]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_18,plain,
% 11.99/2.00      ( r1_xboole_0(X0,X1) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X0 ),
% 11.99/2.00      inference(cnf_transformation,[],[f81]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_1059,plain,
% 11.99/2.00      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X0
% 11.99/2.00      | r1_xboole_0(X0,X1) = iProver_top ),
% 11.99/2.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_15658,plain,
% 11.99/2.00      ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) = iProver_top ),
% 11.99/2.00      inference(superposition,[status(thm)],[c_14783,c_1059]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_7,plain,
% 11.99/2.00      ( ~ r1_xboole_0(X0,X1) | ~ r2_hidden(X2,X1) | ~ r2_hidden(X2,X0) ),
% 11.99/2.00      inference(cnf_transformation,[],[f50]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_1066,plain,
% 11.99/2.00      ( r1_xboole_0(X0,X1) != iProver_top
% 11.99/2.00      | r2_hidden(X2,X1) != iProver_top
% 11.99/2.00      | r2_hidden(X2,X0) != iProver_top ),
% 11.99/2.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_15697,plain,
% 11.99/2.00      ( r2_hidden(X0,X1) != iProver_top
% 11.99/2.00      | r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) != iProver_top ),
% 11.99/2.00      inference(superposition,[status(thm)],[c_15658,c_1066]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_16307,plain,
% 11.99/2.00      ( r1_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = iProver_top
% 11.99/2.00      | r2_hidden(sK1(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))),X2) != iProver_top ),
% 11.99/2.00      inference(superposition,[status(thm)],[c_1065,c_15697]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_16335,plain,
% 11.99/2.00      ( r1_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = iProver_top ),
% 11.99/2.00      inference(superposition,[status(thm)],[c_1064,c_16307]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_19,plain,
% 11.99/2.00      ( ~ r1_xboole_0(X0,X1) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
% 11.99/2.00      inference(cnf_transformation,[],[f82]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_1058,plain,
% 11.99/2.00      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0
% 11.99/2.00      | r1_xboole_0(X0,X1) != iProver_top ),
% 11.99/2.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_16681,plain,
% 11.99/2.00      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
% 11.99/2.00      inference(superposition,[status(thm)],[c_16335,c_1058]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_28417,plain,
% 11.99/2.00      ( k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
% 11.99/2.00      inference(light_normalisation,
% 11.99/2.00                [status(thm)],
% 11.99/2.00                [c_1662,c_1662,c_16681]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_28439,plain,
% 11.99/2.00      ( k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = X1 ),
% 11.99/2.00      inference(superposition,[status(thm)],[c_20,c_28417]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_49378,plain,
% 11.99/2.00      ( k5_xboole_0(k3_tarski(k3_enumset1(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK3)),k3_xboole_0(k3_tarski(k3_enumset1(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK3)),k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2)))) = sK3 ),
% 11.99/2.00      inference(superposition,[status(thm)],[c_48120,c_28439]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_13,plain,
% 11.99/2.00      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0 ),
% 11.99/2.00      inference(cnf_transformation,[],[f77]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_1607,plain,
% 11.99/2.00      ( k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0 ),
% 11.99/2.00      inference(superposition,[status(thm)],[c_20,c_13]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_1704,plain,
% 11.99/2.00      ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) ),
% 11.99/2.00      inference(superposition,[status(thm)],[c_1607,c_16]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_17,plain,
% 11.99/2.00      ( r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) ),
% 11.99/2.00      inference(cnf_transformation,[],[f80]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_1060,plain,
% 11.99/2.00      ( r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) = iProver_top ),
% 11.99/2.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_1390,plain,
% 11.99/2.00      ( k3_xboole_0(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) = X0 ),
% 11.99/2.00      inference(superposition,[status(thm)],[c_1060,c_1061]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_1706,plain,
% 11.99/2.00      ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 11.99/2.00      inference(superposition,[status(thm)],[c_1607,c_1390]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_1708,plain,
% 11.99/2.00      ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 11.99/2.00      inference(demodulation,[status(thm)],[c_1704,c_1706]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_11,plain,
% 11.99/2.00      ( r1_tarski(X0,X0) ),
% 11.99/2.00      inference(cnf_transformation,[],[f91]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_1062,plain,
% 11.99/2.00      ( r1_tarski(X0,X0) = iProver_top ),
% 11.99/2.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_1389,plain,
% 11.99/2.00      ( k3_xboole_0(X0,X0) = X0 ),
% 11.99/2.00      inference(superposition,[status(thm)],[c_1062,c_1061]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_1709,plain,
% 11.99/2.00      ( k5_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 11.99/2.00      inference(light_normalisation,[status(thm)],[c_1708,c_1389]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_1971,plain,
% 11.99/2.00      ( k5_xboole_0(X0,X0) = k5_xboole_0(X1,X1) ),
% 11.99/2.00      inference(superposition,[status(thm)],[c_1709,c_1709]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_1973,plain,
% 11.99/2.00      ( k5_xboole_0(X0,X0) = sP0_iProver_split ),
% 11.99/2.00      inference(splitting,
% 11.99/2.00                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 11.99/2.00                [c_1971]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_1703,plain,
% 11.99/2.00      ( k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) ),
% 11.99/2.00      inference(superposition,[status(thm)],[c_1607,c_15]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_1710,plain,
% 11.99/2.00      ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
% 11.99/2.00      inference(demodulation,[status(thm)],[c_1703,c_1607]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_2064,plain,
% 11.99/2.00      ( k5_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 11.99/2.00      inference(superposition,[status(thm)],[c_1389,c_1710]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_2068,plain,
% 11.99/2.00      ( sP0_iProver_split = k1_xboole_0 ),
% 11.99/2.00      inference(demodulation,[status(thm)],[c_2064,c_1973]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_2069,plain,
% 11.99/2.00      ( k5_xboole_0(X0,k3_xboole_0(X0,sP0_iProver_split)) = X0 ),
% 11.99/2.00      inference(demodulation,[status(thm)],[c_2068,c_1710]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_49442,plain,
% 11.99/2.00      ( k3_tarski(k3_enumset1(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK3)) = sK3 ),
% 11.99/2.00      inference(demodulation,[status(thm)],[c_49378,c_1973,c_2069]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_24,negated_conjecture,
% 11.99/2.00      ( k3_tarski(k3_enumset1(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK3)) != sK3 ),
% 11.99/2.00      inference(cnf_transformation,[],[f87]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(contradiction,plain,
% 11.99/2.00      ( $false ),
% 11.99/2.00      inference(minisat,[status(thm)],[c_49442,c_24]) ).
% 11.99/2.00  
% 11.99/2.00  
% 11.99/2.00  % SZS output end CNFRefutation for theBenchmark.p
% 11.99/2.00  
% 11.99/2.00  ------                               Statistics
% 11.99/2.00  
% 11.99/2.00  ------ General
% 11.99/2.00  
% 11.99/2.00  abstr_ref_over_cycles:                  0
% 11.99/2.00  abstr_ref_under_cycles:                 0
% 11.99/2.00  gc_basic_clause_elim:                   0
% 11.99/2.00  forced_gc_time:                         0
% 11.99/2.00  parsing_time:                           0.008
% 11.99/2.00  unif_index_cands_time:                  0.
% 11.99/2.00  unif_index_add_time:                    0.
% 11.99/2.00  orderings_time:                         0.
% 11.99/2.00  out_proof_time:                         0.014
% 11.99/2.00  total_time:                             1.438
% 11.99/2.00  num_of_symbols:                         44
% 11.99/2.00  num_of_terms:                           61762
% 11.99/2.00  
% 11.99/2.00  ------ Preprocessing
% 11.99/2.00  
% 11.99/2.00  num_of_splits:                          0
% 11.99/2.00  num_of_split_atoms:                     1
% 11.99/2.00  num_of_reused_defs:                     0
% 11.99/2.00  num_eq_ax_congr_red:                    24
% 11.99/2.00  num_of_sem_filtered_clauses:            1
% 11.99/2.00  num_of_subtypes:                        0
% 11.99/2.00  monotx_restored_types:                  0
% 11.99/2.00  sat_num_of_epr_types:                   0
% 11.99/2.00  sat_num_of_non_cyclic_types:            0
% 11.99/2.00  sat_guarded_non_collapsed_types:        0
% 11.99/2.00  num_pure_diseq_elim:                    0
% 11.99/2.00  simp_replaced_by:                       0
% 11.99/2.00  res_preprocessed:                       117
% 11.99/2.00  prep_upred:                             0
% 11.99/2.00  prep_unflattend:                        0
% 11.99/2.00  smt_new_axioms:                         0
% 11.99/2.00  pred_elim_cands:                        3
% 11.99/2.00  pred_elim:                              0
% 11.99/2.00  pred_elim_cl:                           0
% 11.99/2.00  pred_elim_cycles:                       2
% 11.99/2.00  merged_defs:                            8
% 11.99/2.00  merged_defs_ncl:                        0
% 11.99/2.00  bin_hyper_res:                          8
% 11.99/2.00  prep_cycles:                            4
% 11.99/2.00  pred_elim_time:                         0.001
% 11.99/2.00  splitting_time:                         0.
% 11.99/2.00  sem_filter_time:                        0.
% 11.99/2.00  monotx_time:                            0.
% 11.99/2.00  subtype_inf_time:                       0.
% 11.99/2.00  
% 11.99/2.00  ------ Problem properties
% 11.99/2.00  
% 11.99/2.00  clauses:                                25
% 11.99/2.00  conjectures:                            2
% 11.99/2.00  epr:                                    5
% 11.99/2.00  horn:                                   21
% 11.99/2.00  ground:                                 2
% 11.99/2.00  unary:                                  8
% 11.99/2.00  binary:                                 10
% 11.99/2.00  lits:                                   50
% 11.99/2.00  lits_eq:                                12
% 11.99/2.00  fd_pure:                                0
% 11.99/2.00  fd_pseudo:                              0
% 11.99/2.00  fd_cond:                                0
% 11.99/2.00  fd_pseudo_cond:                         4
% 11.99/2.00  ac_symbols:                             0
% 11.99/2.00  
% 11.99/2.00  ------ Propositional Solver
% 11.99/2.00  
% 11.99/2.00  prop_solver_calls:                      34
% 11.99/2.00  prop_fast_solver_calls:                 784
% 11.99/2.00  smt_solver_calls:                       0
% 11.99/2.00  smt_fast_solver_calls:                  0
% 11.99/2.00  prop_num_of_clauses:                    25374
% 11.99/2.00  prop_preprocess_simplified:             53054
% 11.99/2.00  prop_fo_subsumed:                       3
% 11.99/2.00  prop_solver_time:                       0.
% 11.99/2.00  smt_solver_time:                        0.
% 11.99/2.00  smt_fast_solver_time:                   0.
% 11.99/2.00  prop_fast_solver_time:                  0.
% 11.99/2.00  prop_unsat_core_time:                   0.004
% 11.99/2.00  
% 11.99/2.00  ------ QBF
% 11.99/2.00  
% 11.99/2.00  qbf_q_res:                              0
% 11.99/2.00  qbf_num_tautologies:                    0
% 11.99/2.00  qbf_prep_cycles:                        0
% 11.99/2.00  
% 11.99/2.00  ------ BMC1
% 11.99/2.00  
% 11.99/2.00  bmc1_current_bound:                     -1
% 11.99/2.00  bmc1_last_solved_bound:                 -1
% 11.99/2.00  bmc1_unsat_core_size:                   -1
% 11.99/2.00  bmc1_unsat_core_parents_size:           -1
% 11.99/2.00  bmc1_merge_next_fun:                    0
% 11.99/2.00  bmc1_unsat_core_clauses_time:           0.
% 11.99/2.00  
% 11.99/2.00  ------ Instantiation
% 11.99/2.00  
% 11.99/2.00  inst_num_of_clauses:                    7587
% 11.99/2.00  inst_num_in_passive:                    4818
% 11.99/2.00  inst_num_in_active:                     728
% 11.99/2.00  inst_num_in_unprocessed:                2042
% 11.99/2.00  inst_num_of_loops:                      770
% 11.99/2.00  inst_num_of_learning_restarts:          0
% 11.99/2.00  inst_num_moves_active_passive:          41
% 11.99/2.00  inst_lit_activity:                      0
% 11.99/2.00  inst_lit_activity_moves:                0
% 11.99/2.00  inst_num_tautologies:                   0
% 11.99/2.00  inst_num_prop_implied:                  0
% 11.99/2.00  inst_num_existing_simplified:           0
% 11.99/2.00  inst_num_eq_res_simplified:             0
% 11.99/2.00  inst_num_child_elim:                    0
% 11.99/2.00  inst_num_of_dismatching_blockings:      1761
% 11.99/2.00  inst_num_of_non_proper_insts:           4972
% 11.99/2.00  inst_num_of_duplicates:                 0
% 11.99/2.00  inst_inst_num_from_inst_to_res:         0
% 11.99/2.00  inst_dismatching_checking_time:         0.
% 11.99/2.00  
% 11.99/2.00  ------ Resolution
% 11.99/2.00  
% 11.99/2.00  res_num_of_clauses:                     0
% 11.99/2.00  res_num_in_passive:                     0
% 11.99/2.00  res_num_in_active:                      0
% 11.99/2.00  res_num_of_loops:                       121
% 11.99/2.00  res_forward_subset_subsumed:            204
% 11.99/2.00  res_backward_subset_subsumed:           2
% 11.99/2.00  res_forward_subsumed:                   0
% 11.99/2.00  res_backward_subsumed:                  0
% 11.99/2.00  res_forward_subsumption_resolution:     0
% 11.99/2.00  res_backward_subsumption_resolution:    0
% 11.99/2.00  res_clause_to_clause_subsumption:       3428
% 11.99/2.00  res_orphan_elimination:                 0
% 11.99/2.00  res_tautology_del:                      54
% 11.99/2.00  res_num_eq_res_simplified:              0
% 11.99/2.00  res_num_sel_changes:                    0
% 11.99/2.00  res_moves_from_active_to_pass:          0
% 11.99/2.00  
% 11.99/2.00  ------ Superposition
% 11.99/2.00  
% 11.99/2.00  sup_time_total:                         0.
% 11.99/2.00  sup_time_generating:                    0.
% 11.99/2.00  sup_time_sim_full:                      0.
% 11.99/2.00  sup_time_sim_immed:                     0.
% 11.99/2.00  
% 11.99/2.00  sup_num_of_clauses:                     364
% 11.99/2.00  sup_num_in_active:                      140
% 11.99/2.00  sup_num_in_passive:                     224
% 11.99/2.00  sup_num_of_loops:                       152
% 11.99/2.00  sup_fw_superposition:                   2063
% 11.99/2.00  sup_bw_superposition:                   1306
% 11.99/2.00  sup_immediate_simplified:               1477
% 11.99/2.00  sup_given_eliminated:                   2
% 11.99/2.00  comparisons_done:                       0
% 11.99/2.00  comparisons_avoided:                    0
% 11.99/2.00  
% 11.99/2.00  ------ Simplifications
% 11.99/2.00  
% 11.99/2.00  
% 11.99/2.00  sim_fw_subset_subsumed:                 32
% 11.99/2.00  sim_bw_subset_subsumed:                 2
% 11.99/2.00  sim_fw_subsumed:                        273
% 11.99/2.00  sim_bw_subsumed:                        1
% 11.99/2.00  sim_fw_subsumption_res:                 0
% 11.99/2.00  sim_bw_subsumption_res:                 0
% 11.99/2.00  sim_tautology_del:                      47
% 11.99/2.00  sim_eq_tautology_del:                   242
% 11.99/2.00  sim_eq_res_simp:                        22
% 11.99/2.00  sim_fw_demodulated:                     1047
% 11.99/2.00  sim_bw_demodulated:                     14
% 11.99/2.00  sim_light_normalised:                   448
% 11.99/2.00  sim_joinable_taut:                      0
% 11.99/2.00  sim_joinable_simp:                      0
% 11.99/2.00  sim_ac_normalised:                      0
% 11.99/2.00  sim_smt_subsumption:                    0
% 11.99/2.00  
%------------------------------------------------------------------------------
