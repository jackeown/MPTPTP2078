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
% DateTime   : Thu Dec  3 11:35:37 EST 2020

% Result     : Theorem 3.68s
% Output     : CNFRefutation 3.68s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 306 expanded)
%              Number of clauses        :   33 (  66 expanded)
%              Number of leaves         :   18 (  87 expanded)
%              Depth                    :   13
%              Number of atoms          :  146 ( 429 expanded)
%              Number of equality atoms :   80 ( 302 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f10,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f13])).

fof(f46,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f39,f40])).

fof(f47,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f38,f46])).

fof(f49,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f37,f47])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f42,f49])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => k4_xboole_0(k2_xboole_0(X2,X1),X0) = k2_xboole_0(k4_xboole_0(X2,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(k2_xboole_0(X2,X1),X0) = k2_xboole_0(k4_xboole_0(X2,X0),X1)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(k2_xboole_0(X2,X1),X0) = k2_xboole_0(k4_xboole_0(X2,X0),X1)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f16,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f48,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f43,f47])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(k3_tarski(k3_enumset1(X2,X2,X2,X2,X1)),k3_xboole_0(k3_tarski(k3_enumset1(X2,X2,X2,X2,X1)),X0)) = k3_tarski(k3_enumset1(k5_xboole_0(X2,k3_xboole_0(X2,X0)),k5_xboole_0(X2,k3_xboole_0(X2,X0)),k5_xboole_0(X2,k3_xboole_0(X2,X0)),k5_xboole_0(X2,k3_xboole_0(X2,X0)),X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f36,f30,f48,f48,f30])).

fof(f17,conjecture,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      <=> ~ r2_hidden(X1,X0) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f24,plain,(
    ? [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <~> ~ r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f25,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) = X0 ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f26,plain,
    ( ? [X0,X1] :
        ( ( r2_hidden(X1,X0)
          | k4_xboole_0(X0,k1_tarski(X1)) != X0 )
        & ( ~ r2_hidden(X1,X0)
          | k4_xboole_0(X0,k1_tarski(X1)) = X0 ) )
   => ( ( r2_hidden(sK1,sK0)
        | k4_xboole_0(sK0,k1_tarski(sK1)) != sK0 )
      & ( ~ r2_hidden(sK1,sK0)
        | k4_xboole_0(sK0,k1_tarski(sK1)) = sK0 ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ( r2_hidden(sK1,sK0)
      | k4_xboole_0(sK0,k1_tarski(sK1)) != sK0 )
    & ( ~ r2_hidden(sK1,sK0)
      | k4_xboole_0(sK0,k1_tarski(sK1)) = sK0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f26])).

fof(f44,plain,
    ( ~ r2_hidden(sK1,sK0)
    | k4_xboole_0(sK0,k1_tarski(sK1)) = sK0 ),
    inference(cnf_transformation,[],[f27])).

fof(f56,plain,
    ( ~ r2_hidden(sK1,sK0)
    | k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) = sK0 ),
    inference(definition_unfolding,[],[f44,f30,f49])).

fof(f7,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f50,plain,(
    ! [X0,X1] : k3_tarski(k3_enumset1(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = X0 ),
    inference(definition_unfolding,[],[f33,f48,f30])).

fof(f8,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f51,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(definition_unfolding,[],[f35,f30])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f14,axiom,(
    ! [X0,X1] :
      ~ ( r2_hidden(X0,X1)
        & r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) ) ),
    inference(definition_unfolding,[],[f41,f49])).

fof(f45,plain,
    ( r2_hidden(sK1,sK0)
    | k4_xboole_0(sK0,k1_tarski(sK1)) != sK0 ),
    inference(cnf_transformation,[],[f27])).

fof(f55,plain,
    ( r2_hidden(sK1,sK0)
    | k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) != sK0 ),
    inference(definition_unfolding,[],[f45,f30,f49])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_414,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_415,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_693,plain,
    ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_414,c_415])).

cnf(c_9,plain,
    ( r2_hidden(X0,X1)
    | r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_410,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_7,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_tarski(k3_enumset1(k5_xboole_0(X2,k3_xboole_0(X2,X0)),k5_xboole_0(X2,k3_xboole_0(X2,X0)),k5_xboole_0(X2,k3_xboole_0(X2,X0)),k5_xboole_0(X2,k3_xboole_0(X2,X0)),X1)) = k5_xboole_0(k3_tarski(k3_enumset1(X2,X2,X2,X2,X1)),k3_xboole_0(k3_tarski(k3_enumset1(X2,X2,X2,X2,X1)),X0)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_412,plain,
    ( k3_tarski(k3_enumset1(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2)) = k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X2)),k3_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X2)),X1))
    | r1_xboole_0(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1656,plain,
    ( k3_tarski(k3_enumset1(k5_xboole_0(X0,k3_xboole_0(X0,k3_enumset1(X1,X1,X1,X1,X1))),k5_xboole_0(X0,k3_xboole_0(X0,k3_enumset1(X1,X1,X1,X1,X1))),k5_xboole_0(X0,k3_xboole_0(X0,k3_enumset1(X1,X1,X1,X1,X1))),k5_xboole_0(X0,k3_xboole_0(X0,k3_enumset1(X1,X1,X1,X1,X1))),X2)) = k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X2)),k3_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X2)),k3_enumset1(X1,X1,X1,X1,X1)))
    | r2_hidden(X1,X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_410,c_412])).

cnf(c_11,negated_conjecture,
    ( ~ r2_hidden(sK1,sK0)
    | k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) = sK0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_408,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) = sK0
    | r2_hidden(sK1,sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_4800,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) = sK0
    | k3_tarski(k3_enumset1(k5_xboole_0(X0,k3_xboole_0(X0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))),k5_xboole_0(X0,k3_xboole_0(X0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))),k5_xboole_0(X0,k3_xboole_0(X0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))),k5_xboole_0(X0,k3_xboole_0(X0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))),sK0)) = k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,sK0)),k3_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,sK0)),k3_enumset1(sK1,sK1,sK1,sK1,sK1))) ),
    inference(superposition,[status(thm)],[c_1656,c_408])).

cnf(c_5640,plain,
    ( k5_xboole_0(k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK0)),k3_xboole_0(k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK0)),k3_enumset1(sK1,sK1,sK1,sK1,sK1))) = k3_tarski(k3_enumset1(k5_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k1_xboole_0,k1_xboole_0),sK0))
    | k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) = sK0 ),
    inference(superposition,[status(thm)],[c_693,c_4800])).

cnf(c_5,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_4,plain,
    ( k3_tarski(k3_enumset1(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_803,plain,
    ( k3_tarski(k3_enumset1(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k5_xboole_0(X1,k3_xboole_0(X0,X1)))) = X1 ),
    inference(superposition,[status(thm)],[c_0,c_4])).

cnf(c_1100,plain,
    ( k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k5_xboole_0(X0,k1_xboole_0))) = X0 ),
    inference(superposition,[status(thm)],[c_693,c_803])).

cnf(c_1126,plain,
    ( k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1100,c_5])).

cnf(c_5643,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) = sK0 ),
    inference(demodulation,[status(thm)],[c_5640,c_5,c_1126])).

cnf(c_6,plain,
    ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_413,plain,
    ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_5925,plain,
    ( r1_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5643,c_413])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_1618,plain,
    ( r1_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK0)
    | ~ r1_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1629,plain,
    ( r1_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK0) = iProver_top
    | r1_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1618])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_572,plain,
    ( ~ r2_hidden(sK1,sK0)
    | ~ r1_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK0) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_573,plain,
    ( r2_hidden(sK1,sK0) != iProver_top
    | r1_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_572])).

cnf(c_10,negated_conjecture,
    ( r2_hidden(sK1,sK0)
    | k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) != sK0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_13,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) != sK0
    | r2_hidden(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5925,c_5643,c_1629,c_573,c_13])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.11/0.33  % Computer   : n005.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 18:46:32 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.18/0.33  % Running in FOF mode
% 3.68/0.97  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.68/0.97  
% 3.68/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.68/0.97  
% 3.68/0.97  ------  iProver source info
% 3.68/0.97  
% 3.68/0.97  git: date: 2020-06-30 10:37:57 +0100
% 3.68/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.68/0.97  git: non_committed_changes: false
% 3.68/0.97  git: last_make_outside_of_git: false
% 3.68/0.97  
% 3.68/0.97  ------ 
% 3.68/0.97  ------ Parsing...
% 3.68/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.68/0.97  
% 3.68/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.68/0.97  
% 3.68/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.68/0.97  
% 3.68/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.68/0.97  ------ Proving...
% 3.68/0.97  ------ Problem Properties 
% 3.68/0.97  
% 3.68/0.97  
% 3.68/0.97  clauses                                 12
% 3.68/0.97  conjectures                             2
% 3.68/0.97  EPR                                     2
% 3.68/0.97  Horn                                    11
% 3.68/0.97  unary                                   5
% 3.68/0.97  binary                                  7
% 3.68/0.97  lits                                    19
% 3.68/0.97  lits eq                                 7
% 3.68/0.97  fd_pure                                 0
% 3.68/0.97  fd_pseudo                               0
% 3.68/0.97  fd_cond                                 0
% 3.68/0.97  fd_pseudo_cond                          0
% 3.68/0.97  AC symbols                              0
% 3.68/0.97  
% 3.68/0.97  ------ Input Options Time Limit: Unbounded
% 3.68/0.97  
% 3.68/0.97  
% 3.68/0.97  ------ 
% 3.68/0.97  Current options:
% 3.68/0.97  ------ 
% 3.68/0.97  
% 3.68/0.97  
% 3.68/0.97  
% 3.68/0.97  
% 3.68/0.97  ------ Proving...
% 3.68/0.97  
% 3.68/0.97  
% 3.68/0.97  % SZS status Theorem for theBenchmark.p
% 3.68/0.97  
% 3.68/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 3.68/0.97  
% 3.68/0.97  fof(f5,axiom,(
% 3.68/0.97    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.68/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.68/0.97  
% 3.68/0.97  fof(f32,plain,(
% 3.68/0.97    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.68/0.97    inference(cnf_transformation,[],[f5])).
% 3.68/0.97  
% 3.68/0.97  fof(f4,axiom,(
% 3.68/0.97    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.68/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.68/0.97  
% 3.68/0.97  fof(f20,plain,(
% 3.68/0.97    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.68/0.97    inference(ennf_transformation,[],[f4])).
% 3.68/0.97  
% 3.68/0.97  fof(f31,plain,(
% 3.68/0.97    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 3.68/0.97    inference(cnf_transformation,[],[f20])).
% 3.68/0.97  
% 3.68/0.97  fof(f15,axiom,(
% 3.68/0.97    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 3.68/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.68/0.97  
% 3.68/0.97  fof(f23,plain,(
% 3.68/0.97    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 3.68/0.97    inference(ennf_transformation,[],[f15])).
% 3.68/0.97  
% 3.68/0.97  fof(f42,plain,(
% 3.68/0.97    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 3.68/0.97    inference(cnf_transformation,[],[f23])).
% 3.68/0.97  
% 3.68/0.97  fof(f10,axiom,(
% 3.68/0.97    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.68/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.68/0.97  
% 3.68/0.97  fof(f37,plain,(
% 3.68/0.97    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.68/0.97    inference(cnf_transformation,[],[f10])).
% 3.68/0.97  
% 3.68/0.97  fof(f11,axiom,(
% 3.68/0.97    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.68/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.68/0.97  
% 3.68/0.97  fof(f38,plain,(
% 3.68/0.97    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.68/0.97    inference(cnf_transformation,[],[f11])).
% 3.68/0.97  
% 3.68/0.97  fof(f12,axiom,(
% 3.68/0.97    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.68/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.68/0.97  
% 3.68/0.97  fof(f39,plain,(
% 3.68/0.97    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.68/0.97    inference(cnf_transformation,[],[f12])).
% 3.68/0.97  
% 3.68/0.97  fof(f13,axiom,(
% 3.68/0.97    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.68/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.68/0.97  
% 3.68/0.97  fof(f40,plain,(
% 3.68/0.97    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.68/0.97    inference(cnf_transformation,[],[f13])).
% 3.68/0.97  
% 3.68/0.97  fof(f46,plain,(
% 3.68/0.97    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 3.68/0.97    inference(definition_unfolding,[],[f39,f40])).
% 3.68/0.97  
% 3.68/0.97  fof(f47,plain,(
% 3.68/0.97    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 3.68/0.97    inference(definition_unfolding,[],[f38,f46])).
% 3.68/0.97  
% 3.68/0.97  fof(f49,plain,(
% 3.68/0.97    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 3.68/0.97    inference(definition_unfolding,[],[f37,f47])).
% 3.68/0.97  
% 3.68/0.97  fof(f54,plain,(
% 3.68/0.97    ( ! [X0,X1] : (r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 3.68/0.97    inference(definition_unfolding,[],[f42,f49])).
% 3.68/0.97  
% 3.68/0.97  fof(f9,axiom,(
% 3.68/0.97    ! [X0,X1,X2] : (r1_xboole_0(X0,X1) => k4_xboole_0(k2_xboole_0(X2,X1),X0) = k2_xboole_0(k4_xboole_0(X2,X0),X1))),
% 3.68/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.68/0.97  
% 3.68/0.97  fof(f21,plain,(
% 3.68/0.97    ! [X0,X1,X2] : (k4_xboole_0(k2_xboole_0(X2,X1),X0) = k2_xboole_0(k4_xboole_0(X2,X0),X1) | ~r1_xboole_0(X0,X1))),
% 3.68/0.97    inference(ennf_transformation,[],[f9])).
% 3.68/0.97  
% 3.68/0.97  fof(f36,plain,(
% 3.68/0.97    ( ! [X2,X0,X1] : (k4_xboole_0(k2_xboole_0(X2,X1),X0) = k2_xboole_0(k4_xboole_0(X2,X0),X1) | ~r1_xboole_0(X0,X1)) )),
% 3.68/0.97    inference(cnf_transformation,[],[f21])).
% 3.68/0.97  
% 3.68/0.97  fof(f16,axiom,(
% 3.68/0.97    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.68/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.68/0.97  
% 3.68/0.97  fof(f43,plain,(
% 3.68/0.97    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.68/0.97    inference(cnf_transformation,[],[f16])).
% 3.68/0.97  
% 3.68/0.97  fof(f48,plain,(
% 3.68/0.97    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 3.68/0.97    inference(definition_unfolding,[],[f43,f47])).
% 3.68/0.97  
% 3.68/0.97  fof(f3,axiom,(
% 3.68/0.97    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.68/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.68/0.97  
% 3.68/0.97  fof(f30,plain,(
% 3.68/0.97    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.68/0.97    inference(cnf_transformation,[],[f3])).
% 3.68/0.97  
% 3.68/0.97  fof(f52,plain,(
% 3.68/0.97    ( ! [X2,X0,X1] : (k5_xboole_0(k3_tarski(k3_enumset1(X2,X2,X2,X2,X1)),k3_xboole_0(k3_tarski(k3_enumset1(X2,X2,X2,X2,X1)),X0)) = k3_tarski(k3_enumset1(k5_xboole_0(X2,k3_xboole_0(X2,X0)),k5_xboole_0(X2,k3_xboole_0(X2,X0)),k5_xboole_0(X2,k3_xboole_0(X2,X0)),k5_xboole_0(X2,k3_xboole_0(X2,X0)),X1)) | ~r1_xboole_0(X0,X1)) )),
% 3.68/0.97    inference(definition_unfolding,[],[f36,f30,f48,f48,f30])).
% 3.68/0.97  
% 3.68/0.97  fof(f17,conjecture,(
% 3.68/0.97    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 3.68/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.68/0.97  
% 3.68/0.97  fof(f18,negated_conjecture,(
% 3.68/0.97    ~! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 3.68/0.97    inference(negated_conjecture,[],[f17])).
% 3.68/0.97  
% 3.68/0.97  fof(f24,plain,(
% 3.68/0.97    ? [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <~> ~r2_hidden(X1,X0))),
% 3.68/0.97    inference(ennf_transformation,[],[f18])).
% 3.68/0.97  
% 3.68/0.97  fof(f25,plain,(
% 3.68/0.97    ? [X0,X1] : ((r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) = X0))),
% 3.68/0.97    inference(nnf_transformation,[],[f24])).
% 3.68/0.97  
% 3.68/0.97  fof(f26,plain,(
% 3.68/0.97    ? [X0,X1] : ((r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) = X0)) => ((r2_hidden(sK1,sK0) | k4_xboole_0(sK0,k1_tarski(sK1)) != sK0) & (~r2_hidden(sK1,sK0) | k4_xboole_0(sK0,k1_tarski(sK1)) = sK0))),
% 3.68/0.97    introduced(choice_axiom,[])).
% 3.68/0.97  
% 3.68/0.97  fof(f27,plain,(
% 3.68/0.97    (r2_hidden(sK1,sK0) | k4_xboole_0(sK0,k1_tarski(sK1)) != sK0) & (~r2_hidden(sK1,sK0) | k4_xboole_0(sK0,k1_tarski(sK1)) = sK0)),
% 3.68/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f26])).
% 3.68/0.97  
% 3.68/0.97  fof(f44,plain,(
% 3.68/0.97    ~r2_hidden(sK1,sK0) | k4_xboole_0(sK0,k1_tarski(sK1)) = sK0),
% 3.68/0.97    inference(cnf_transformation,[],[f27])).
% 3.68/0.97  
% 3.68/0.97  fof(f56,plain,(
% 3.68/0.97    ~r2_hidden(sK1,sK0) | k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) = sK0),
% 3.68/0.97    inference(definition_unfolding,[],[f44,f30,f49])).
% 3.68/0.97  
% 3.68/0.97  fof(f7,axiom,(
% 3.68/0.97    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 3.68/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.68/0.97  
% 3.68/0.97  fof(f34,plain,(
% 3.68/0.97    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.68/0.97    inference(cnf_transformation,[],[f7])).
% 3.68/0.97  
% 3.68/0.97  fof(f1,axiom,(
% 3.68/0.97    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.68/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.68/0.97  
% 3.68/0.97  fof(f28,plain,(
% 3.68/0.97    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.68/0.97    inference(cnf_transformation,[],[f1])).
% 3.68/0.97  
% 3.68/0.97  fof(f6,axiom,(
% 3.68/0.97    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 3.68/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.68/0.97  
% 3.68/0.97  fof(f33,plain,(
% 3.68/0.97    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 3.68/0.97    inference(cnf_transformation,[],[f6])).
% 3.68/0.97  
% 3.68/0.97  fof(f50,plain,(
% 3.68/0.97    ( ! [X0,X1] : (k3_tarski(k3_enumset1(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = X0) )),
% 3.68/0.97    inference(definition_unfolding,[],[f33,f48,f30])).
% 3.68/0.97  
% 3.68/0.97  fof(f8,axiom,(
% 3.68/0.97    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 3.68/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.68/0.97  
% 3.68/0.97  fof(f35,plain,(
% 3.68/0.97    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 3.68/0.97    inference(cnf_transformation,[],[f8])).
% 3.68/0.97  
% 3.68/0.97  fof(f51,plain,(
% 3.68/0.97    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) )),
% 3.68/0.97    inference(definition_unfolding,[],[f35,f30])).
% 3.68/0.97  
% 3.68/0.97  fof(f2,axiom,(
% 3.68/0.97    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 3.68/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.68/0.97  
% 3.68/0.97  fof(f19,plain,(
% 3.68/0.97    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 3.68/0.97    inference(ennf_transformation,[],[f2])).
% 3.68/0.97  
% 3.68/0.97  fof(f29,plain,(
% 3.68/0.97    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 3.68/0.97    inference(cnf_transformation,[],[f19])).
% 3.68/0.97  
% 3.68/0.97  fof(f14,axiom,(
% 3.68/0.97    ! [X0,X1] : ~(r2_hidden(X0,X1) & r1_xboole_0(k1_tarski(X0),X1))),
% 3.68/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.68/0.97  
% 3.68/0.97  fof(f22,plain,(
% 3.68/0.97    ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1))),
% 3.68/0.97    inference(ennf_transformation,[],[f14])).
% 3.68/0.97  
% 3.68/0.97  fof(f41,plain,(
% 3.68/0.97    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1)) )),
% 3.68/0.97    inference(cnf_transformation,[],[f22])).
% 3.68/0.97  
% 3.68/0.97  fof(f53,plain,(
% 3.68/0.97    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1)) )),
% 3.68/0.97    inference(definition_unfolding,[],[f41,f49])).
% 3.68/0.97  
% 3.68/0.97  fof(f45,plain,(
% 3.68/0.97    r2_hidden(sK1,sK0) | k4_xboole_0(sK0,k1_tarski(sK1)) != sK0),
% 3.68/0.97    inference(cnf_transformation,[],[f27])).
% 3.68/0.97  
% 3.68/0.97  fof(f55,plain,(
% 3.68/0.97    r2_hidden(sK1,sK0) | k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) != sK0),
% 3.68/0.97    inference(definition_unfolding,[],[f45,f30,f49])).
% 3.68/0.97  
% 3.68/0.97  cnf(c_3,plain,
% 3.68/0.97      ( r1_tarski(k1_xboole_0,X0) ),
% 3.68/0.97      inference(cnf_transformation,[],[f32]) ).
% 3.68/0.97  
% 3.68/0.97  cnf(c_414,plain,
% 3.68/0.97      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.68/0.97      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.68/0.97  
% 3.68/0.97  cnf(c_2,plain,
% 3.68/0.97      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 3.68/0.97      inference(cnf_transformation,[],[f31]) ).
% 3.68/0.97  
% 3.68/0.97  cnf(c_415,plain,
% 3.68/0.97      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 3.68/0.97      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.68/0.97  
% 3.68/0.97  cnf(c_693,plain,
% 3.68/0.97      ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.68/0.97      inference(superposition,[status(thm)],[c_414,c_415]) ).
% 3.68/0.97  
% 3.68/0.97  cnf(c_9,plain,
% 3.68/0.97      ( r2_hidden(X0,X1) | r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) ),
% 3.68/0.97      inference(cnf_transformation,[],[f54]) ).
% 3.68/0.97  
% 3.68/0.97  cnf(c_410,plain,
% 3.68/0.97      ( r2_hidden(X0,X1) = iProver_top
% 3.68/0.97      | r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) = iProver_top ),
% 3.68/0.97      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.68/0.97  
% 3.68/0.97  cnf(c_7,plain,
% 3.68/0.97      ( ~ r1_xboole_0(X0,X1)
% 3.68/0.97      | k3_tarski(k3_enumset1(k5_xboole_0(X2,k3_xboole_0(X2,X0)),k5_xboole_0(X2,k3_xboole_0(X2,X0)),k5_xboole_0(X2,k3_xboole_0(X2,X0)),k5_xboole_0(X2,k3_xboole_0(X2,X0)),X1)) = k5_xboole_0(k3_tarski(k3_enumset1(X2,X2,X2,X2,X1)),k3_xboole_0(k3_tarski(k3_enumset1(X2,X2,X2,X2,X1)),X0)) ),
% 3.68/0.97      inference(cnf_transformation,[],[f52]) ).
% 3.68/0.97  
% 3.68/0.97  cnf(c_412,plain,
% 3.68/0.97      ( k3_tarski(k3_enumset1(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2)) = k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X2)),k3_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X2)),X1))
% 3.68/0.97      | r1_xboole_0(X1,X2) != iProver_top ),
% 3.68/0.97      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.68/0.97  
% 3.68/0.97  cnf(c_1656,plain,
% 3.68/0.97      ( k3_tarski(k3_enumset1(k5_xboole_0(X0,k3_xboole_0(X0,k3_enumset1(X1,X1,X1,X1,X1))),k5_xboole_0(X0,k3_xboole_0(X0,k3_enumset1(X1,X1,X1,X1,X1))),k5_xboole_0(X0,k3_xboole_0(X0,k3_enumset1(X1,X1,X1,X1,X1))),k5_xboole_0(X0,k3_xboole_0(X0,k3_enumset1(X1,X1,X1,X1,X1))),X2)) = k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X2)),k3_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X2)),k3_enumset1(X1,X1,X1,X1,X1)))
% 3.68/0.97      | r2_hidden(X1,X2) = iProver_top ),
% 3.68/0.97      inference(superposition,[status(thm)],[c_410,c_412]) ).
% 3.68/0.97  
% 3.68/0.97  cnf(c_11,negated_conjecture,
% 3.68/0.97      ( ~ r2_hidden(sK1,sK0)
% 3.68/0.97      | k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) = sK0 ),
% 3.68/0.97      inference(cnf_transformation,[],[f56]) ).
% 3.68/0.97  
% 3.68/0.97  cnf(c_408,plain,
% 3.68/0.97      ( k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) = sK0
% 3.68/0.97      | r2_hidden(sK1,sK0) != iProver_top ),
% 3.68/0.97      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.68/0.97  
% 3.68/0.97  cnf(c_4800,plain,
% 3.68/0.97      ( k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) = sK0
% 3.68/0.97      | k3_tarski(k3_enumset1(k5_xboole_0(X0,k3_xboole_0(X0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))),k5_xboole_0(X0,k3_xboole_0(X0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))),k5_xboole_0(X0,k3_xboole_0(X0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))),k5_xboole_0(X0,k3_xboole_0(X0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))),sK0)) = k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,sK0)),k3_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,sK0)),k3_enumset1(sK1,sK1,sK1,sK1,sK1))) ),
% 3.68/0.97      inference(superposition,[status(thm)],[c_1656,c_408]) ).
% 3.68/0.97  
% 3.68/0.97  cnf(c_5640,plain,
% 3.68/0.97      ( k5_xboole_0(k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK0)),k3_xboole_0(k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK0)),k3_enumset1(sK1,sK1,sK1,sK1,sK1))) = k3_tarski(k3_enumset1(k5_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k1_xboole_0,k1_xboole_0),sK0))
% 3.68/0.97      | k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) = sK0 ),
% 3.68/0.97      inference(superposition,[status(thm)],[c_693,c_4800]) ).
% 3.68/0.97  
% 3.68/0.97  cnf(c_5,plain,
% 3.68/0.97      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.68/0.97      inference(cnf_transformation,[],[f34]) ).
% 3.68/0.97  
% 3.68/0.97  cnf(c_0,plain,
% 3.68/0.97      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 3.68/0.97      inference(cnf_transformation,[],[f28]) ).
% 3.68/0.97  
% 3.68/0.97  cnf(c_4,plain,
% 3.68/0.97      ( k3_tarski(k3_enumset1(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = X0 ),
% 3.68/0.97      inference(cnf_transformation,[],[f50]) ).
% 3.68/0.97  
% 3.68/0.97  cnf(c_803,plain,
% 3.68/0.97      ( k3_tarski(k3_enumset1(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k5_xboole_0(X1,k3_xboole_0(X0,X1)))) = X1 ),
% 3.68/0.97      inference(superposition,[status(thm)],[c_0,c_4]) ).
% 3.68/0.97  
% 3.68/0.97  cnf(c_1100,plain,
% 3.68/0.97      ( k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k5_xboole_0(X0,k1_xboole_0))) = X0 ),
% 3.68/0.97      inference(superposition,[status(thm)],[c_693,c_803]) ).
% 3.68/0.97  
% 3.68/0.97  cnf(c_1126,plain,
% 3.68/0.97      ( k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0 ),
% 3.68/0.97      inference(light_normalisation,[status(thm)],[c_1100,c_5]) ).
% 3.68/0.97  
% 3.68/0.97  cnf(c_5643,plain,
% 3.68/0.97      ( k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) = sK0 ),
% 3.68/0.97      inference(demodulation,[status(thm)],[c_5640,c_5,c_1126]) ).
% 3.68/0.97  
% 3.68/0.97  cnf(c_6,plain,
% 3.68/0.97      ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
% 3.68/0.97      inference(cnf_transformation,[],[f51]) ).
% 3.68/0.97  
% 3.68/0.97  cnf(c_413,plain,
% 3.68/0.97      ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) = iProver_top ),
% 3.68/0.97      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.68/0.97  
% 3.68/0.97  cnf(c_5925,plain,
% 3.68/0.97      ( r1_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) = iProver_top ),
% 3.68/0.97      inference(superposition,[status(thm)],[c_5643,c_413]) ).
% 3.68/0.97  
% 3.68/0.97  cnf(c_1,plain,
% 3.68/0.97      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 3.68/0.97      inference(cnf_transformation,[],[f29]) ).
% 3.68/0.97  
% 3.68/0.97  cnf(c_1618,plain,
% 3.68/0.97      ( r1_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK0)
% 3.68/0.97      | ~ r1_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) ),
% 3.68/0.97      inference(instantiation,[status(thm)],[c_1]) ).
% 3.68/0.97  
% 3.68/0.97  cnf(c_1629,plain,
% 3.68/0.97      ( r1_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK0) = iProver_top
% 3.68/0.97      | r1_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) != iProver_top ),
% 3.68/0.97      inference(predicate_to_equality,[status(thm)],[c_1618]) ).
% 3.68/0.97  
% 3.68/0.97  cnf(c_8,plain,
% 3.68/0.97      ( ~ r2_hidden(X0,X1)
% 3.68/0.97      | ~ r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) ),
% 3.68/0.97      inference(cnf_transformation,[],[f53]) ).
% 3.68/0.97  
% 3.68/0.97  cnf(c_572,plain,
% 3.68/0.97      ( ~ r2_hidden(sK1,sK0)
% 3.68/0.97      | ~ r1_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK0) ),
% 3.68/0.97      inference(instantiation,[status(thm)],[c_8]) ).
% 3.68/0.97  
% 3.68/0.97  cnf(c_573,plain,
% 3.68/0.97      ( r2_hidden(sK1,sK0) != iProver_top
% 3.68/0.97      | r1_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK0) != iProver_top ),
% 3.68/0.97      inference(predicate_to_equality,[status(thm)],[c_572]) ).
% 3.68/0.97  
% 3.68/0.97  cnf(c_10,negated_conjecture,
% 3.68/0.97      ( r2_hidden(sK1,sK0)
% 3.68/0.97      | k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) != sK0 ),
% 3.68/0.97      inference(cnf_transformation,[],[f55]) ).
% 3.68/0.97  
% 3.68/0.97  cnf(c_13,plain,
% 3.68/0.97      ( k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) != sK0
% 3.68/0.97      | r2_hidden(sK1,sK0) = iProver_top ),
% 3.68/0.97      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.68/0.97  
% 3.68/0.97  cnf(contradiction,plain,
% 3.68/0.97      ( $false ),
% 3.68/0.97      inference(minisat,[status(thm)],[c_5925,c_5643,c_1629,c_573,c_13]) ).
% 3.68/0.97  
% 3.68/0.97  
% 3.68/0.97  % SZS output end CNFRefutation for theBenchmark.p
% 3.68/0.97  
% 3.68/0.97  ------                               Statistics
% 3.68/0.97  
% 3.68/0.97  ------ Selected
% 3.68/0.97  
% 3.68/0.97  total_time:                             0.23
% 3.68/0.97  
%------------------------------------------------------------------------------
