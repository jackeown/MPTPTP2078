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
% DateTime   : Thu Dec  3 11:35:12 EST 2020

% Result     : Theorem 3.32s
% Output     : CNFRefutation 3.32s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 201 expanded)
%              Number of clauses        :   24 (  28 expanded)
%              Number of leaves         :   18 (  64 expanded)
%              Depth                    :   11
%              Number of atoms          :   99 ( 228 expanded)
%              Number of equality atoms :   73 ( 196 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f12])).

fof(f47,plain,(
    ! [X4,X2,X0,X3,X1] : k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f34,f35])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f33,f47])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f13])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f6])).

fof(f16,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f43,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f39,f42])).

fof(f7,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f42,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f31,f32])).

fof(f45,plain,(
    ! [X0] : k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0) ),
    inference(definition_unfolding,[],[f30,f42])).

fof(f46,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k3_tarski(k2_enumset1(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k2_enumset1(X7,X7,X7,X7))) ),
    inference(definition_unfolding,[],[f29,f43,f45])).

fof(f49,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k3_tarski(k2_enumset1(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k2_enumset1(X6,X6,X6,X6))) ),
    inference(definition_unfolding,[],[f36,f46])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f50,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k2_enumset1(X2,X2,X1,X0) ),
    inference(definition_unfolding,[],[f28,f32,f32])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_tarski(k2_enumset1(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X0,X0,X0,X1),k2_enumset1(X0,X0,X0,X1),k2_enumset1(X2,X2,X2,X3))) ),
    inference(definition_unfolding,[],[f27,f43,f42,f42])).

fof(f17,conjecture,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)
      | r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k3_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)
        | r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f21,plain,(
    ? [X0,X1] :
      ( k3_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0)
      & ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f22,plain,
    ( ? [X0,X1] :
        ( k3_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0)
        & ~ r1_xboole_0(k1_tarski(X0),X1) )
   => ( k3_xboole_0(k1_tarski(sK0),sK1) != k1_tarski(sK0)
      & ~ r1_xboole_0(k1_tarski(sK0),sK1) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( k3_xboole_0(k1_tarski(sK0),sK1) != k1_tarski(sK0)
    & ~ r1_xboole_0(k1_tarski(sK0),sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f22])).

fof(f41,plain,(
    k3_xboole_0(k1_tarski(sK0),sK1) != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f3,axiom,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f44,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k2_enumset1(X0,X0,X0,X1))) = k3_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f26,f43])).

fof(f54,plain,(
    k5_xboole_0(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1),k3_tarski(k2_enumset1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0),sK1))) != k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f41,f44,f45,f45])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f37,f45])).

fof(f40,plain,(
    ~ r1_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f55,plain,(
    ~ r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    inference(definition_unfolding,[],[f40,f45])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k3_xboole_0(X1,k1_tarski(X0)) = k1_tarski(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X1,k1_tarski(X0)) = k1_tarski(X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X1,k1_tarski(X0)) = k1_tarski(X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(k5_xboole_0(X1,k2_enumset1(X0,X0,X0,X0)),k3_tarski(k2_enumset1(X1,X1,X1,k2_enumset1(X0,X0,X0,X0)))) = k2_enumset1(X0,X0,X0,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f38,f44,f45,f45])).

cnf(c_5,plain,
    ( k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1,plain,
    ( k3_tarski(k2_enumset1(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k2_enumset1(X6,X6,X6,X6))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_488,plain,
    ( k3_tarski(k2_enumset1(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X0,X1,X2,X3),k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X4,X4,X4))) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4) ),
    inference(superposition,[status(thm)],[c_5,c_1])).

cnf(c_4,plain,
    ( k2_enumset1(X0,X0,X1,X2) = k2_enumset1(X2,X2,X1,X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_0,plain,
    ( k3_tarski(k2_enumset1(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X0,X0,X0,X1),k2_enumset1(X0,X0,X0,X1),k2_enumset1(X2,X2,X2,X3))) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_477,plain,
    ( k3_tarski(k2_enumset1(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X0,X0,X0,X1),k2_enumset1(X0,X0,X0,X1),k2_enumset1(X2,X2,X3,X3))) = k2_enumset1(X0,X1,X3,X2) ),
    inference(superposition,[status(thm)],[c_4,c_0])).

cnf(c_1096,plain,
    ( k5_enumset1(X0,X0,X0,X0,X0,X1,X2) = k2_enumset1(X0,X1,X2,X2) ),
    inference(superposition,[status(thm)],[c_488,c_477])).

cnf(c_8,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1),k3_tarski(k2_enumset1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0),sK1))) != k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_3,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_2,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_47,negated_conjecture,
    ( k5_xboole_0(sK1,k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_tarski(k2_enumset1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0),sK1)))) != k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(theory_normalisation,[status(thm)],[c_8,c_3,c_2])).

cnf(c_261,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_tarski(k2_enumset1(sK1,sK1,k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0))))) != k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(demodulation,[status(thm)],[c_4,c_47])).

cnf(c_6720,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,k2_enumset1(sK0,sK0,sK0,sK0))))) != k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(demodulation,[status(thm)],[c_1096,c_261])).

cnf(c_6,plain,
    ( r2_hidden(X0,X1)
    | r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_119,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_9,negated_conjecture,
    ( ~ r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_117,plain,
    ( r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1114,plain,
    ( r2_hidden(sK0,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_119,c_117])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,X1)
    | k5_xboole_0(k5_xboole_0(X1,k2_enumset1(X0,X0,X0,X0)),k3_tarski(k2_enumset1(X1,X1,X1,k2_enumset1(X0,X0,X0,X0)))) = k2_enumset1(X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_48,plain,
    ( ~ r2_hidden(X0,X1)
    | k5_xboole_0(X1,k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_tarski(k2_enumset1(X1,X1,X1,k2_enumset1(X0,X0,X0,X0))))) = k2_enumset1(X0,X0,X0,X0) ),
    inference(theory_normalisation,[status(thm)],[c_7,c_3,c_2])).

cnf(c_118,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k3_tarski(k2_enumset1(X0,X0,X0,k2_enumset1(X1,X1,X1,X1))))) = k2_enumset1(X1,X1,X1,X1)
    | r2_hidden(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_48])).

cnf(c_1491,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_tarski(k2_enumset1(sK1,sK1,sK1,k2_enumset1(sK0,sK0,sK0,sK0))))) = k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(superposition,[status(thm)],[c_1114,c_118])).

cnf(c_6721,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) != k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(demodulation,[status(thm)],[c_6720,c_5,c_1491])).

cnf(c_6722,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_6721])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n016.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 11:35:34 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.32/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.32/0.98  
% 3.32/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.32/0.98  
% 3.32/0.98  ------  iProver source info
% 3.32/0.98  
% 3.32/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.32/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.32/0.98  git: non_committed_changes: false
% 3.32/0.98  git: last_make_outside_of_git: false
% 3.32/0.98  
% 3.32/0.98  ------ 
% 3.32/0.98  ------ Parsing...
% 3.32/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.32/0.98  
% 3.32/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.32/0.98  
% 3.32/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.32/0.98  
% 3.32/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.32/0.98  ------ Proving...
% 3.32/0.98  ------ Problem Properties 
% 3.32/0.98  
% 3.32/0.98  
% 3.32/0.98  clauses                                 10
% 3.32/0.98  conjectures                             2
% 3.32/0.98  EPR                                     0
% 3.32/0.98  Horn                                    9
% 3.32/0.98  unary                                   8
% 3.32/0.98  binary                                  2
% 3.32/0.98  lits                                    12
% 3.32/0.98  lits eq                                 8
% 3.32/0.98  fd_pure                                 0
% 3.32/0.98  fd_pseudo                               0
% 3.32/0.98  fd_cond                                 0
% 3.32/0.98  fd_pseudo_cond                          0
% 3.32/0.98  AC symbols                              1
% 3.32/0.98  
% 3.32/0.98  ------ Input Options Time Limit: Unbounded
% 3.32/0.98  
% 3.32/0.98  
% 3.32/0.98  ------ 
% 3.32/0.98  Current options:
% 3.32/0.98  ------ 
% 3.32/0.98  
% 3.32/0.98  
% 3.32/0.98  
% 3.32/0.98  
% 3.32/0.98  ------ Proving...
% 3.32/0.98  
% 3.32/0.98  
% 3.32/0.98  % SZS status Theorem for theBenchmark.p
% 3.32/0.98  
% 3.32/0.98   Resolution empty clause
% 3.32/0.98  
% 3.32/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.32/0.98  
% 3.32/0.98  fof(f10,axiom,(
% 3.32/0.98    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.32/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.32/0.98  
% 3.32/0.98  fof(f33,plain,(
% 3.32/0.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.32/0.98    inference(cnf_transformation,[],[f10])).
% 3.32/0.98  
% 3.32/0.98  fof(f11,axiom,(
% 3.32/0.98    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 3.32/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.32/0.98  
% 3.32/0.98  fof(f34,plain,(
% 3.32/0.98    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 3.32/0.98    inference(cnf_transformation,[],[f11])).
% 3.32/0.98  
% 3.32/0.98  fof(f12,axiom,(
% 3.32/0.98    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 3.32/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.32/0.98  
% 3.32/0.98  fof(f35,plain,(
% 3.32/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 3.32/0.98    inference(cnf_transformation,[],[f12])).
% 3.32/0.98  
% 3.32/0.98  fof(f47,plain,(
% 3.32/0.98    ( ! [X4,X2,X0,X3,X1] : (k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 3.32/0.98    inference(definition_unfolding,[],[f34,f35])).
% 3.32/0.98  
% 3.32/0.98  fof(f51,plain,(
% 3.32/0.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)) )),
% 3.32/0.98    inference(definition_unfolding,[],[f33,f47])).
% 3.32/0.98  
% 3.32/0.98  fof(f13,axiom,(
% 3.32/0.98    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 3.32/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.32/0.98  
% 3.32/0.98  fof(f36,plain,(
% 3.32/0.98    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 3.32/0.98    inference(cnf_transformation,[],[f13])).
% 3.32/0.98  
% 3.32/0.98  fof(f6,axiom,(
% 3.32/0.98    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)),
% 3.32/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.32/0.98  
% 3.32/0.98  fof(f29,plain,(
% 3.32/0.98    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 3.32/0.98    inference(cnf_transformation,[],[f6])).
% 3.32/0.98  
% 3.32/0.98  fof(f16,axiom,(
% 3.32/0.98    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.32/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.32/0.98  
% 3.32/0.98  fof(f39,plain,(
% 3.32/0.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.32/0.98    inference(cnf_transformation,[],[f16])).
% 3.32/0.98  
% 3.32/0.98  fof(f43,plain,(
% 3.32/0.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 3.32/0.98    inference(definition_unfolding,[],[f39,f42])).
% 3.32/0.98  
% 3.32/0.98  fof(f7,axiom,(
% 3.32/0.98    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.32/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.32/0.98  
% 3.32/0.98  fof(f30,plain,(
% 3.32/0.98    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.32/0.98    inference(cnf_transformation,[],[f7])).
% 3.32/0.98  
% 3.32/0.98  fof(f8,axiom,(
% 3.32/0.98    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.32/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.32/0.98  
% 3.32/0.98  fof(f31,plain,(
% 3.32/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.32/0.98    inference(cnf_transformation,[],[f8])).
% 3.32/0.98  
% 3.32/0.98  fof(f9,axiom,(
% 3.32/0.98    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 3.32/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.32/0.98  
% 3.32/0.98  fof(f32,plain,(
% 3.32/0.98    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 3.32/0.98    inference(cnf_transformation,[],[f9])).
% 3.32/0.98  
% 3.32/0.98  fof(f42,plain,(
% 3.32/0.98    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.32/0.98    inference(definition_unfolding,[],[f31,f32])).
% 3.32/0.98  
% 3.32/0.98  fof(f45,plain,(
% 3.32/0.98    ( ! [X0] : (k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0)) )),
% 3.32/0.98    inference(definition_unfolding,[],[f30,f42])).
% 3.32/0.98  
% 3.32/0.98  fof(f46,plain,(
% 3.32/0.98    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k3_tarski(k2_enumset1(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k2_enumset1(X7,X7,X7,X7)))) )),
% 3.32/0.98    inference(definition_unfolding,[],[f29,f43,f45])).
% 3.32/0.98  
% 3.32/0.98  fof(f49,plain,(
% 3.32/0.98    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k3_tarski(k2_enumset1(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k2_enumset1(X6,X6,X6,X6)))) )),
% 3.32/0.98    inference(definition_unfolding,[],[f36,f46])).
% 3.32/0.98  
% 3.32/0.98  fof(f5,axiom,(
% 3.32/0.98    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0)),
% 3.32/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.32/0.98  
% 3.32/0.98  fof(f28,plain,(
% 3.32/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0)) )),
% 3.32/0.98    inference(cnf_transformation,[],[f5])).
% 3.32/0.98  
% 3.32/0.98  fof(f50,plain,(
% 3.32/0.98    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k2_enumset1(X2,X2,X1,X0)) )),
% 3.32/0.98    inference(definition_unfolding,[],[f28,f32,f32])).
% 3.32/0.98  
% 3.32/0.98  fof(f4,axiom,(
% 3.32/0.98    ! [X0,X1,X2,X3] : k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3)),
% 3.32/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.32/0.98  
% 3.32/0.98  fof(f27,plain,(
% 3.32/0.98    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3)) )),
% 3.32/0.98    inference(cnf_transformation,[],[f4])).
% 3.32/0.98  
% 3.32/0.98  fof(f48,plain,(
% 3.32/0.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_tarski(k2_enumset1(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X0,X0,X0,X1),k2_enumset1(X0,X0,X0,X1),k2_enumset1(X2,X2,X2,X3)))) )),
% 3.32/0.98    inference(definition_unfolding,[],[f27,f43,f42,f42])).
% 3.32/0.98  
% 3.32/0.98  fof(f17,conjecture,(
% 3.32/0.98    ! [X0,X1] : (k3_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0) | r1_xboole_0(k1_tarski(X0),X1))),
% 3.32/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.32/0.98  
% 3.32/0.98  fof(f18,negated_conjecture,(
% 3.32/0.98    ~! [X0,X1] : (k3_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0) | r1_xboole_0(k1_tarski(X0),X1))),
% 3.32/0.98    inference(negated_conjecture,[],[f17])).
% 3.32/0.98  
% 3.32/0.98  fof(f21,plain,(
% 3.32/0.98    ? [X0,X1] : (k3_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0) & ~r1_xboole_0(k1_tarski(X0),X1))),
% 3.32/0.98    inference(ennf_transformation,[],[f18])).
% 3.32/0.98  
% 3.32/0.98  fof(f22,plain,(
% 3.32/0.98    ? [X0,X1] : (k3_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0) & ~r1_xboole_0(k1_tarski(X0),X1)) => (k3_xboole_0(k1_tarski(sK0),sK1) != k1_tarski(sK0) & ~r1_xboole_0(k1_tarski(sK0),sK1))),
% 3.32/0.98    introduced(choice_axiom,[])).
% 3.32/0.98  
% 3.32/0.98  fof(f23,plain,(
% 3.32/0.98    k3_xboole_0(k1_tarski(sK0),sK1) != k1_tarski(sK0) & ~r1_xboole_0(k1_tarski(sK0),sK1)),
% 3.32/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f22])).
% 3.32/0.98  
% 3.32/0.98  fof(f41,plain,(
% 3.32/0.98    k3_xboole_0(k1_tarski(sK0),sK1) != k1_tarski(sK0)),
% 3.32/0.98    inference(cnf_transformation,[],[f23])).
% 3.32/0.98  
% 3.32/0.98  fof(f3,axiom,(
% 3.32/0.98    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 3.32/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.32/0.98  
% 3.32/0.98  fof(f26,plain,(
% 3.32/0.98    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 3.32/0.98    inference(cnf_transformation,[],[f3])).
% 3.32/0.98  
% 3.32/0.98  fof(f44,plain,(
% 3.32/0.98    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k2_enumset1(X0,X0,X0,X1))) = k3_xboole_0(X0,X1)) )),
% 3.32/0.98    inference(definition_unfolding,[],[f26,f43])).
% 3.32/0.98  
% 3.32/0.98  fof(f54,plain,(
% 3.32/0.98    k5_xboole_0(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1),k3_tarski(k2_enumset1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0),sK1))) != k2_enumset1(sK0,sK0,sK0,sK0)),
% 3.32/0.98    inference(definition_unfolding,[],[f41,f44,f45,f45])).
% 3.32/0.98  
% 3.32/0.98  fof(f2,axiom,(
% 3.32/0.98    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 3.32/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.32/0.98  
% 3.32/0.98  fof(f25,plain,(
% 3.32/0.98    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 3.32/0.98    inference(cnf_transformation,[],[f2])).
% 3.32/0.98  
% 3.32/0.98  fof(f1,axiom,(
% 3.32/0.98    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 3.32/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.32/0.98  
% 3.32/0.98  fof(f24,plain,(
% 3.32/0.98    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 3.32/0.98    inference(cnf_transformation,[],[f1])).
% 3.32/0.98  
% 3.32/0.98  fof(f14,axiom,(
% 3.32/0.98    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 3.32/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.32/0.98  
% 3.32/0.98  fof(f19,plain,(
% 3.32/0.98    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 3.32/0.98    inference(ennf_transformation,[],[f14])).
% 3.32/0.98  
% 3.32/0.98  fof(f37,plain,(
% 3.32/0.98    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 3.32/0.98    inference(cnf_transformation,[],[f19])).
% 3.32/0.98  
% 3.32/0.98  fof(f52,plain,(
% 3.32/0.98    ( ! [X0,X1] : (r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 3.32/0.98    inference(definition_unfolding,[],[f37,f45])).
% 3.32/0.98  
% 3.32/0.98  fof(f40,plain,(
% 3.32/0.98    ~r1_xboole_0(k1_tarski(sK0),sK1)),
% 3.32/0.98    inference(cnf_transformation,[],[f23])).
% 3.32/0.98  
% 3.32/0.98  fof(f55,plain,(
% 3.32/0.98    ~r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 3.32/0.98    inference(definition_unfolding,[],[f40,f45])).
% 3.32/0.98  
% 3.32/0.98  fof(f15,axiom,(
% 3.32/0.98    ! [X0,X1] : (r2_hidden(X0,X1) => k3_xboole_0(X1,k1_tarski(X0)) = k1_tarski(X0))),
% 3.32/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.32/0.98  
% 3.32/0.98  fof(f20,plain,(
% 3.32/0.98    ! [X0,X1] : (k3_xboole_0(X1,k1_tarski(X0)) = k1_tarski(X0) | ~r2_hidden(X0,X1))),
% 3.32/0.98    inference(ennf_transformation,[],[f15])).
% 3.32/0.98  
% 3.32/0.98  fof(f38,plain,(
% 3.32/0.98    ( ! [X0,X1] : (k3_xboole_0(X1,k1_tarski(X0)) = k1_tarski(X0) | ~r2_hidden(X0,X1)) )),
% 3.32/0.98    inference(cnf_transformation,[],[f20])).
% 3.32/0.98  
% 3.32/0.98  fof(f53,plain,(
% 3.32/0.98    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X1,k2_enumset1(X0,X0,X0,X0)),k3_tarski(k2_enumset1(X1,X1,X1,k2_enumset1(X0,X0,X0,X0)))) = k2_enumset1(X0,X0,X0,X0) | ~r2_hidden(X0,X1)) )),
% 3.32/0.98    inference(definition_unfolding,[],[f38,f44,f45,f45])).
% 3.32/0.98  
% 3.32/0.98  cnf(c_5,plain,
% 3.32/0.98      ( k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
% 3.32/0.98      inference(cnf_transformation,[],[f51]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_1,plain,
% 3.32/0.98      ( k3_tarski(k2_enumset1(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k2_enumset1(X6,X6,X6,X6))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
% 3.32/0.98      inference(cnf_transformation,[],[f49]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_488,plain,
% 3.32/0.98      ( k3_tarski(k2_enumset1(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X0,X1,X2,X3),k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X4,X4,X4))) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4) ),
% 3.32/0.98      inference(superposition,[status(thm)],[c_5,c_1]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_4,plain,
% 3.32/0.98      ( k2_enumset1(X0,X0,X1,X2) = k2_enumset1(X2,X2,X1,X0) ),
% 3.32/0.98      inference(cnf_transformation,[],[f50]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_0,plain,
% 3.32/0.98      ( k3_tarski(k2_enumset1(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X0,X0,X0,X1),k2_enumset1(X0,X0,X0,X1),k2_enumset1(X2,X2,X2,X3))) = k2_enumset1(X0,X1,X2,X3) ),
% 3.32/0.98      inference(cnf_transformation,[],[f48]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_477,plain,
% 3.32/0.98      ( k3_tarski(k2_enumset1(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X0,X0,X0,X1),k2_enumset1(X0,X0,X0,X1),k2_enumset1(X2,X2,X3,X3))) = k2_enumset1(X0,X1,X3,X2) ),
% 3.32/0.98      inference(superposition,[status(thm)],[c_4,c_0]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_1096,plain,
% 3.32/0.98      ( k5_enumset1(X0,X0,X0,X0,X0,X1,X2) = k2_enumset1(X0,X1,X2,X2) ),
% 3.32/0.98      inference(superposition,[status(thm)],[c_488,c_477]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_8,negated_conjecture,
% 3.32/0.98      ( k5_xboole_0(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1),k3_tarski(k2_enumset1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0),sK1))) != k2_enumset1(sK0,sK0,sK0,sK0) ),
% 3.32/0.98      inference(cnf_transformation,[],[f54]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_3,plain,
% 3.32/0.98      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 3.32/0.98      inference(cnf_transformation,[],[f25]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_2,plain,
% 3.32/0.98      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 3.32/0.98      inference(cnf_transformation,[],[f24]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_47,negated_conjecture,
% 3.32/0.98      ( k5_xboole_0(sK1,k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_tarski(k2_enumset1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0),sK1)))) != k2_enumset1(sK0,sK0,sK0,sK0) ),
% 3.32/0.98      inference(theory_normalisation,[status(thm)],[c_8,c_3,c_2]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_261,plain,
% 3.32/0.98      ( k5_xboole_0(sK1,k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_tarski(k2_enumset1(sK1,sK1,k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0))))) != k2_enumset1(sK0,sK0,sK0,sK0) ),
% 3.32/0.98      inference(demodulation,[status(thm)],[c_4,c_47]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_6720,plain,
% 3.32/0.98      ( k5_xboole_0(sK1,k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,k2_enumset1(sK0,sK0,sK0,sK0))))) != k2_enumset1(sK0,sK0,sK0,sK0) ),
% 3.32/0.98      inference(demodulation,[status(thm)],[c_1096,c_261]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_6,plain,
% 3.32/0.98      ( r2_hidden(X0,X1) | r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) ),
% 3.32/0.98      inference(cnf_transformation,[],[f52]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_119,plain,
% 3.32/0.98      ( r2_hidden(X0,X1) = iProver_top
% 3.32/0.98      | r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) = iProver_top ),
% 3.32/0.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_9,negated_conjecture,
% 3.32/0.98      ( ~ r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
% 3.32/0.98      inference(cnf_transformation,[],[f55]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_117,plain,
% 3.32/0.98      ( r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1) != iProver_top ),
% 3.32/0.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_1114,plain,
% 3.32/0.98      ( r2_hidden(sK0,sK1) = iProver_top ),
% 3.32/0.98      inference(superposition,[status(thm)],[c_119,c_117]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_7,plain,
% 3.32/0.98      ( ~ r2_hidden(X0,X1)
% 3.32/0.98      | k5_xboole_0(k5_xboole_0(X1,k2_enumset1(X0,X0,X0,X0)),k3_tarski(k2_enumset1(X1,X1,X1,k2_enumset1(X0,X0,X0,X0)))) = k2_enumset1(X0,X0,X0,X0) ),
% 3.32/0.98      inference(cnf_transformation,[],[f53]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_48,plain,
% 3.32/0.98      ( ~ r2_hidden(X0,X1)
% 3.32/0.98      | k5_xboole_0(X1,k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_tarski(k2_enumset1(X1,X1,X1,k2_enumset1(X0,X0,X0,X0))))) = k2_enumset1(X0,X0,X0,X0) ),
% 3.32/0.98      inference(theory_normalisation,[status(thm)],[c_7,c_3,c_2]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_118,plain,
% 3.32/0.98      ( k5_xboole_0(X0,k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k3_tarski(k2_enumset1(X0,X0,X0,k2_enumset1(X1,X1,X1,X1))))) = k2_enumset1(X1,X1,X1,X1)
% 3.32/0.98      | r2_hidden(X1,X0) != iProver_top ),
% 3.32/0.98      inference(predicate_to_equality,[status(thm)],[c_48]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_1491,plain,
% 3.32/0.98      ( k5_xboole_0(sK1,k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_tarski(k2_enumset1(sK1,sK1,sK1,k2_enumset1(sK0,sK0,sK0,sK0))))) = k2_enumset1(sK0,sK0,sK0,sK0) ),
% 3.32/0.98      inference(superposition,[status(thm)],[c_1114,c_118]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_6721,plain,
% 3.32/0.98      ( k2_enumset1(sK0,sK0,sK0,sK0) != k2_enumset1(sK0,sK0,sK0,sK0) ),
% 3.32/0.98      inference(demodulation,[status(thm)],[c_6720,c_5,c_1491]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_6722,plain,
% 3.32/0.98      ( $false ),
% 3.32/0.98      inference(equality_resolution_simp,[status(thm)],[c_6721]) ).
% 3.32/0.98  
% 3.32/0.98  
% 3.32/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.32/0.98  
% 3.32/0.98  ------                               Statistics
% 3.32/0.98  
% 3.32/0.98  ------ Selected
% 3.32/0.98  
% 3.32/0.98  total_time:                             0.291
% 3.32/0.98  
%------------------------------------------------------------------------------
