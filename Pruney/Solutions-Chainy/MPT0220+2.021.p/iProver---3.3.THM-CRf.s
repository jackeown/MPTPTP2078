%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:29:30 EST 2020

% Result     : Theorem 39.96s
% Output     : CNFRefutation 39.96s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 272 expanded)
%              Number of clauses        :   36 (  69 expanded)
%              Number of leaves         :   21 (  78 expanded)
%              Depth                    :   17
%              Number of atoms          :  115 ( 306 expanded)
%              Number of equality atoms :   89 ( 264 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,axiom,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f12,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f56,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f41,f55])).

fof(f13,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f17])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f18])).

fof(f51,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f46,f47])).

fof(f52,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f45,f51])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f44,f52])).

fof(f54,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f43,f53])).

fof(f55,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f42,f54])).

fof(f60,plain,(
    ! [X0,X1] : r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f48,f56,f55])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f20,conjecture,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) = k2_tarski(X0,X1) ),
    inference(negated_conjecture,[],[f20])).

fof(f23,plain,(
    ? [X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) != k2_tarski(X0,X1) ),
    inference(ennf_transformation,[],[f21])).

fof(f26,plain,
    ( ? [X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) != k2_tarski(X0,X1)
   => k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1)) != k2_tarski(sK0,sK1) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1)) != k2_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f26])).

fof(f49,plain,(
    k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1)) != k2_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f11,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f4,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f50,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f40,f33])).

fof(f61,plain,(
    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
    inference(definition_unfolding,[],[f49,f50,f56,f55,f55])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f57,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f35,f33])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f59,plain,(
    ! [X0,X1] : r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f38,f50])).

fof(f8,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f58,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),X1)) ),
    inference(definition_unfolding,[],[f36,f33,f33,f50])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f24])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f63,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f30])).

cnf(c_11,plain,
    ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_211,plain,
    ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_213,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2713,plain,
    ( k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(superposition,[status(thm)],[c_211,c_213])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_12,negated_conjecture,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_350,plain,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_0,c_12])).

cnf(c_150278,plain,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_2713,c_350])).

cnf(c_6,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_9,plain,
    ( r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_212,plain,
    ( r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_880,plain,
    ( r1_tarski(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_212])).

cnf(c_8,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_1,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_438,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_8,c_1])).

cnf(c_891,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_880,c_438])).

cnf(c_2715,plain,
    ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_891,c_213])).

cnf(c_3148,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2715,c_0])).

cnf(c_7,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),X1)) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_10,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_119,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),X1)))) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(theory_normalisation,[status(thm)],[c_7,c_10,c_1])).

cnf(c_3177,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k1_xboole_0)),X0)))) = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[status(thm)],[c_3148,c_119])).

cnf(c_4,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_214,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2711,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_214,c_213])).

cnf(c_3185,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X0)) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_3177,c_8,c_438,c_2711,c_2715])).

cnf(c_222,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_10,c_1])).

cnf(c_1023,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)) = k5_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_8,c_222])).

cnf(c_3186,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3185,c_438,c_1023])).

cnf(c_3445,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3186,c_438])).

cnf(c_223,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,X0)) ),
    inference(superposition,[status(thm)],[c_10,c_1])).

cnf(c_3469,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_3445,c_223])).

cnf(c_3471,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
    inference(demodulation,[status(thm)],[c_3469,c_8])).

cnf(c_150279,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_150278,c_3471])).

cnf(c_150280,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_150279])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:57:41 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 39.96/5.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 39.96/5.49  
% 39.96/5.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 39.96/5.49  
% 39.96/5.49  ------  iProver source info
% 39.96/5.49  
% 39.96/5.49  git: date: 2020-06-30 10:37:57 +0100
% 39.96/5.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 39.96/5.49  git: non_committed_changes: false
% 39.96/5.49  git: last_make_outside_of_git: false
% 39.96/5.49  
% 39.96/5.49  ------ 
% 39.96/5.49  
% 39.96/5.49  ------ Input Options
% 39.96/5.49  
% 39.96/5.49  --out_options                           all
% 39.96/5.49  --tptp_safe_out                         true
% 39.96/5.49  --problem_path                          ""
% 39.96/5.49  --include_path                          ""
% 39.96/5.49  --clausifier                            res/vclausify_rel
% 39.96/5.49  --clausifier_options                    ""
% 39.96/5.49  --stdin                                 false
% 39.96/5.49  --stats_out                             all
% 39.96/5.49  
% 39.96/5.49  ------ General Options
% 39.96/5.49  
% 39.96/5.49  --fof                                   false
% 39.96/5.49  --time_out_real                         305.
% 39.96/5.49  --time_out_virtual                      -1.
% 39.96/5.49  --symbol_type_check                     false
% 39.96/5.49  --clausify_out                          false
% 39.96/5.49  --sig_cnt_out                           false
% 39.96/5.49  --trig_cnt_out                          false
% 39.96/5.49  --trig_cnt_out_tolerance                1.
% 39.96/5.49  --trig_cnt_out_sk_spl                   false
% 39.96/5.49  --abstr_cl_out                          false
% 39.96/5.49  
% 39.96/5.49  ------ Global Options
% 39.96/5.49  
% 39.96/5.49  --schedule                              default
% 39.96/5.49  --add_important_lit                     false
% 39.96/5.49  --prop_solver_per_cl                    1000
% 39.96/5.49  --min_unsat_core                        false
% 39.96/5.49  --soft_assumptions                      false
% 39.96/5.49  --soft_lemma_size                       3
% 39.96/5.49  --prop_impl_unit_size                   0
% 39.96/5.49  --prop_impl_unit                        []
% 39.96/5.49  --share_sel_clauses                     true
% 39.96/5.49  --reset_solvers                         false
% 39.96/5.49  --bc_imp_inh                            [conj_cone]
% 39.96/5.49  --conj_cone_tolerance                   3.
% 39.96/5.49  --extra_neg_conj                        none
% 39.96/5.49  --large_theory_mode                     true
% 39.96/5.49  --prolific_symb_bound                   200
% 39.96/5.49  --lt_threshold                          2000
% 39.96/5.49  --clause_weak_htbl                      true
% 39.96/5.49  --gc_record_bc_elim                     false
% 39.96/5.49  
% 39.96/5.49  ------ Preprocessing Options
% 39.96/5.49  
% 39.96/5.49  --preprocessing_flag                    true
% 39.96/5.49  --time_out_prep_mult                    0.1
% 39.96/5.49  --splitting_mode                        input
% 39.96/5.49  --splitting_grd                         true
% 39.96/5.49  --splitting_cvd                         false
% 39.96/5.49  --splitting_cvd_svl                     false
% 39.96/5.49  --splitting_nvd                         32
% 39.96/5.49  --sub_typing                            true
% 39.96/5.49  --prep_gs_sim                           true
% 39.96/5.49  --prep_unflatten                        true
% 39.96/5.49  --prep_res_sim                          true
% 39.96/5.49  --prep_upred                            true
% 39.96/5.49  --prep_sem_filter                       exhaustive
% 39.96/5.49  --prep_sem_filter_out                   false
% 39.96/5.49  --pred_elim                             true
% 39.96/5.49  --res_sim_input                         true
% 39.96/5.49  --eq_ax_congr_red                       true
% 39.96/5.49  --pure_diseq_elim                       true
% 39.96/5.49  --brand_transform                       false
% 39.96/5.49  --non_eq_to_eq                          false
% 39.96/5.49  --prep_def_merge                        true
% 39.96/5.49  --prep_def_merge_prop_impl              false
% 39.96/5.49  --prep_def_merge_mbd                    true
% 39.96/5.49  --prep_def_merge_tr_red                 false
% 39.96/5.49  --prep_def_merge_tr_cl                  false
% 39.96/5.49  --smt_preprocessing                     true
% 39.96/5.49  --smt_ac_axioms                         fast
% 39.96/5.49  --preprocessed_out                      false
% 39.96/5.49  --preprocessed_stats                    false
% 39.96/5.49  
% 39.96/5.49  ------ Abstraction refinement Options
% 39.96/5.49  
% 39.96/5.49  --abstr_ref                             []
% 39.96/5.49  --abstr_ref_prep                        false
% 39.96/5.49  --abstr_ref_until_sat                   false
% 39.96/5.49  --abstr_ref_sig_restrict                funpre
% 39.96/5.49  --abstr_ref_af_restrict_to_split_sk     false
% 39.96/5.49  --abstr_ref_under                       []
% 39.96/5.49  
% 39.96/5.49  ------ SAT Options
% 39.96/5.49  
% 39.96/5.49  --sat_mode                              false
% 39.96/5.49  --sat_fm_restart_options                ""
% 39.96/5.49  --sat_gr_def                            false
% 39.96/5.49  --sat_epr_types                         true
% 39.96/5.49  --sat_non_cyclic_types                  false
% 39.96/5.49  --sat_finite_models                     false
% 39.96/5.49  --sat_fm_lemmas                         false
% 39.96/5.49  --sat_fm_prep                           false
% 39.96/5.49  --sat_fm_uc_incr                        true
% 39.96/5.49  --sat_out_model                         small
% 39.96/5.49  --sat_out_clauses                       false
% 39.96/5.49  
% 39.96/5.49  ------ QBF Options
% 39.96/5.49  
% 39.96/5.49  --qbf_mode                              false
% 39.96/5.49  --qbf_elim_univ                         false
% 39.96/5.49  --qbf_dom_inst                          none
% 39.96/5.49  --qbf_dom_pre_inst                      false
% 39.96/5.49  --qbf_sk_in                             false
% 39.96/5.49  --qbf_pred_elim                         true
% 39.96/5.49  --qbf_split                             512
% 39.96/5.49  
% 39.96/5.49  ------ BMC1 Options
% 39.96/5.49  
% 39.96/5.49  --bmc1_incremental                      false
% 39.96/5.49  --bmc1_axioms                           reachable_all
% 39.96/5.49  --bmc1_min_bound                        0
% 39.96/5.49  --bmc1_max_bound                        -1
% 39.96/5.49  --bmc1_max_bound_default                -1
% 39.96/5.49  --bmc1_symbol_reachability              true
% 39.96/5.49  --bmc1_property_lemmas                  false
% 39.96/5.49  --bmc1_k_induction                      false
% 39.96/5.49  --bmc1_non_equiv_states                 false
% 39.96/5.49  --bmc1_deadlock                         false
% 39.96/5.49  --bmc1_ucm                              false
% 39.96/5.49  --bmc1_add_unsat_core                   none
% 39.96/5.49  --bmc1_unsat_core_children              false
% 39.96/5.49  --bmc1_unsat_core_extrapolate_axioms    false
% 39.96/5.49  --bmc1_out_stat                         full
% 39.96/5.49  --bmc1_ground_init                      false
% 39.96/5.49  --bmc1_pre_inst_next_state              false
% 39.96/5.49  --bmc1_pre_inst_state                   false
% 39.96/5.49  --bmc1_pre_inst_reach_state             false
% 39.96/5.49  --bmc1_out_unsat_core                   false
% 39.96/5.49  --bmc1_aig_witness_out                  false
% 39.96/5.49  --bmc1_verbose                          false
% 39.96/5.49  --bmc1_dump_clauses_tptp                false
% 39.96/5.49  --bmc1_dump_unsat_core_tptp             false
% 39.96/5.49  --bmc1_dump_file                        -
% 39.96/5.49  --bmc1_ucm_expand_uc_limit              128
% 39.96/5.49  --bmc1_ucm_n_expand_iterations          6
% 39.96/5.49  --bmc1_ucm_extend_mode                  1
% 39.96/5.49  --bmc1_ucm_init_mode                    2
% 39.96/5.49  --bmc1_ucm_cone_mode                    none
% 39.96/5.49  --bmc1_ucm_reduced_relation_type        0
% 39.96/5.49  --bmc1_ucm_relax_model                  4
% 39.96/5.49  --bmc1_ucm_full_tr_after_sat            true
% 39.96/5.49  --bmc1_ucm_expand_neg_assumptions       false
% 39.96/5.49  --bmc1_ucm_layered_model                none
% 39.96/5.49  --bmc1_ucm_max_lemma_size               10
% 39.96/5.49  
% 39.96/5.49  ------ AIG Options
% 39.96/5.49  
% 39.96/5.49  --aig_mode                              false
% 39.96/5.49  
% 39.96/5.49  ------ Instantiation Options
% 39.96/5.49  
% 39.96/5.49  --instantiation_flag                    true
% 39.96/5.49  --inst_sos_flag                         true
% 39.96/5.49  --inst_sos_phase                        true
% 39.96/5.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 39.96/5.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 39.96/5.49  --inst_lit_sel_side                     num_symb
% 39.96/5.49  --inst_solver_per_active                1400
% 39.96/5.49  --inst_solver_calls_frac                1.
% 39.96/5.49  --inst_passive_queue_type               priority_queues
% 39.96/5.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 39.96/5.49  --inst_passive_queues_freq              [25;2]
% 39.96/5.49  --inst_dismatching                      true
% 39.96/5.49  --inst_eager_unprocessed_to_passive     true
% 39.96/5.49  --inst_prop_sim_given                   true
% 39.96/5.49  --inst_prop_sim_new                     false
% 39.96/5.49  --inst_subs_new                         false
% 39.96/5.49  --inst_eq_res_simp                      false
% 39.96/5.49  --inst_subs_given                       false
% 39.96/5.49  --inst_orphan_elimination               true
% 39.96/5.49  --inst_learning_loop_flag               true
% 39.96/5.49  --inst_learning_start                   3000
% 39.96/5.49  --inst_learning_factor                  2
% 39.96/5.49  --inst_start_prop_sim_after_learn       3
% 39.96/5.49  --inst_sel_renew                        solver
% 39.96/5.49  --inst_lit_activity_flag                true
% 39.96/5.49  --inst_restr_to_given                   false
% 39.96/5.49  --inst_activity_threshold               500
% 39.96/5.49  --inst_out_proof                        true
% 39.96/5.49  
% 39.96/5.49  ------ Resolution Options
% 39.96/5.49  
% 39.96/5.49  --resolution_flag                       true
% 39.96/5.49  --res_lit_sel                           adaptive
% 39.96/5.49  --res_lit_sel_side                      none
% 39.96/5.49  --res_ordering                          kbo
% 39.96/5.49  --res_to_prop_solver                    active
% 39.96/5.49  --res_prop_simpl_new                    false
% 39.96/5.49  --res_prop_simpl_given                  true
% 39.96/5.49  --res_passive_queue_type                priority_queues
% 39.96/5.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 39.96/5.49  --res_passive_queues_freq               [15;5]
% 39.96/5.49  --res_forward_subs                      full
% 39.96/5.49  --res_backward_subs                     full
% 39.96/5.49  --res_forward_subs_resolution           true
% 39.96/5.49  --res_backward_subs_resolution          true
% 39.96/5.49  --res_orphan_elimination                true
% 39.96/5.49  --res_time_limit                        2.
% 39.96/5.49  --res_out_proof                         true
% 39.96/5.49  
% 39.96/5.49  ------ Superposition Options
% 39.96/5.49  
% 39.96/5.49  --superposition_flag                    true
% 39.96/5.49  --sup_passive_queue_type                priority_queues
% 39.96/5.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 39.96/5.49  --sup_passive_queues_freq               [8;1;4]
% 39.96/5.49  --demod_completeness_check              fast
% 39.96/5.49  --demod_use_ground                      true
% 39.96/5.49  --sup_to_prop_solver                    passive
% 39.96/5.49  --sup_prop_simpl_new                    true
% 39.96/5.49  --sup_prop_simpl_given                  true
% 39.96/5.49  --sup_fun_splitting                     true
% 39.96/5.49  --sup_smt_interval                      50000
% 39.96/5.49  
% 39.96/5.49  ------ Superposition Simplification Setup
% 39.96/5.49  
% 39.96/5.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 39.96/5.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 39.96/5.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 39.96/5.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 39.96/5.49  --sup_full_triv                         [TrivRules;PropSubs]
% 39.96/5.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 39.96/5.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 39.96/5.49  --sup_immed_triv                        [TrivRules]
% 39.96/5.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 39.96/5.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 39.96/5.49  --sup_immed_bw_main                     []
% 39.96/5.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 39.96/5.49  --sup_input_triv                        [Unflattening;TrivRules]
% 39.96/5.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 39.96/5.49  --sup_input_bw                          []
% 39.96/5.49  
% 39.96/5.49  ------ Combination Options
% 39.96/5.49  
% 39.96/5.49  --comb_res_mult                         3
% 39.96/5.49  --comb_sup_mult                         2
% 39.96/5.49  --comb_inst_mult                        10
% 39.96/5.49  
% 39.96/5.49  ------ Debug Options
% 39.96/5.49  
% 39.96/5.49  --dbg_backtrace                         false
% 39.96/5.49  --dbg_dump_prop_clauses                 false
% 39.96/5.49  --dbg_dump_prop_clauses_file            -
% 39.96/5.49  --dbg_out_stat                          false
% 39.96/5.49  ------ Parsing...
% 39.96/5.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 39.96/5.49  
% 39.96/5.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 39.96/5.49  
% 39.96/5.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 39.96/5.49  
% 39.96/5.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 39.96/5.49  ------ Proving...
% 39.96/5.49  ------ Problem Properties 
% 39.96/5.49  
% 39.96/5.49  
% 39.96/5.49  clauses                                 12
% 39.96/5.49  conjectures                             1
% 39.96/5.49  EPR                                     2
% 39.96/5.49  Horn                                    12
% 39.96/5.49  unary                                   10
% 39.96/5.49  binary                                  1
% 39.96/5.50  lits                                    15
% 39.96/5.50  lits eq                                 9
% 39.96/5.50  fd_pure                                 0
% 39.96/5.50  fd_pseudo                               0
% 39.96/5.50  fd_cond                                 0
% 39.96/5.50  fd_pseudo_cond                          1
% 39.96/5.50  AC symbols                              1
% 39.96/5.50  
% 39.96/5.50  ------ Schedule dynamic 5 is on 
% 39.96/5.50  
% 39.96/5.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 39.96/5.50  
% 39.96/5.50  
% 39.96/5.50  ------ 
% 39.96/5.50  Current options:
% 39.96/5.50  ------ 
% 39.96/5.50  
% 39.96/5.50  ------ Input Options
% 39.96/5.50  
% 39.96/5.50  --out_options                           all
% 39.96/5.50  --tptp_safe_out                         true
% 39.96/5.50  --problem_path                          ""
% 39.96/5.50  --include_path                          ""
% 39.96/5.50  --clausifier                            res/vclausify_rel
% 39.96/5.50  --clausifier_options                    ""
% 39.96/5.50  --stdin                                 false
% 39.96/5.50  --stats_out                             all
% 39.96/5.50  
% 39.96/5.50  ------ General Options
% 39.96/5.50  
% 39.96/5.50  --fof                                   false
% 39.96/5.50  --time_out_real                         305.
% 39.96/5.50  --time_out_virtual                      -1.
% 39.96/5.50  --symbol_type_check                     false
% 39.96/5.50  --clausify_out                          false
% 39.96/5.50  --sig_cnt_out                           false
% 39.96/5.50  --trig_cnt_out                          false
% 39.96/5.50  --trig_cnt_out_tolerance                1.
% 39.96/5.50  --trig_cnt_out_sk_spl                   false
% 39.96/5.50  --abstr_cl_out                          false
% 39.96/5.50  
% 39.96/5.50  ------ Global Options
% 39.96/5.50  
% 39.96/5.50  --schedule                              default
% 39.96/5.50  --add_important_lit                     false
% 39.96/5.50  --prop_solver_per_cl                    1000
% 39.96/5.50  --min_unsat_core                        false
% 39.96/5.50  --soft_assumptions                      false
% 39.96/5.50  --soft_lemma_size                       3
% 39.96/5.50  --prop_impl_unit_size                   0
% 39.96/5.50  --prop_impl_unit                        []
% 39.96/5.50  --share_sel_clauses                     true
% 39.96/5.50  --reset_solvers                         false
% 39.96/5.50  --bc_imp_inh                            [conj_cone]
% 39.96/5.50  --conj_cone_tolerance                   3.
% 39.96/5.50  --extra_neg_conj                        none
% 39.96/5.50  --large_theory_mode                     true
% 39.96/5.50  --prolific_symb_bound                   200
% 39.96/5.50  --lt_threshold                          2000
% 39.96/5.50  --clause_weak_htbl                      true
% 39.96/5.50  --gc_record_bc_elim                     false
% 39.96/5.50  
% 39.96/5.50  ------ Preprocessing Options
% 39.96/5.50  
% 39.96/5.50  --preprocessing_flag                    true
% 39.96/5.50  --time_out_prep_mult                    0.1
% 39.96/5.50  --splitting_mode                        input
% 39.96/5.50  --splitting_grd                         true
% 39.96/5.50  --splitting_cvd                         false
% 39.96/5.50  --splitting_cvd_svl                     false
% 39.96/5.50  --splitting_nvd                         32
% 39.96/5.50  --sub_typing                            true
% 39.96/5.50  --prep_gs_sim                           true
% 39.96/5.50  --prep_unflatten                        true
% 39.96/5.50  --prep_res_sim                          true
% 39.96/5.50  --prep_upred                            true
% 39.96/5.50  --prep_sem_filter                       exhaustive
% 39.96/5.50  --prep_sem_filter_out                   false
% 39.96/5.50  --pred_elim                             true
% 39.96/5.50  --res_sim_input                         true
% 39.96/5.50  --eq_ax_congr_red                       true
% 39.96/5.50  --pure_diseq_elim                       true
% 39.96/5.50  --brand_transform                       false
% 39.96/5.50  --non_eq_to_eq                          false
% 39.96/5.50  --prep_def_merge                        true
% 39.96/5.50  --prep_def_merge_prop_impl              false
% 39.96/5.50  --prep_def_merge_mbd                    true
% 39.96/5.50  --prep_def_merge_tr_red                 false
% 39.96/5.50  --prep_def_merge_tr_cl                  false
% 39.96/5.50  --smt_preprocessing                     true
% 39.96/5.50  --smt_ac_axioms                         fast
% 39.96/5.50  --preprocessed_out                      false
% 39.96/5.50  --preprocessed_stats                    false
% 39.96/5.50  
% 39.96/5.50  ------ Abstraction refinement Options
% 39.96/5.50  
% 39.96/5.50  --abstr_ref                             []
% 39.96/5.50  --abstr_ref_prep                        false
% 39.96/5.50  --abstr_ref_until_sat                   false
% 39.96/5.50  --abstr_ref_sig_restrict                funpre
% 39.96/5.50  --abstr_ref_af_restrict_to_split_sk     false
% 39.96/5.50  --abstr_ref_under                       []
% 39.96/5.50  
% 39.96/5.50  ------ SAT Options
% 39.96/5.50  
% 39.96/5.50  --sat_mode                              false
% 39.96/5.50  --sat_fm_restart_options                ""
% 39.96/5.50  --sat_gr_def                            false
% 39.96/5.50  --sat_epr_types                         true
% 39.96/5.50  --sat_non_cyclic_types                  false
% 39.96/5.50  --sat_finite_models                     false
% 39.96/5.50  --sat_fm_lemmas                         false
% 39.96/5.50  --sat_fm_prep                           false
% 39.96/5.50  --sat_fm_uc_incr                        true
% 39.96/5.50  --sat_out_model                         small
% 39.96/5.50  --sat_out_clauses                       false
% 39.96/5.50  
% 39.96/5.50  ------ QBF Options
% 39.96/5.50  
% 39.96/5.50  --qbf_mode                              false
% 39.96/5.50  --qbf_elim_univ                         false
% 39.96/5.50  --qbf_dom_inst                          none
% 39.96/5.50  --qbf_dom_pre_inst                      false
% 39.96/5.50  --qbf_sk_in                             false
% 39.96/5.50  --qbf_pred_elim                         true
% 39.96/5.50  --qbf_split                             512
% 39.96/5.50  
% 39.96/5.50  ------ BMC1 Options
% 39.96/5.50  
% 39.96/5.50  --bmc1_incremental                      false
% 39.96/5.50  --bmc1_axioms                           reachable_all
% 39.96/5.50  --bmc1_min_bound                        0
% 39.96/5.50  --bmc1_max_bound                        -1
% 39.96/5.50  --bmc1_max_bound_default                -1
% 39.96/5.50  --bmc1_symbol_reachability              true
% 39.96/5.50  --bmc1_property_lemmas                  false
% 39.96/5.50  --bmc1_k_induction                      false
% 39.96/5.50  --bmc1_non_equiv_states                 false
% 39.96/5.50  --bmc1_deadlock                         false
% 39.96/5.50  --bmc1_ucm                              false
% 39.96/5.50  --bmc1_add_unsat_core                   none
% 39.96/5.50  --bmc1_unsat_core_children              false
% 39.96/5.50  --bmc1_unsat_core_extrapolate_axioms    false
% 39.96/5.50  --bmc1_out_stat                         full
% 39.96/5.50  --bmc1_ground_init                      false
% 39.96/5.50  --bmc1_pre_inst_next_state              false
% 39.96/5.50  --bmc1_pre_inst_state                   false
% 39.96/5.50  --bmc1_pre_inst_reach_state             false
% 39.96/5.50  --bmc1_out_unsat_core                   false
% 39.96/5.50  --bmc1_aig_witness_out                  false
% 39.96/5.50  --bmc1_verbose                          false
% 39.96/5.50  --bmc1_dump_clauses_tptp                false
% 39.96/5.50  --bmc1_dump_unsat_core_tptp             false
% 39.96/5.50  --bmc1_dump_file                        -
% 39.96/5.50  --bmc1_ucm_expand_uc_limit              128
% 39.96/5.50  --bmc1_ucm_n_expand_iterations          6
% 39.96/5.50  --bmc1_ucm_extend_mode                  1
% 39.96/5.50  --bmc1_ucm_init_mode                    2
% 39.96/5.50  --bmc1_ucm_cone_mode                    none
% 39.96/5.50  --bmc1_ucm_reduced_relation_type        0
% 39.96/5.50  --bmc1_ucm_relax_model                  4
% 39.96/5.50  --bmc1_ucm_full_tr_after_sat            true
% 39.96/5.50  --bmc1_ucm_expand_neg_assumptions       false
% 39.96/5.50  --bmc1_ucm_layered_model                none
% 39.96/5.50  --bmc1_ucm_max_lemma_size               10
% 39.96/5.50  
% 39.96/5.50  ------ AIG Options
% 39.96/5.50  
% 39.96/5.50  --aig_mode                              false
% 39.96/5.50  
% 39.96/5.50  ------ Instantiation Options
% 39.96/5.50  
% 39.96/5.50  --instantiation_flag                    true
% 39.96/5.50  --inst_sos_flag                         true
% 39.96/5.50  --inst_sos_phase                        true
% 39.96/5.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 39.96/5.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 39.96/5.50  --inst_lit_sel_side                     none
% 39.96/5.50  --inst_solver_per_active                1400
% 39.96/5.50  --inst_solver_calls_frac                1.
% 39.96/5.50  --inst_passive_queue_type               priority_queues
% 39.96/5.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 39.96/5.50  --inst_passive_queues_freq              [25;2]
% 39.96/5.50  --inst_dismatching                      true
% 39.96/5.50  --inst_eager_unprocessed_to_passive     true
% 39.96/5.50  --inst_prop_sim_given                   true
% 39.96/5.50  --inst_prop_sim_new                     false
% 39.96/5.50  --inst_subs_new                         false
% 39.96/5.50  --inst_eq_res_simp                      false
% 39.96/5.50  --inst_subs_given                       false
% 39.96/5.50  --inst_orphan_elimination               true
% 39.96/5.50  --inst_learning_loop_flag               true
% 39.96/5.50  --inst_learning_start                   3000
% 39.96/5.50  --inst_learning_factor                  2
% 39.96/5.50  --inst_start_prop_sim_after_learn       3
% 39.96/5.50  --inst_sel_renew                        solver
% 39.96/5.50  --inst_lit_activity_flag                true
% 39.96/5.50  --inst_restr_to_given                   false
% 39.96/5.50  --inst_activity_threshold               500
% 39.96/5.50  --inst_out_proof                        true
% 39.96/5.50  
% 39.96/5.50  ------ Resolution Options
% 39.96/5.50  
% 39.96/5.50  --resolution_flag                       false
% 39.96/5.50  --res_lit_sel                           adaptive
% 39.96/5.50  --res_lit_sel_side                      none
% 39.96/5.50  --res_ordering                          kbo
% 39.96/5.50  --res_to_prop_solver                    active
% 39.96/5.50  --res_prop_simpl_new                    false
% 39.96/5.50  --res_prop_simpl_given                  true
% 39.96/5.50  --res_passive_queue_type                priority_queues
% 39.96/5.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 39.96/5.50  --res_passive_queues_freq               [15;5]
% 39.96/5.50  --res_forward_subs                      full
% 39.96/5.50  --res_backward_subs                     full
% 39.96/5.50  --res_forward_subs_resolution           true
% 39.96/5.50  --res_backward_subs_resolution          true
% 39.96/5.50  --res_orphan_elimination                true
% 39.96/5.50  --res_time_limit                        2.
% 39.96/5.50  --res_out_proof                         true
% 39.96/5.50  
% 39.96/5.50  ------ Superposition Options
% 39.96/5.50  
% 39.96/5.50  --superposition_flag                    true
% 39.96/5.50  --sup_passive_queue_type                priority_queues
% 39.96/5.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 39.96/5.50  --sup_passive_queues_freq               [8;1;4]
% 39.96/5.50  --demod_completeness_check              fast
% 39.96/5.50  --demod_use_ground                      true
% 39.96/5.50  --sup_to_prop_solver                    passive
% 39.96/5.50  --sup_prop_simpl_new                    true
% 39.96/5.50  --sup_prop_simpl_given                  true
% 39.96/5.50  --sup_fun_splitting                     true
% 39.96/5.50  --sup_smt_interval                      50000
% 39.96/5.50  
% 39.96/5.50  ------ Superposition Simplification Setup
% 39.96/5.50  
% 39.96/5.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 39.96/5.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 39.96/5.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 39.96/5.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 39.96/5.50  --sup_full_triv                         [TrivRules;PropSubs]
% 39.96/5.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 39.96/5.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 39.96/5.50  --sup_immed_triv                        [TrivRules]
% 39.96/5.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 39.96/5.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 39.96/5.50  --sup_immed_bw_main                     []
% 39.96/5.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 39.96/5.50  --sup_input_triv                        [Unflattening;TrivRules]
% 39.96/5.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 39.96/5.50  --sup_input_bw                          []
% 39.96/5.50  
% 39.96/5.50  ------ Combination Options
% 39.96/5.50  
% 39.96/5.50  --comb_res_mult                         3
% 39.96/5.50  --comb_sup_mult                         2
% 39.96/5.50  --comb_inst_mult                        10
% 39.96/5.50  
% 39.96/5.50  ------ Debug Options
% 39.96/5.50  
% 39.96/5.50  --dbg_backtrace                         false
% 39.96/5.50  --dbg_dump_prop_clauses                 false
% 39.96/5.50  --dbg_dump_prop_clauses_file            -
% 39.96/5.50  --dbg_out_stat                          false
% 39.96/5.50  
% 39.96/5.50  
% 39.96/5.50  
% 39.96/5.50  
% 39.96/5.50  ------ Proving...
% 39.96/5.50  
% 39.96/5.50  
% 39.96/5.50  % SZS status Theorem for theBenchmark.p
% 39.96/5.50  
% 39.96/5.50   Resolution empty clause
% 39.96/5.50  
% 39.96/5.50  % SZS output start CNFRefutation for theBenchmark.p
% 39.96/5.50  
% 39.96/5.50  fof(f19,axiom,(
% 39.96/5.50    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))),
% 39.96/5.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.96/5.50  
% 39.96/5.50  fof(f48,plain,(
% 39.96/5.50    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 39.96/5.50    inference(cnf_transformation,[],[f19])).
% 39.96/5.50  
% 39.96/5.50  fof(f12,axiom,(
% 39.96/5.50    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 39.96/5.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.96/5.50  
% 39.96/5.50  fof(f41,plain,(
% 39.96/5.50    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 39.96/5.50    inference(cnf_transformation,[],[f12])).
% 39.96/5.50  
% 39.96/5.50  fof(f56,plain,(
% 39.96/5.50    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 39.96/5.50    inference(definition_unfolding,[],[f41,f55])).
% 39.96/5.50  
% 39.96/5.50  fof(f13,axiom,(
% 39.96/5.50    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 39.96/5.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.96/5.50  
% 39.96/5.50  fof(f42,plain,(
% 39.96/5.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 39.96/5.50    inference(cnf_transformation,[],[f13])).
% 39.96/5.50  
% 39.96/5.50  fof(f14,axiom,(
% 39.96/5.50    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 39.96/5.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.96/5.50  
% 39.96/5.50  fof(f43,plain,(
% 39.96/5.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 39.96/5.50    inference(cnf_transformation,[],[f14])).
% 39.96/5.50  
% 39.96/5.50  fof(f15,axiom,(
% 39.96/5.50    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 39.96/5.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.96/5.50  
% 39.96/5.50  fof(f44,plain,(
% 39.96/5.50    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 39.96/5.50    inference(cnf_transformation,[],[f15])).
% 39.96/5.50  
% 39.96/5.50  fof(f16,axiom,(
% 39.96/5.50    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 39.96/5.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.96/5.50  
% 39.96/5.50  fof(f45,plain,(
% 39.96/5.50    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 39.96/5.50    inference(cnf_transformation,[],[f16])).
% 39.96/5.50  
% 39.96/5.50  fof(f17,axiom,(
% 39.96/5.50    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 39.96/5.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.96/5.50  
% 39.96/5.50  fof(f46,plain,(
% 39.96/5.50    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 39.96/5.50    inference(cnf_transformation,[],[f17])).
% 39.96/5.50  
% 39.96/5.50  fof(f18,axiom,(
% 39.96/5.50    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 39.96/5.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.96/5.50  
% 39.96/5.50  fof(f47,plain,(
% 39.96/5.50    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 39.96/5.50    inference(cnf_transformation,[],[f18])).
% 39.96/5.50  
% 39.96/5.50  fof(f51,plain,(
% 39.96/5.50    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 39.96/5.50    inference(definition_unfolding,[],[f46,f47])).
% 39.96/5.50  
% 39.96/5.50  fof(f52,plain,(
% 39.96/5.50    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 39.96/5.50    inference(definition_unfolding,[],[f45,f51])).
% 39.96/5.50  
% 39.96/5.50  fof(f53,plain,(
% 39.96/5.50    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 39.96/5.50    inference(definition_unfolding,[],[f44,f52])).
% 39.96/5.50  
% 39.96/5.50  fof(f54,plain,(
% 39.96/5.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 39.96/5.50    inference(definition_unfolding,[],[f43,f53])).
% 39.96/5.50  
% 39.96/5.50  fof(f55,plain,(
% 39.96/5.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 39.96/5.50    inference(definition_unfolding,[],[f42,f54])).
% 39.96/5.50  
% 39.96/5.50  fof(f60,plain,(
% 39.96/5.50    ( ! [X0,X1] : (r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 39.96/5.50    inference(definition_unfolding,[],[f48,f56,f55])).
% 39.96/5.50  
% 39.96/5.50  fof(f5,axiom,(
% 39.96/5.50    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 39.96/5.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.96/5.50  
% 39.96/5.50  fof(f22,plain,(
% 39.96/5.50    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 39.96/5.50    inference(ennf_transformation,[],[f5])).
% 39.96/5.50  
% 39.96/5.50  fof(f34,plain,(
% 39.96/5.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 39.96/5.50    inference(cnf_transformation,[],[f22])).
% 39.96/5.50  
% 39.96/5.50  fof(f1,axiom,(
% 39.96/5.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 39.96/5.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.96/5.50  
% 39.96/5.50  fof(f28,plain,(
% 39.96/5.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 39.96/5.50    inference(cnf_transformation,[],[f1])).
% 39.96/5.50  
% 39.96/5.50  fof(f20,conjecture,(
% 39.96/5.50    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) = k2_tarski(X0,X1)),
% 39.96/5.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.96/5.50  
% 39.96/5.50  fof(f21,negated_conjecture,(
% 39.96/5.50    ~! [X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) = k2_tarski(X0,X1)),
% 39.96/5.50    inference(negated_conjecture,[],[f20])).
% 39.96/5.50  
% 39.96/5.50  fof(f23,plain,(
% 39.96/5.50    ? [X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) != k2_tarski(X0,X1)),
% 39.96/5.50    inference(ennf_transformation,[],[f21])).
% 39.96/5.50  
% 39.96/5.50  fof(f26,plain,(
% 39.96/5.50    ? [X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) != k2_tarski(X0,X1) => k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1)) != k2_tarski(sK0,sK1)),
% 39.96/5.50    introduced(choice_axiom,[])).
% 39.96/5.50  
% 39.96/5.50  fof(f27,plain,(
% 39.96/5.50    k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1)) != k2_tarski(sK0,sK1)),
% 39.96/5.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f26])).
% 39.96/5.50  
% 39.96/5.50  fof(f49,plain,(
% 39.96/5.50    k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1)) != k2_tarski(sK0,sK1)),
% 39.96/5.50    inference(cnf_transformation,[],[f27])).
% 39.96/5.50  
% 39.96/5.50  fof(f11,axiom,(
% 39.96/5.50    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 39.96/5.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.96/5.50  
% 39.96/5.50  fof(f40,plain,(
% 39.96/5.50    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 39.96/5.50    inference(cnf_transformation,[],[f11])).
% 39.96/5.50  
% 39.96/5.50  fof(f4,axiom,(
% 39.96/5.50    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 39.96/5.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.96/5.50  
% 39.96/5.50  fof(f33,plain,(
% 39.96/5.50    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 39.96/5.50    inference(cnf_transformation,[],[f4])).
% 39.96/5.50  
% 39.96/5.50  fof(f50,plain,(
% 39.96/5.50    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 39.96/5.50    inference(definition_unfolding,[],[f40,f33])).
% 39.96/5.50  
% 39.96/5.50  fof(f61,plain,(
% 39.96/5.50    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),
% 39.96/5.50    inference(definition_unfolding,[],[f49,f50,f56,f55,f55])).
% 39.96/5.50  
% 39.96/5.50  fof(f6,axiom,(
% 39.96/5.50    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 39.96/5.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.96/5.50  
% 39.96/5.50  fof(f35,plain,(
% 39.96/5.50    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 39.96/5.50    inference(cnf_transformation,[],[f6])).
% 39.96/5.50  
% 39.96/5.50  fof(f57,plain,(
% 39.96/5.50    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 39.96/5.50    inference(definition_unfolding,[],[f35,f33])).
% 39.96/5.50  
% 39.96/5.50  fof(f9,axiom,(
% 39.96/5.50    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 39.96/5.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.96/5.50  
% 39.96/5.50  fof(f38,plain,(
% 39.96/5.50    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 39.96/5.50    inference(cnf_transformation,[],[f9])).
% 39.96/5.50  
% 39.96/5.50  fof(f59,plain,(
% 39.96/5.50    ( ! [X0,X1] : (r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) )),
% 39.96/5.50    inference(definition_unfolding,[],[f38,f50])).
% 39.96/5.50  
% 39.96/5.50  fof(f8,axiom,(
% 39.96/5.50    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 39.96/5.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.96/5.50  
% 39.96/5.50  fof(f37,plain,(
% 39.96/5.50    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 39.96/5.50    inference(cnf_transformation,[],[f8])).
% 39.96/5.50  
% 39.96/5.50  fof(f2,axiom,(
% 39.96/5.50    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 39.96/5.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.96/5.50  
% 39.96/5.50  fof(f29,plain,(
% 39.96/5.50    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 39.96/5.50    inference(cnf_transformation,[],[f2])).
% 39.96/5.50  
% 39.96/5.50  fof(f7,axiom,(
% 39.96/5.50    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 39.96/5.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.96/5.50  
% 39.96/5.50  fof(f36,plain,(
% 39.96/5.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 39.96/5.50    inference(cnf_transformation,[],[f7])).
% 39.96/5.50  
% 39.96/5.50  fof(f58,plain,(
% 39.96/5.50    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),X1))) )),
% 39.96/5.50    inference(definition_unfolding,[],[f36,f33,f33,f50])).
% 39.96/5.50  
% 39.96/5.50  fof(f10,axiom,(
% 39.96/5.50    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 39.96/5.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.96/5.50  
% 39.96/5.50  fof(f39,plain,(
% 39.96/5.50    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 39.96/5.50    inference(cnf_transformation,[],[f10])).
% 39.96/5.50  
% 39.96/5.50  fof(f3,axiom,(
% 39.96/5.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 39.96/5.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.96/5.50  
% 39.96/5.50  fof(f24,plain,(
% 39.96/5.50    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 39.96/5.50    inference(nnf_transformation,[],[f3])).
% 39.96/5.50  
% 39.96/5.50  fof(f25,plain,(
% 39.96/5.50    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 39.96/5.50    inference(flattening,[],[f24])).
% 39.96/5.50  
% 39.96/5.50  fof(f30,plain,(
% 39.96/5.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 39.96/5.50    inference(cnf_transformation,[],[f25])).
% 39.96/5.50  
% 39.96/5.50  fof(f63,plain,(
% 39.96/5.50    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 39.96/5.50    inference(equality_resolution,[],[f30])).
% 39.96/5.50  
% 39.96/5.50  cnf(c_11,plain,
% 39.96/5.50      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
% 39.96/5.50      inference(cnf_transformation,[],[f60]) ).
% 39.96/5.50  
% 39.96/5.50  cnf(c_211,plain,
% 39.96/5.50      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = iProver_top ),
% 39.96/5.50      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 39.96/5.50  
% 39.96/5.50  cnf(c_5,plain,
% 39.96/5.50      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 39.96/5.50      inference(cnf_transformation,[],[f34]) ).
% 39.96/5.50  
% 39.96/5.50  cnf(c_213,plain,
% 39.96/5.50      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 39.96/5.50      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 39.96/5.50  
% 39.96/5.50  cnf(c_2713,plain,
% 39.96/5.50      ( k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
% 39.96/5.50      inference(superposition,[status(thm)],[c_211,c_213]) ).
% 39.96/5.50  
% 39.96/5.50  cnf(c_0,plain,
% 39.96/5.50      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 39.96/5.50      inference(cnf_transformation,[],[f28]) ).
% 39.96/5.50  
% 39.96/5.50  cnf(c_12,negated_conjecture,
% 39.96/5.50      ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
% 39.96/5.50      inference(cnf_transformation,[],[f61]) ).
% 39.96/5.50  
% 39.96/5.50  cnf(c_350,plain,
% 39.96/5.50      ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
% 39.96/5.50      inference(demodulation,[status(thm)],[c_0,c_12]) ).
% 39.96/5.50  
% 39.96/5.50  cnf(c_150278,plain,
% 39.96/5.50      ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
% 39.96/5.50      inference(demodulation,[status(thm)],[c_2713,c_350]) ).
% 39.96/5.50  
% 39.96/5.50  cnf(c_6,plain,
% 39.96/5.50      ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
% 39.96/5.50      inference(cnf_transformation,[],[f57]) ).
% 39.96/5.50  
% 39.96/5.50  cnf(c_9,plain,
% 39.96/5.50      ( r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
% 39.96/5.50      inference(cnf_transformation,[],[f59]) ).
% 39.96/5.50  
% 39.96/5.50  cnf(c_212,plain,
% 39.96/5.50      ( r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = iProver_top ),
% 39.96/5.50      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 39.96/5.50  
% 39.96/5.50  cnf(c_880,plain,
% 39.96/5.50      ( r1_tarski(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0)) = iProver_top ),
% 39.96/5.50      inference(superposition,[status(thm)],[c_6,c_212]) ).
% 39.96/5.50  
% 39.96/5.50  cnf(c_8,plain,
% 39.96/5.50      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 39.96/5.50      inference(cnf_transformation,[],[f37]) ).
% 39.96/5.50  
% 39.96/5.50  cnf(c_1,plain,
% 39.96/5.50      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 39.96/5.50      inference(cnf_transformation,[],[f29]) ).
% 39.96/5.50  
% 39.96/5.50  cnf(c_438,plain,
% 39.96/5.50      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 39.96/5.50      inference(superposition,[status(thm)],[c_8,c_1]) ).
% 39.96/5.50  
% 39.96/5.50  cnf(c_891,plain,
% 39.96/5.50      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 39.96/5.50      inference(light_normalisation,[status(thm)],[c_880,c_438]) ).
% 39.96/5.50  
% 39.96/5.50  cnf(c_2715,plain,
% 39.96/5.50      ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 39.96/5.50      inference(superposition,[status(thm)],[c_891,c_213]) ).
% 39.96/5.50  
% 39.96/5.50  cnf(c_3148,plain,
% 39.96/5.50      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 39.96/5.50      inference(superposition,[status(thm)],[c_2715,c_0]) ).
% 39.96/5.50  
% 39.96/5.50  cnf(c_7,plain,
% 39.96/5.50      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),X1)) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
% 39.96/5.50      inference(cnf_transformation,[],[f58]) ).
% 39.96/5.50  
% 39.96/5.50  cnf(c_10,plain,
% 39.96/5.50      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 39.96/5.50      inference(cnf_transformation,[],[f39]) ).
% 39.96/5.50  
% 39.96/5.50  cnf(c_119,plain,
% 39.96/5.50      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),X1)))) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
% 39.96/5.50      inference(theory_normalisation,[status(thm)],[c_7,c_10,c_1]) ).
% 39.96/5.50  
% 39.96/5.50  cnf(c_3177,plain,
% 39.96/5.50      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k1_xboole_0)),X0)))) = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) ),
% 39.96/5.50      inference(superposition,[status(thm)],[c_3148,c_119]) ).
% 39.96/5.50  
% 39.96/5.50  cnf(c_4,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f63]) ).
% 39.96/5.50  
% 39.96/5.50  cnf(c_214,plain,
% 39.96/5.50      ( r1_tarski(X0,X0) = iProver_top ),
% 39.96/5.50      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 39.96/5.50  
% 39.96/5.50  cnf(c_2711,plain,
% 39.96/5.50      ( k3_xboole_0(X0,X0) = X0 ),
% 39.96/5.50      inference(superposition,[status(thm)],[c_214,c_213]) ).
% 39.96/5.50  
% 39.96/5.50  cnf(c_3185,plain,
% 39.96/5.50      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X0)) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 39.96/5.50      inference(light_normalisation,
% 39.96/5.50                [status(thm)],
% 39.96/5.50                [c_3177,c_8,c_438,c_2711,c_2715]) ).
% 39.96/5.50  
% 39.96/5.50  cnf(c_222,plain,
% 39.96/5.50      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
% 39.96/5.50      inference(superposition,[status(thm)],[c_10,c_1]) ).
% 39.96/5.50  
% 39.96/5.50  cnf(c_1023,plain,
% 39.96/5.50      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)) = k5_xboole_0(X1,X0) ),
% 39.96/5.50      inference(superposition,[status(thm)],[c_8,c_222]) ).
% 39.96/5.50  
% 39.96/5.50  cnf(c_3186,plain,
% 39.96/5.50      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X0)) = k1_xboole_0 ),
% 39.96/5.50      inference(demodulation,[status(thm)],[c_3185,c_438,c_1023]) ).
% 39.96/5.50  
% 39.96/5.50  cnf(c_3445,plain,
% 39.96/5.50      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 39.96/5.50      inference(superposition,[status(thm)],[c_3186,c_438]) ).
% 39.96/5.50  
% 39.96/5.50  cnf(c_223,plain,
% 39.96/5.50      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,X0)) ),
% 39.96/5.50      inference(superposition,[status(thm)],[c_10,c_1]) ).
% 39.96/5.50  
% 39.96/5.50  cnf(c_3469,plain,
% 39.96/5.50      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(X1,k1_xboole_0) ),
% 39.96/5.50      inference(superposition,[status(thm)],[c_3445,c_223]) ).
% 39.96/5.50  
% 39.96/5.50  cnf(c_3471,plain,
% 39.96/5.50      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
% 39.96/5.50      inference(demodulation,[status(thm)],[c_3469,c_8]) ).
% 39.96/5.50  
% 39.96/5.50  cnf(c_150279,plain,
% 39.96/5.50      ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
% 39.96/5.50      inference(demodulation,[status(thm)],[c_150278,c_3471]) ).
% 39.96/5.50  
% 39.96/5.50  cnf(c_150280,plain,
% 39.96/5.50      ( $false ),
% 39.96/5.50      inference(equality_resolution_simp,[status(thm)],[c_150279]) ).
% 39.96/5.50  
% 39.96/5.50  
% 39.96/5.50  % SZS output end CNFRefutation for theBenchmark.p
% 39.96/5.50  
% 39.96/5.50  ------                               Statistics
% 39.96/5.50  
% 39.96/5.50  ------ General
% 39.96/5.50  
% 39.96/5.50  abstr_ref_over_cycles:                  0
% 39.96/5.50  abstr_ref_under_cycles:                 0
% 39.96/5.50  gc_basic_clause_elim:                   0
% 39.96/5.50  forced_gc_time:                         0
% 39.96/5.50  parsing_time:                           0.007
% 39.96/5.50  unif_index_cands_time:                  0.
% 39.96/5.50  unif_index_add_time:                    0.
% 39.96/5.50  orderings_time:                         0.
% 39.96/5.50  out_proof_time:                         0.008
% 39.96/5.50  total_time:                             4.962
% 39.96/5.50  num_of_symbols:                         38
% 39.96/5.50  num_of_terms:                           294334
% 39.96/5.50  
% 39.96/5.50  ------ Preprocessing
% 39.96/5.50  
% 39.96/5.50  num_of_splits:                          0
% 39.96/5.50  num_of_split_atoms:                     0
% 39.96/5.50  num_of_reused_defs:                     0
% 39.96/5.50  num_eq_ax_congr_red:                    0
% 39.96/5.50  num_of_sem_filtered_clauses:            1
% 39.96/5.50  num_of_subtypes:                        0
% 39.96/5.50  monotx_restored_types:                  0
% 39.96/5.50  sat_num_of_epr_types:                   0
% 39.96/5.50  sat_num_of_non_cyclic_types:            0
% 39.96/5.50  sat_guarded_non_collapsed_types:        0
% 39.96/5.50  num_pure_diseq_elim:                    0
% 39.96/5.50  simp_replaced_by:                       0
% 39.96/5.50  res_preprocessed:                       61
% 39.96/5.50  prep_upred:                             0
% 39.96/5.50  prep_unflattend:                        0
% 39.96/5.50  smt_new_axioms:                         0
% 39.96/5.50  pred_elim_cands:                        1
% 39.96/5.50  pred_elim:                              0
% 39.96/5.50  pred_elim_cl:                           0
% 39.96/5.50  pred_elim_cycles:                       2
% 39.96/5.50  merged_defs:                            0
% 39.96/5.50  merged_defs_ncl:                        0
% 39.96/5.50  bin_hyper_res:                          0
% 39.96/5.50  prep_cycles:                            4
% 39.96/5.50  pred_elim_time:                         0.
% 39.96/5.50  splitting_time:                         0.
% 39.96/5.50  sem_filter_time:                        0.
% 39.96/5.50  monotx_time:                            0.
% 39.96/5.50  subtype_inf_time:                       0.
% 39.96/5.50  
% 39.96/5.50  ------ Problem properties
% 39.96/5.50  
% 39.96/5.50  clauses:                                12
% 39.96/5.50  conjectures:                            1
% 39.96/5.50  epr:                                    2
% 39.96/5.50  horn:                                   12
% 39.96/5.50  ground:                                 1
% 39.96/5.50  unary:                                  10
% 39.96/5.50  binary:                                 1
% 39.96/5.50  lits:                                   15
% 39.96/5.50  lits_eq:                                9
% 39.96/5.50  fd_pure:                                0
% 39.96/5.50  fd_pseudo:                              0
% 39.96/5.50  fd_cond:                                0
% 39.96/5.50  fd_pseudo_cond:                         1
% 39.96/5.50  ac_symbols:                             1
% 39.96/5.50  
% 39.96/5.50  ------ Propositional Solver
% 39.96/5.50  
% 39.96/5.50  prop_solver_calls:                      35
% 39.96/5.50  prop_fast_solver_calls:                 750
% 39.96/5.50  smt_solver_calls:                       0
% 39.96/5.50  smt_fast_solver_calls:                  0
% 39.96/5.50  prop_num_of_clauses:                    23677
% 39.96/5.50  prop_preprocess_simplified:             31046
% 39.96/5.50  prop_fo_subsumed:                       0
% 39.96/5.50  prop_solver_time:                       0.
% 39.96/5.50  smt_solver_time:                        0.
% 39.96/5.50  smt_fast_solver_time:                   0.
% 39.96/5.50  prop_fast_solver_time:                  0.
% 39.96/5.50  prop_unsat_core_time:                   0.
% 39.96/5.50  
% 39.96/5.50  ------ QBF
% 39.96/5.50  
% 39.96/5.50  qbf_q_res:                              0
% 39.96/5.50  qbf_num_tautologies:                    0
% 39.96/5.50  qbf_prep_cycles:                        0
% 39.96/5.50  
% 39.96/5.50  ------ BMC1
% 39.96/5.50  
% 39.96/5.50  bmc1_current_bound:                     -1
% 39.96/5.50  bmc1_last_solved_bound:                 -1
% 39.96/5.50  bmc1_unsat_core_size:                   -1
% 39.96/5.50  bmc1_unsat_core_parents_size:           -1
% 39.96/5.50  bmc1_merge_next_fun:                    0
% 39.96/5.50  bmc1_unsat_core_clauses_time:           0.
% 39.96/5.50  
% 39.96/5.50  ------ Instantiation
% 39.96/5.50  
% 39.96/5.50  inst_num_of_clauses:                    4060
% 39.96/5.50  inst_num_in_passive:                    2339
% 39.96/5.50  inst_num_in_active:                     997
% 39.96/5.50  inst_num_in_unprocessed:                724
% 39.96/5.50  inst_num_of_loops:                      1340
% 39.96/5.50  inst_num_of_learning_restarts:          0
% 39.96/5.50  inst_num_moves_active_passive:          339
% 39.96/5.50  inst_lit_activity:                      0
% 39.96/5.50  inst_lit_activity_moves:                1
% 39.96/5.50  inst_num_tautologies:                   0
% 39.96/5.50  inst_num_prop_implied:                  0
% 39.96/5.50  inst_num_existing_simplified:           0
% 39.96/5.50  inst_num_eq_res_simplified:             0
% 39.96/5.50  inst_num_child_elim:                    0
% 39.96/5.50  inst_num_of_dismatching_blockings:      2398
% 39.96/5.50  inst_num_of_non_proper_insts:           5956
% 39.96/5.50  inst_num_of_duplicates:                 0
% 39.96/5.50  inst_inst_num_from_inst_to_res:         0
% 39.96/5.50  inst_dismatching_checking_time:         0.
% 39.96/5.50  
% 39.96/5.50  ------ Resolution
% 39.96/5.50  
% 39.96/5.50  res_num_of_clauses:                     0
% 39.96/5.50  res_num_in_passive:                     0
% 39.96/5.50  res_num_in_active:                      0
% 39.96/5.50  res_num_of_loops:                       65
% 39.96/5.50  res_forward_subset_subsumed:            1463
% 39.96/5.50  res_backward_subset_subsumed:           0
% 39.96/5.50  res_forward_subsumed:                   0
% 39.96/5.50  res_backward_subsumed:                  0
% 39.96/5.50  res_forward_subsumption_resolution:     0
% 39.96/5.50  res_backward_subsumption_resolution:    0
% 39.96/5.50  res_clause_to_clause_subsumption:       433885
% 39.96/5.50  res_orphan_elimination:                 0
% 39.96/5.50  res_tautology_del:                      401
% 39.96/5.50  res_num_eq_res_simplified:              0
% 39.96/5.50  res_num_sel_changes:                    0
% 39.96/5.50  res_moves_from_active_to_pass:          0
% 39.96/5.50  
% 39.96/5.50  ------ Superposition
% 39.96/5.50  
% 39.96/5.50  sup_time_total:                         0.
% 39.96/5.50  sup_time_generating:                    0.
% 39.96/5.50  sup_time_sim_full:                      0.
% 39.96/5.50  sup_time_sim_immed:                     0.
% 39.96/5.50  
% 39.96/5.50  sup_num_of_clauses:                     9110
% 39.96/5.50  sup_num_in_active:                      221
% 39.96/5.50  sup_num_in_passive:                     8889
% 39.96/5.50  sup_num_of_loops:                       266
% 39.96/5.50  sup_fw_superposition:                   37857
% 39.96/5.50  sup_bw_superposition:                   31246
% 39.96/5.50  sup_immediate_simplified:               39807
% 39.96/5.50  sup_given_eliminated:                   6
% 39.96/5.50  comparisons_done:                       0
% 39.96/5.50  comparisons_avoided:                    0
% 39.96/5.50  
% 39.96/5.50  ------ Simplifications
% 39.96/5.50  
% 39.96/5.50  
% 39.96/5.50  sim_fw_subset_subsumed:                 10
% 39.96/5.50  sim_bw_subset_subsumed:                 0
% 39.96/5.50  sim_fw_subsumed:                        2215
% 39.96/5.50  sim_bw_subsumed:                        44
% 39.96/5.50  sim_fw_subsumption_res:                 0
% 39.96/5.50  sim_bw_subsumption_res:                 0
% 39.96/5.50  sim_tautology_del:                      0
% 39.96/5.50  sim_eq_tautology_del:                   8521
% 39.96/5.50  sim_eq_res_simp:                        0
% 39.96/5.50  sim_fw_demodulated:                     39324
% 39.96/5.50  sim_bw_demodulated:                     352
% 39.96/5.50  sim_light_normalised:                   10871
% 39.96/5.50  sim_joinable_taut:                      1010
% 39.96/5.50  sim_joinable_simp:                      0
% 39.96/5.50  sim_ac_normalised:                      0
% 39.96/5.50  sim_smt_subsumption:                    0
% 39.96/5.50  
%------------------------------------------------------------------------------
