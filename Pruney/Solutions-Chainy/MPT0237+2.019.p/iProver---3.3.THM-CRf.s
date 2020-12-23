%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:31:44 EST 2020

% Result     : Theorem 7.26s
% Output     : CNFRefutation 7.26s
% Verified   : 
% Statistics : Number of formulae       :  106 (1423 expanded)
%              Number of clauses        :   48 ( 441 expanded)
%              Number of leaves         :   20 ( 349 expanded)
%              Depth                    :   25
%              Number of atoms          :  130 (1744 expanded)
%              Number of equality atoms :  120 (1401 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
        | X0 = X1 )
      & ( X0 != X1
        | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f9,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f15])).

fof(f49,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f42,f43])).

fof(f50,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f41,f49])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f40,f50])).

fof(f52,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f39,f51])).

fof(f53,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f38,f52])).

fof(f54,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f37,f53])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f46,f32,f54,f54,f54])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f31,f32])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f30,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f21])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f6,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f16,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f8,axiom,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f56,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f44,f36,f53])).

fof(f19,conjecture,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1] : k2_tarski(X0,X1) = k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1))) ),
    inference(negated_conjecture,[],[f19])).

fof(f25,plain,(
    ? [X0,X1] : k2_tarski(X0,X1) != k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1))) ),
    inference(ennf_transformation,[],[f20])).

fof(f27,plain,
    ( ? [X0,X1] : k2_tarski(X0,X1) != k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1)))
   => k2_tarski(sK0,sK1) != k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK1))) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    k2_tarski(sK0,sK1) != k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f27])).

fof(f48,plain,(
    k2_tarski(sK0,sK1) != k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK1))) ),
    inference(cnf_transformation,[],[f28])).

fof(f60,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) ),
    inference(definition_unfolding,[],[f48,f53,f53,f54,f54])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( X0 != X1
     => k5_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(ennf_transformation,[],[f18])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f47,f54,f54,f53])).

cnf(c_7,plain,
    ( X0 = X1
    | k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k3_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_3,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_48,plain,
    ( X0 != X1
    | k5_xboole_0(X2,k3_xboole_0(X2,X1)) = k1_xboole_0
    | k3_xboole_0(X0,X3) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_3])).

cnf(c_49,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X0)) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_48])).

cnf(c_216,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_49])).

cnf(c_1,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_218,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1,c_49])).

cnf(c_223,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_218,c_1])).

cnf(c_5,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_235,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_223,c_5])).

cnf(c_444,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_223,c_235])).

cnf(c_4,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_466,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_444,c_4])).

cnf(c_468,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_466,c_235])).

cnf(c_700,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X0) = k5_xboole_0(k3_xboole_0(X0,X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_49,c_468])).

cnf(c_715,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X0) = k3_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_700,c_4])).

cnf(c_1217,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X1) = k3_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_715])).

cnf(c_1818,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_216,c_1217])).

cnf(c_236,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_223,c_5])).

cnf(c_810,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_236,c_468])).

cnf(c_828,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
    inference(demodulation,[status(thm)],[c_810,c_4])).

cnf(c_1138,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X0))) = k5_xboole_0(X1,X2) ),
    inference(superposition,[status(thm)],[c_5,c_828])).

cnf(c_3081,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X2,k1_xboole_0)) = k5_xboole_0(X2,k3_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_1818,c_1138])).

cnf(c_3144,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X1,X2)) = k5_xboole_0(k3_xboole_0(X2,X1),X0) ),
    inference(demodulation,[status(thm)],[c_3081,c_4])).

cnf(c_1157,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_828,c_468])).

cnf(c_1163,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_5,c_1157])).

cnf(c_6,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_10,negated_conjecture,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_285,plain,
    ( k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_6,c_10])).

cnf(c_1434,plain,
    ( k5_xboole_0(k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_1157,c_285])).

cnf(c_3413,plain,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_1163,c_1434])).

cnf(c_11186,plain,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_3144,c_3413])).

cnf(c_11797,plain,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)
    | sK1 = sK0 ),
    inference(superposition,[status(thm)],[c_7,c_11186])).

cnf(c_9,plain,
    ( X0 = X1
    | k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_190,plain,
    ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1)
    | sK1 = X0 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_191,plain,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)
    | sK1 = sK0 ),
    inference(instantiation,[status(thm)],[c_190])).

cnf(c_12043,plain,
    ( sK1 = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_11797,c_191])).

cnf(c_481,plain,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
    inference(superposition,[status(thm)],[c_5,c_285])).

cnf(c_12048,plain,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(demodulation,[status(thm)],[c_12043,c_481])).

cnf(c_1145,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X1) = X0 ),
    inference(superposition,[status(thm)],[c_468,c_828])).

cnf(c_1839,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(X0,X1)) = k3_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_1818,c_1145])).

cnf(c_696,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,X2))) = X2 ),
    inference(superposition,[status(thm)],[c_5,c_468])).

cnf(c_2159,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k5_xboole_0(X0,k3_xboole_0(X1,X2))) = k3_xboole_0(X2,X1) ),
    inference(superposition,[status(thm)],[c_1839,c_696])).

cnf(c_2190,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X1,X2))) = k3_xboole_0(X2,X1) ),
    inference(light_normalisation,[status(thm)],[c_2159,c_4])).

cnf(c_12051,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(demodulation,[status(thm)],[c_12048,c_1,c_2190])).

cnf(c_12052,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_12051])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:47:44 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 7.26/1.53  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.26/1.53  
% 7.26/1.53  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.26/1.53  
% 7.26/1.53  ------  iProver source info
% 7.26/1.53  
% 7.26/1.53  git: date: 2020-06-30 10:37:57 +0100
% 7.26/1.53  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.26/1.53  git: non_committed_changes: false
% 7.26/1.53  git: last_make_outside_of_git: false
% 7.26/1.53  
% 7.26/1.53  ------ 
% 7.26/1.53  
% 7.26/1.53  ------ Input Options
% 7.26/1.53  
% 7.26/1.53  --out_options                           all
% 7.26/1.53  --tptp_safe_out                         true
% 7.26/1.53  --problem_path                          ""
% 7.26/1.53  --include_path                          ""
% 7.26/1.53  --clausifier                            res/vclausify_rel
% 7.26/1.53  --clausifier_options                    --mode clausify
% 7.26/1.53  --stdin                                 false
% 7.26/1.53  --stats_out                             all
% 7.26/1.53  
% 7.26/1.53  ------ General Options
% 7.26/1.53  
% 7.26/1.53  --fof                                   false
% 7.26/1.53  --time_out_real                         305.
% 7.26/1.53  --time_out_virtual                      -1.
% 7.26/1.53  --symbol_type_check                     false
% 7.26/1.53  --clausify_out                          false
% 7.26/1.53  --sig_cnt_out                           false
% 7.26/1.53  --trig_cnt_out                          false
% 7.26/1.53  --trig_cnt_out_tolerance                1.
% 7.26/1.53  --trig_cnt_out_sk_spl                   false
% 7.26/1.53  --abstr_cl_out                          false
% 7.26/1.53  
% 7.26/1.53  ------ Global Options
% 7.26/1.53  
% 7.26/1.53  --schedule                              default
% 7.26/1.53  --add_important_lit                     false
% 7.26/1.53  --prop_solver_per_cl                    1000
% 7.26/1.53  --min_unsat_core                        false
% 7.26/1.53  --soft_assumptions                      false
% 7.26/1.53  --soft_lemma_size                       3
% 7.26/1.53  --prop_impl_unit_size                   0
% 7.26/1.53  --prop_impl_unit                        []
% 7.26/1.53  --share_sel_clauses                     true
% 7.26/1.53  --reset_solvers                         false
% 7.26/1.53  --bc_imp_inh                            [conj_cone]
% 7.26/1.53  --conj_cone_tolerance                   3.
% 7.26/1.53  --extra_neg_conj                        none
% 7.26/1.53  --large_theory_mode                     true
% 7.26/1.53  --prolific_symb_bound                   200
% 7.26/1.53  --lt_threshold                          2000
% 7.26/1.53  --clause_weak_htbl                      true
% 7.26/1.53  --gc_record_bc_elim                     false
% 7.26/1.53  
% 7.26/1.53  ------ Preprocessing Options
% 7.26/1.53  
% 7.26/1.53  --preprocessing_flag                    true
% 7.26/1.53  --time_out_prep_mult                    0.1
% 7.26/1.53  --splitting_mode                        input
% 7.26/1.53  --splitting_grd                         true
% 7.26/1.53  --splitting_cvd                         false
% 7.26/1.53  --splitting_cvd_svl                     false
% 7.26/1.53  --splitting_nvd                         32
% 7.26/1.53  --sub_typing                            true
% 7.26/1.53  --prep_gs_sim                           true
% 7.26/1.53  --prep_unflatten                        true
% 7.26/1.53  --prep_res_sim                          true
% 7.26/1.53  --prep_upred                            true
% 7.26/1.53  --prep_sem_filter                       exhaustive
% 7.26/1.53  --prep_sem_filter_out                   false
% 7.26/1.53  --pred_elim                             true
% 7.26/1.53  --res_sim_input                         true
% 7.26/1.53  --eq_ax_congr_red                       true
% 7.26/1.53  --pure_diseq_elim                       true
% 7.26/1.53  --brand_transform                       false
% 7.26/1.53  --non_eq_to_eq                          false
% 7.26/1.53  --prep_def_merge                        true
% 7.26/1.53  --prep_def_merge_prop_impl              false
% 7.26/1.53  --prep_def_merge_mbd                    true
% 7.26/1.53  --prep_def_merge_tr_red                 false
% 7.26/1.53  --prep_def_merge_tr_cl                  false
% 7.26/1.53  --smt_preprocessing                     true
% 7.26/1.53  --smt_ac_axioms                         fast
% 7.26/1.53  --preprocessed_out                      false
% 7.26/1.53  --preprocessed_stats                    false
% 7.26/1.53  
% 7.26/1.53  ------ Abstraction refinement Options
% 7.26/1.53  
% 7.26/1.53  --abstr_ref                             []
% 7.26/1.53  --abstr_ref_prep                        false
% 7.26/1.53  --abstr_ref_until_sat                   false
% 7.26/1.53  --abstr_ref_sig_restrict                funpre
% 7.26/1.53  --abstr_ref_af_restrict_to_split_sk     false
% 7.26/1.53  --abstr_ref_under                       []
% 7.26/1.53  
% 7.26/1.53  ------ SAT Options
% 7.26/1.53  
% 7.26/1.53  --sat_mode                              false
% 7.26/1.53  --sat_fm_restart_options                ""
% 7.26/1.53  --sat_gr_def                            false
% 7.26/1.53  --sat_epr_types                         true
% 7.26/1.53  --sat_non_cyclic_types                  false
% 7.26/1.53  --sat_finite_models                     false
% 7.26/1.53  --sat_fm_lemmas                         false
% 7.26/1.53  --sat_fm_prep                           false
% 7.26/1.53  --sat_fm_uc_incr                        true
% 7.26/1.53  --sat_out_model                         small
% 7.26/1.53  --sat_out_clauses                       false
% 7.26/1.53  
% 7.26/1.53  ------ QBF Options
% 7.26/1.53  
% 7.26/1.53  --qbf_mode                              false
% 7.26/1.53  --qbf_elim_univ                         false
% 7.26/1.53  --qbf_dom_inst                          none
% 7.26/1.53  --qbf_dom_pre_inst                      false
% 7.26/1.53  --qbf_sk_in                             false
% 7.26/1.53  --qbf_pred_elim                         true
% 7.26/1.53  --qbf_split                             512
% 7.26/1.53  
% 7.26/1.53  ------ BMC1 Options
% 7.26/1.53  
% 7.26/1.53  --bmc1_incremental                      false
% 7.26/1.53  --bmc1_axioms                           reachable_all
% 7.26/1.53  --bmc1_min_bound                        0
% 7.26/1.53  --bmc1_max_bound                        -1
% 7.26/1.53  --bmc1_max_bound_default                -1
% 7.26/1.53  --bmc1_symbol_reachability              true
% 7.26/1.53  --bmc1_property_lemmas                  false
% 7.26/1.53  --bmc1_k_induction                      false
% 7.26/1.53  --bmc1_non_equiv_states                 false
% 7.26/1.53  --bmc1_deadlock                         false
% 7.26/1.53  --bmc1_ucm                              false
% 7.26/1.53  --bmc1_add_unsat_core                   none
% 7.26/1.53  --bmc1_unsat_core_children              false
% 7.26/1.53  --bmc1_unsat_core_extrapolate_axioms    false
% 7.26/1.53  --bmc1_out_stat                         full
% 7.26/1.53  --bmc1_ground_init                      false
% 7.26/1.53  --bmc1_pre_inst_next_state              false
% 7.26/1.53  --bmc1_pre_inst_state                   false
% 7.26/1.53  --bmc1_pre_inst_reach_state             false
% 7.26/1.53  --bmc1_out_unsat_core                   false
% 7.26/1.53  --bmc1_aig_witness_out                  false
% 7.26/1.53  --bmc1_verbose                          false
% 7.26/1.53  --bmc1_dump_clauses_tptp                false
% 7.26/1.53  --bmc1_dump_unsat_core_tptp             false
% 7.26/1.53  --bmc1_dump_file                        -
% 7.26/1.53  --bmc1_ucm_expand_uc_limit              128
% 7.26/1.53  --bmc1_ucm_n_expand_iterations          6
% 7.26/1.53  --bmc1_ucm_extend_mode                  1
% 7.26/1.53  --bmc1_ucm_init_mode                    2
% 7.26/1.53  --bmc1_ucm_cone_mode                    none
% 7.26/1.53  --bmc1_ucm_reduced_relation_type        0
% 7.26/1.53  --bmc1_ucm_relax_model                  4
% 7.26/1.53  --bmc1_ucm_full_tr_after_sat            true
% 7.26/1.53  --bmc1_ucm_expand_neg_assumptions       false
% 7.26/1.53  --bmc1_ucm_layered_model                none
% 7.26/1.53  --bmc1_ucm_max_lemma_size               10
% 7.26/1.53  
% 7.26/1.53  ------ AIG Options
% 7.26/1.53  
% 7.26/1.53  --aig_mode                              false
% 7.26/1.53  
% 7.26/1.53  ------ Instantiation Options
% 7.26/1.53  
% 7.26/1.53  --instantiation_flag                    true
% 7.26/1.53  --inst_sos_flag                         false
% 7.26/1.53  --inst_sos_phase                        true
% 7.26/1.53  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.26/1.53  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.26/1.53  --inst_lit_sel_side                     num_symb
% 7.26/1.53  --inst_solver_per_active                1400
% 7.26/1.53  --inst_solver_calls_frac                1.
% 7.26/1.53  --inst_passive_queue_type               priority_queues
% 7.26/1.53  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.26/1.53  --inst_passive_queues_freq              [25;2]
% 7.26/1.53  --inst_dismatching                      true
% 7.26/1.53  --inst_eager_unprocessed_to_passive     true
% 7.26/1.53  --inst_prop_sim_given                   true
% 7.26/1.53  --inst_prop_sim_new                     false
% 7.26/1.53  --inst_subs_new                         false
% 7.26/1.53  --inst_eq_res_simp                      false
% 7.26/1.53  --inst_subs_given                       false
% 7.26/1.53  --inst_orphan_elimination               true
% 7.26/1.53  --inst_learning_loop_flag               true
% 7.26/1.53  --inst_learning_start                   3000
% 7.26/1.53  --inst_learning_factor                  2
% 7.26/1.53  --inst_start_prop_sim_after_learn       3
% 7.26/1.53  --inst_sel_renew                        solver
% 7.26/1.53  --inst_lit_activity_flag                true
% 7.26/1.53  --inst_restr_to_given                   false
% 7.26/1.53  --inst_activity_threshold               500
% 7.26/1.53  --inst_out_proof                        true
% 7.26/1.53  
% 7.26/1.53  ------ Resolution Options
% 7.26/1.53  
% 7.26/1.53  --resolution_flag                       true
% 7.26/1.53  --res_lit_sel                           adaptive
% 7.26/1.53  --res_lit_sel_side                      none
% 7.26/1.53  --res_ordering                          kbo
% 7.26/1.53  --res_to_prop_solver                    active
% 7.26/1.53  --res_prop_simpl_new                    false
% 7.26/1.53  --res_prop_simpl_given                  true
% 7.26/1.53  --res_passive_queue_type                priority_queues
% 7.26/1.53  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.26/1.53  --res_passive_queues_freq               [15;5]
% 7.26/1.53  --res_forward_subs                      full
% 7.26/1.53  --res_backward_subs                     full
% 7.26/1.53  --res_forward_subs_resolution           true
% 7.26/1.53  --res_backward_subs_resolution          true
% 7.26/1.53  --res_orphan_elimination                true
% 7.26/1.53  --res_time_limit                        2.
% 7.26/1.53  --res_out_proof                         true
% 7.26/1.53  
% 7.26/1.53  ------ Superposition Options
% 7.26/1.53  
% 7.26/1.53  --superposition_flag                    true
% 7.26/1.53  --sup_passive_queue_type                priority_queues
% 7.26/1.53  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.26/1.53  --sup_passive_queues_freq               [8;1;4]
% 7.26/1.53  --demod_completeness_check              fast
% 7.26/1.53  --demod_use_ground                      true
% 7.26/1.53  --sup_to_prop_solver                    passive
% 7.26/1.53  --sup_prop_simpl_new                    true
% 7.26/1.53  --sup_prop_simpl_given                  true
% 7.26/1.53  --sup_fun_splitting                     false
% 7.26/1.53  --sup_smt_interval                      50000
% 7.26/1.53  
% 7.26/1.53  ------ Superposition Simplification Setup
% 7.26/1.53  
% 7.26/1.53  --sup_indices_passive                   []
% 7.26/1.53  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.26/1.53  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.26/1.53  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.26/1.53  --sup_full_triv                         [TrivRules;PropSubs]
% 7.26/1.53  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.26/1.53  --sup_full_bw                           [BwDemod]
% 7.26/1.53  --sup_immed_triv                        [TrivRules]
% 7.26/1.53  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.26/1.53  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.26/1.53  --sup_immed_bw_main                     []
% 7.26/1.53  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.26/1.53  --sup_input_triv                        [Unflattening;TrivRules]
% 7.26/1.53  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.26/1.53  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.26/1.53  
% 7.26/1.53  ------ Combination Options
% 7.26/1.53  
% 7.26/1.53  --comb_res_mult                         3
% 7.26/1.53  --comb_sup_mult                         2
% 7.26/1.53  --comb_inst_mult                        10
% 7.26/1.53  
% 7.26/1.53  ------ Debug Options
% 7.26/1.53  
% 7.26/1.53  --dbg_backtrace                         false
% 7.26/1.53  --dbg_dump_prop_clauses                 false
% 7.26/1.53  --dbg_dump_prop_clauses_file            -
% 7.26/1.53  --dbg_out_stat                          false
% 7.26/1.53  ------ Parsing...
% 7.26/1.53  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.26/1.53  
% 7.26/1.53  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.26/1.53  
% 7.26/1.53  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.26/1.53  
% 7.26/1.53  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.26/1.53  ------ Proving...
% 7.26/1.53  ------ Problem Properties 
% 7.26/1.53  
% 7.26/1.53  
% 7.26/1.53  clauses                                 10
% 7.26/1.53  conjectures                             1
% 7.26/1.53  EPR                                     0
% 7.26/1.53  Horn                                    8
% 7.26/1.53  unary                                   8
% 7.26/1.53  binary                                  2
% 7.26/1.53  lits                                    12
% 7.26/1.53  lits eq                                 12
% 7.26/1.53  fd_pure                                 0
% 7.26/1.53  fd_pseudo                               0
% 7.26/1.53  fd_cond                                 0
% 7.26/1.53  fd_pseudo_cond                          2
% 7.26/1.53  AC symbols                              0
% 7.26/1.53  
% 7.26/1.53  ------ Schedule dynamic 5 is on 
% 7.26/1.53  
% 7.26/1.53  ------ pure equality problem: resolution off 
% 7.26/1.53  
% 7.26/1.53  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.26/1.53  
% 7.26/1.53  
% 7.26/1.53  ------ 
% 7.26/1.53  Current options:
% 7.26/1.53  ------ 
% 7.26/1.53  
% 7.26/1.53  ------ Input Options
% 7.26/1.53  
% 7.26/1.53  --out_options                           all
% 7.26/1.53  --tptp_safe_out                         true
% 7.26/1.53  --problem_path                          ""
% 7.26/1.53  --include_path                          ""
% 7.26/1.53  --clausifier                            res/vclausify_rel
% 7.26/1.53  --clausifier_options                    --mode clausify
% 7.26/1.53  --stdin                                 false
% 7.26/1.53  --stats_out                             all
% 7.26/1.53  
% 7.26/1.53  ------ General Options
% 7.26/1.53  
% 7.26/1.53  --fof                                   false
% 7.26/1.53  --time_out_real                         305.
% 7.26/1.53  --time_out_virtual                      -1.
% 7.26/1.53  --symbol_type_check                     false
% 7.26/1.53  --clausify_out                          false
% 7.26/1.53  --sig_cnt_out                           false
% 7.26/1.53  --trig_cnt_out                          false
% 7.26/1.53  --trig_cnt_out_tolerance                1.
% 7.26/1.53  --trig_cnt_out_sk_spl                   false
% 7.26/1.53  --abstr_cl_out                          false
% 7.26/1.53  
% 7.26/1.53  ------ Global Options
% 7.26/1.53  
% 7.26/1.53  --schedule                              default
% 7.26/1.53  --add_important_lit                     false
% 7.26/1.53  --prop_solver_per_cl                    1000
% 7.26/1.53  --min_unsat_core                        false
% 7.26/1.53  --soft_assumptions                      false
% 7.26/1.53  --soft_lemma_size                       3
% 7.26/1.53  --prop_impl_unit_size                   0
% 7.26/1.53  --prop_impl_unit                        []
% 7.26/1.53  --share_sel_clauses                     true
% 7.26/1.53  --reset_solvers                         false
% 7.26/1.53  --bc_imp_inh                            [conj_cone]
% 7.26/1.53  --conj_cone_tolerance                   3.
% 7.26/1.53  --extra_neg_conj                        none
% 7.26/1.53  --large_theory_mode                     true
% 7.26/1.53  --prolific_symb_bound                   200
% 7.26/1.53  --lt_threshold                          2000
% 7.26/1.53  --clause_weak_htbl                      true
% 7.26/1.53  --gc_record_bc_elim                     false
% 7.26/1.53  
% 7.26/1.53  ------ Preprocessing Options
% 7.26/1.53  
% 7.26/1.53  --preprocessing_flag                    true
% 7.26/1.53  --time_out_prep_mult                    0.1
% 7.26/1.53  --splitting_mode                        input
% 7.26/1.53  --splitting_grd                         true
% 7.26/1.53  --splitting_cvd                         false
% 7.26/1.53  --splitting_cvd_svl                     false
% 7.26/1.53  --splitting_nvd                         32
% 7.26/1.53  --sub_typing                            true
% 7.26/1.53  --prep_gs_sim                           true
% 7.26/1.53  --prep_unflatten                        true
% 7.26/1.53  --prep_res_sim                          true
% 7.26/1.53  --prep_upred                            true
% 7.26/1.53  --prep_sem_filter                       exhaustive
% 7.26/1.53  --prep_sem_filter_out                   false
% 7.26/1.53  --pred_elim                             true
% 7.26/1.53  --res_sim_input                         true
% 7.26/1.53  --eq_ax_congr_red                       true
% 7.26/1.53  --pure_diseq_elim                       true
% 7.26/1.53  --brand_transform                       false
% 7.26/1.53  --non_eq_to_eq                          false
% 7.26/1.53  --prep_def_merge                        true
% 7.26/1.53  --prep_def_merge_prop_impl              false
% 7.26/1.53  --prep_def_merge_mbd                    true
% 7.26/1.53  --prep_def_merge_tr_red                 false
% 7.26/1.53  --prep_def_merge_tr_cl                  false
% 7.26/1.53  --smt_preprocessing                     true
% 7.26/1.53  --smt_ac_axioms                         fast
% 7.26/1.53  --preprocessed_out                      false
% 7.26/1.53  --preprocessed_stats                    false
% 7.26/1.53  
% 7.26/1.53  ------ Abstraction refinement Options
% 7.26/1.53  
% 7.26/1.53  --abstr_ref                             []
% 7.26/1.53  --abstr_ref_prep                        false
% 7.26/1.53  --abstr_ref_until_sat                   false
% 7.26/1.53  --abstr_ref_sig_restrict                funpre
% 7.26/1.53  --abstr_ref_af_restrict_to_split_sk     false
% 7.26/1.53  --abstr_ref_under                       []
% 7.26/1.53  
% 7.26/1.53  ------ SAT Options
% 7.26/1.53  
% 7.26/1.53  --sat_mode                              false
% 7.26/1.53  --sat_fm_restart_options                ""
% 7.26/1.53  --sat_gr_def                            false
% 7.26/1.53  --sat_epr_types                         true
% 7.26/1.53  --sat_non_cyclic_types                  false
% 7.26/1.53  --sat_finite_models                     false
% 7.26/1.53  --sat_fm_lemmas                         false
% 7.26/1.53  --sat_fm_prep                           false
% 7.26/1.53  --sat_fm_uc_incr                        true
% 7.26/1.53  --sat_out_model                         small
% 7.26/1.53  --sat_out_clauses                       false
% 7.26/1.53  
% 7.26/1.53  ------ QBF Options
% 7.26/1.53  
% 7.26/1.53  --qbf_mode                              false
% 7.26/1.53  --qbf_elim_univ                         false
% 7.26/1.53  --qbf_dom_inst                          none
% 7.26/1.53  --qbf_dom_pre_inst                      false
% 7.26/1.53  --qbf_sk_in                             false
% 7.26/1.53  --qbf_pred_elim                         true
% 7.26/1.53  --qbf_split                             512
% 7.26/1.53  
% 7.26/1.53  ------ BMC1 Options
% 7.26/1.53  
% 7.26/1.53  --bmc1_incremental                      false
% 7.26/1.53  --bmc1_axioms                           reachable_all
% 7.26/1.53  --bmc1_min_bound                        0
% 7.26/1.53  --bmc1_max_bound                        -1
% 7.26/1.53  --bmc1_max_bound_default                -1
% 7.26/1.53  --bmc1_symbol_reachability              true
% 7.26/1.53  --bmc1_property_lemmas                  false
% 7.26/1.53  --bmc1_k_induction                      false
% 7.26/1.53  --bmc1_non_equiv_states                 false
% 7.26/1.53  --bmc1_deadlock                         false
% 7.26/1.53  --bmc1_ucm                              false
% 7.26/1.53  --bmc1_add_unsat_core                   none
% 7.26/1.53  --bmc1_unsat_core_children              false
% 7.26/1.53  --bmc1_unsat_core_extrapolate_axioms    false
% 7.26/1.53  --bmc1_out_stat                         full
% 7.26/1.53  --bmc1_ground_init                      false
% 7.26/1.53  --bmc1_pre_inst_next_state              false
% 7.26/1.53  --bmc1_pre_inst_state                   false
% 7.26/1.53  --bmc1_pre_inst_reach_state             false
% 7.26/1.53  --bmc1_out_unsat_core                   false
% 7.26/1.53  --bmc1_aig_witness_out                  false
% 7.26/1.53  --bmc1_verbose                          false
% 7.26/1.53  --bmc1_dump_clauses_tptp                false
% 7.26/1.53  --bmc1_dump_unsat_core_tptp             false
% 7.26/1.53  --bmc1_dump_file                        -
% 7.26/1.53  --bmc1_ucm_expand_uc_limit              128
% 7.26/1.53  --bmc1_ucm_n_expand_iterations          6
% 7.26/1.53  --bmc1_ucm_extend_mode                  1
% 7.26/1.53  --bmc1_ucm_init_mode                    2
% 7.26/1.53  --bmc1_ucm_cone_mode                    none
% 7.26/1.53  --bmc1_ucm_reduced_relation_type        0
% 7.26/1.53  --bmc1_ucm_relax_model                  4
% 7.26/1.53  --bmc1_ucm_full_tr_after_sat            true
% 7.26/1.53  --bmc1_ucm_expand_neg_assumptions       false
% 7.26/1.53  --bmc1_ucm_layered_model                none
% 7.26/1.53  --bmc1_ucm_max_lemma_size               10
% 7.26/1.53  
% 7.26/1.53  ------ AIG Options
% 7.26/1.53  
% 7.26/1.53  --aig_mode                              false
% 7.26/1.53  
% 7.26/1.53  ------ Instantiation Options
% 7.26/1.53  
% 7.26/1.53  --instantiation_flag                    true
% 7.26/1.53  --inst_sos_flag                         false
% 7.26/1.53  --inst_sos_phase                        true
% 7.26/1.53  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.26/1.53  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.26/1.53  --inst_lit_sel_side                     none
% 7.26/1.53  --inst_solver_per_active                1400
% 7.26/1.53  --inst_solver_calls_frac                1.
% 7.26/1.53  --inst_passive_queue_type               priority_queues
% 7.26/1.53  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.26/1.53  --inst_passive_queues_freq              [25;2]
% 7.26/1.53  --inst_dismatching                      true
% 7.26/1.53  --inst_eager_unprocessed_to_passive     true
% 7.26/1.53  --inst_prop_sim_given                   true
% 7.26/1.53  --inst_prop_sim_new                     false
% 7.26/1.53  --inst_subs_new                         false
% 7.26/1.53  --inst_eq_res_simp                      false
% 7.26/1.53  --inst_subs_given                       false
% 7.26/1.53  --inst_orphan_elimination               true
% 7.26/1.53  --inst_learning_loop_flag               true
% 7.26/1.53  --inst_learning_start                   3000
% 7.26/1.53  --inst_learning_factor                  2
% 7.26/1.53  --inst_start_prop_sim_after_learn       3
% 7.26/1.53  --inst_sel_renew                        solver
% 7.26/1.53  --inst_lit_activity_flag                true
% 7.26/1.53  --inst_restr_to_given                   false
% 7.26/1.53  --inst_activity_threshold               500
% 7.26/1.53  --inst_out_proof                        true
% 7.26/1.53  
% 7.26/1.53  ------ Resolution Options
% 7.26/1.53  
% 7.26/1.53  --resolution_flag                       false
% 7.26/1.53  --res_lit_sel                           adaptive
% 7.26/1.53  --res_lit_sel_side                      none
% 7.26/1.53  --res_ordering                          kbo
% 7.26/1.53  --res_to_prop_solver                    active
% 7.26/1.53  --res_prop_simpl_new                    false
% 7.26/1.53  --res_prop_simpl_given                  true
% 7.26/1.53  --res_passive_queue_type                priority_queues
% 7.26/1.53  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.26/1.53  --res_passive_queues_freq               [15;5]
% 7.26/1.53  --res_forward_subs                      full
% 7.26/1.53  --res_backward_subs                     full
% 7.26/1.53  --res_forward_subs_resolution           true
% 7.26/1.53  --res_backward_subs_resolution          true
% 7.26/1.53  --res_orphan_elimination                true
% 7.26/1.53  --res_time_limit                        2.
% 7.26/1.53  --res_out_proof                         true
% 7.26/1.53  
% 7.26/1.53  ------ Superposition Options
% 7.26/1.53  
% 7.26/1.53  --superposition_flag                    true
% 7.26/1.53  --sup_passive_queue_type                priority_queues
% 7.26/1.53  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.26/1.53  --sup_passive_queues_freq               [8;1;4]
% 7.26/1.53  --demod_completeness_check              fast
% 7.26/1.53  --demod_use_ground                      true
% 7.26/1.53  --sup_to_prop_solver                    passive
% 7.26/1.53  --sup_prop_simpl_new                    true
% 7.26/1.53  --sup_prop_simpl_given                  true
% 7.26/1.53  --sup_fun_splitting                     false
% 7.26/1.53  --sup_smt_interval                      50000
% 7.26/1.53  
% 7.26/1.53  ------ Superposition Simplification Setup
% 7.26/1.53  
% 7.26/1.53  --sup_indices_passive                   []
% 7.26/1.53  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.26/1.53  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.26/1.53  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.26/1.53  --sup_full_triv                         [TrivRules;PropSubs]
% 7.26/1.53  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.26/1.53  --sup_full_bw                           [BwDemod]
% 7.26/1.53  --sup_immed_triv                        [TrivRules]
% 7.26/1.53  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.26/1.53  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.26/1.53  --sup_immed_bw_main                     []
% 7.26/1.53  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.26/1.53  --sup_input_triv                        [Unflattening;TrivRules]
% 7.26/1.53  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.26/1.53  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.26/1.53  
% 7.26/1.53  ------ Combination Options
% 7.26/1.53  
% 7.26/1.53  --comb_res_mult                         3
% 7.26/1.53  --comb_sup_mult                         2
% 7.26/1.53  --comb_inst_mult                        10
% 7.26/1.53  
% 7.26/1.53  ------ Debug Options
% 7.26/1.53  
% 7.26/1.53  --dbg_backtrace                         false
% 7.26/1.53  --dbg_dump_prop_clauses                 false
% 7.26/1.53  --dbg_dump_prop_clauses_file            -
% 7.26/1.53  --dbg_out_stat                          false
% 7.26/1.53  
% 7.26/1.53  
% 7.26/1.53  
% 7.26/1.53  
% 7.26/1.53  ------ Proving...
% 7.26/1.53  
% 7.26/1.53  
% 7.26/1.53  % SZS status Theorem for theBenchmark.p
% 7.26/1.53  
% 7.26/1.53   Resolution empty clause
% 7.26/1.53  
% 7.26/1.53  % SZS output start CNFRefutation for theBenchmark.p
% 7.26/1.53  
% 7.26/1.53  fof(f17,axiom,(
% 7.26/1.53    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) <=> X0 != X1)),
% 7.26/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.26/1.53  
% 7.26/1.53  fof(f26,plain,(
% 7.26/1.53    ! [X0,X1] : ((k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) | X0 = X1) & (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)))),
% 7.26/1.53    inference(nnf_transformation,[],[f17])).
% 7.26/1.53  
% 7.26/1.53  fof(f46,plain,(
% 7.26/1.53    ( ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) | X0 = X1) )),
% 7.26/1.53    inference(cnf_transformation,[],[f26])).
% 7.26/1.53  
% 7.26/1.53  fof(f4,axiom,(
% 7.26/1.53    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 7.26/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.26/1.53  
% 7.26/1.53  fof(f32,plain,(
% 7.26/1.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 7.26/1.53    inference(cnf_transformation,[],[f4])).
% 7.26/1.53  
% 7.26/1.53  fof(f9,axiom,(
% 7.26/1.53    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 7.26/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.26/1.53  
% 7.26/1.53  fof(f37,plain,(
% 7.26/1.53    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 7.26/1.53    inference(cnf_transformation,[],[f9])).
% 7.26/1.53  
% 7.26/1.53  fof(f10,axiom,(
% 7.26/1.53    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 7.26/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.26/1.53  
% 7.26/1.53  fof(f38,plain,(
% 7.26/1.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 7.26/1.53    inference(cnf_transformation,[],[f10])).
% 7.26/1.53  
% 7.26/1.53  fof(f11,axiom,(
% 7.26/1.53    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 7.26/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.26/1.53  
% 7.26/1.53  fof(f39,plain,(
% 7.26/1.53    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 7.26/1.53    inference(cnf_transformation,[],[f11])).
% 7.26/1.53  
% 7.26/1.53  fof(f12,axiom,(
% 7.26/1.53    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 7.26/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.26/1.53  
% 7.26/1.53  fof(f40,plain,(
% 7.26/1.53    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 7.26/1.53    inference(cnf_transformation,[],[f12])).
% 7.26/1.53  
% 7.26/1.53  fof(f13,axiom,(
% 7.26/1.53    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 7.26/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.26/1.53  
% 7.26/1.53  fof(f41,plain,(
% 7.26/1.53    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 7.26/1.53    inference(cnf_transformation,[],[f13])).
% 7.26/1.53  
% 7.26/1.53  fof(f14,axiom,(
% 7.26/1.53    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 7.26/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.26/1.53  
% 7.26/1.53  fof(f42,plain,(
% 7.26/1.53    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 7.26/1.53    inference(cnf_transformation,[],[f14])).
% 7.26/1.53  
% 7.26/1.53  fof(f15,axiom,(
% 7.26/1.53    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 7.26/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.26/1.53  
% 7.26/1.53  fof(f43,plain,(
% 7.26/1.53    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 7.26/1.53    inference(cnf_transformation,[],[f15])).
% 7.26/1.53  
% 7.26/1.53  fof(f49,plain,(
% 7.26/1.53    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 7.26/1.53    inference(definition_unfolding,[],[f42,f43])).
% 7.26/1.53  
% 7.26/1.53  fof(f50,plain,(
% 7.26/1.53    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 7.26/1.53    inference(definition_unfolding,[],[f41,f49])).
% 7.26/1.53  
% 7.26/1.53  fof(f51,plain,(
% 7.26/1.53    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 7.26/1.53    inference(definition_unfolding,[],[f40,f50])).
% 7.26/1.53  
% 7.26/1.53  fof(f52,plain,(
% 7.26/1.53    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 7.26/1.53    inference(definition_unfolding,[],[f39,f51])).
% 7.26/1.53  
% 7.26/1.53  fof(f53,plain,(
% 7.26/1.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 7.26/1.53    inference(definition_unfolding,[],[f38,f52])).
% 7.26/1.53  
% 7.26/1.53  fof(f54,plain,(
% 7.26/1.53    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 7.26/1.53    inference(definition_unfolding,[],[f37,f53])).
% 7.26/1.53  
% 7.26/1.53  fof(f57,plain,(
% 7.26/1.53    ( ! [X0,X1] : (k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) | X0 = X1) )),
% 7.26/1.53    inference(definition_unfolding,[],[f46,f32,f54,f54,f54])).
% 7.26/1.53  
% 7.26/1.53  fof(f1,axiom,(
% 7.26/1.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 7.26/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.26/1.53  
% 7.26/1.53  fof(f29,plain,(
% 7.26/1.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 7.26/1.53    inference(cnf_transformation,[],[f1])).
% 7.26/1.53  
% 7.26/1.53  fof(f3,axiom,(
% 7.26/1.53    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 7.26/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.26/1.53  
% 7.26/1.53  fof(f22,plain,(
% 7.26/1.53    ! [X0,X1] : (r1_tarski(X0,X1) => k4_xboole_0(X0,X1) = k1_xboole_0)),
% 7.26/1.53    inference(unused_predicate_definition_removal,[],[f3])).
% 7.26/1.53  
% 7.26/1.53  fof(f23,plain,(
% 7.26/1.53    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1))),
% 7.26/1.53    inference(ennf_transformation,[],[f22])).
% 7.26/1.53  
% 7.26/1.53  fof(f31,plain,(
% 7.26/1.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 7.26/1.53    inference(cnf_transformation,[],[f23])).
% 7.26/1.53  
% 7.26/1.53  fof(f55,plain,(
% 7.26/1.53    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) | ~r1_tarski(X0,X1)) )),
% 7.26/1.53    inference(definition_unfolding,[],[f31,f32])).
% 7.26/1.53  
% 7.26/1.53  fof(f5,axiom,(
% 7.26/1.53    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 7.26/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.26/1.53  
% 7.26/1.53  fof(f33,plain,(
% 7.26/1.53    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 7.26/1.53    inference(cnf_transformation,[],[f5])).
% 7.26/1.53  
% 7.26/1.53  fof(f2,axiom,(
% 7.26/1.53    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 7.26/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.26/1.53  
% 7.26/1.53  fof(f21,plain,(
% 7.26/1.53    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 7.26/1.53    inference(rectify,[],[f2])).
% 7.26/1.53  
% 7.26/1.53  fof(f30,plain,(
% 7.26/1.53    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 7.26/1.53    inference(cnf_transformation,[],[f21])).
% 7.26/1.53  
% 7.26/1.53  fof(f7,axiom,(
% 7.26/1.53    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 7.26/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.26/1.53  
% 7.26/1.53  fof(f35,plain,(
% 7.26/1.53    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 7.26/1.53    inference(cnf_transformation,[],[f7])).
% 7.26/1.53  
% 7.26/1.53  fof(f6,axiom,(
% 7.26/1.53    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 7.26/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.26/1.53  
% 7.26/1.53  fof(f34,plain,(
% 7.26/1.53    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 7.26/1.53    inference(cnf_transformation,[],[f6])).
% 7.26/1.53  
% 7.26/1.53  fof(f16,axiom,(
% 7.26/1.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 7.26/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.26/1.53  
% 7.26/1.53  fof(f44,plain,(
% 7.26/1.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 7.26/1.53    inference(cnf_transformation,[],[f16])).
% 7.26/1.53  
% 7.26/1.53  fof(f8,axiom,(
% 7.26/1.53    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1)),
% 7.26/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.26/1.53  
% 7.26/1.53  fof(f36,plain,(
% 7.26/1.53    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 7.26/1.53    inference(cnf_transformation,[],[f8])).
% 7.26/1.53  
% 7.26/1.53  fof(f56,plain,(
% 7.26/1.53    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 7.26/1.53    inference(definition_unfolding,[],[f44,f36,f53])).
% 7.26/1.53  
% 7.26/1.53  fof(f19,conjecture,(
% 7.26/1.53    ! [X0,X1] : k2_tarski(X0,X1) = k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 7.26/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.26/1.53  
% 7.26/1.53  fof(f20,negated_conjecture,(
% 7.26/1.53    ~! [X0,X1] : k2_tarski(X0,X1) = k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 7.26/1.53    inference(negated_conjecture,[],[f19])).
% 7.26/1.53  
% 7.26/1.53  fof(f25,plain,(
% 7.26/1.53    ? [X0,X1] : k2_tarski(X0,X1) != k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 7.26/1.53    inference(ennf_transformation,[],[f20])).
% 7.26/1.53  
% 7.26/1.53  fof(f27,plain,(
% 7.26/1.53    ? [X0,X1] : k2_tarski(X0,X1) != k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1))) => k2_tarski(sK0,sK1) != k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK1)))),
% 7.26/1.53    introduced(choice_axiom,[])).
% 7.26/1.53  
% 7.26/1.53  fof(f28,plain,(
% 7.26/1.53    k2_tarski(sK0,sK1) != k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK1)))),
% 7.26/1.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f27])).
% 7.26/1.53  
% 7.26/1.53  fof(f48,plain,(
% 7.26/1.53    k2_tarski(sK0,sK1) != k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK1)))),
% 7.26/1.53    inference(cnf_transformation,[],[f28])).
% 7.26/1.53  
% 7.26/1.53  fof(f60,plain,(
% 7.26/1.53    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))),
% 7.26/1.53    inference(definition_unfolding,[],[f48,f53,f53,f54,f54])).
% 7.26/1.53  
% 7.26/1.53  fof(f18,axiom,(
% 7.26/1.53    ! [X0,X1] : (X0 != X1 => k5_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1))),
% 7.26/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.26/1.53  
% 7.26/1.53  fof(f24,plain,(
% 7.26/1.53    ! [X0,X1] : (k5_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) | X0 = X1)),
% 7.26/1.53    inference(ennf_transformation,[],[f18])).
% 7.26/1.53  
% 7.26/1.53  fof(f47,plain,(
% 7.26/1.53    ( ! [X0,X1] : (k5_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) | X0 = X1) )),
% 7.26/1.53    inference(cnf_transformation,[],[f24])).
% 7.26/1.53  
% 7.26/1.53  fof(f59,plain,(
% 7.26/1.53    ( ! [X0,X1] : (k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) | X0 = X1) )),
% 7.26/1.53    inference(definition_unfolding,[],[f47,f54,f54,f53])).
% 7.26/1.53  
% 7.26/1.53  cnf(c_7,plain,
% 7.26/1.53      ( X0 = X1
% 7.26/1.53      | k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k3_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
% 7.26/1.53      inference(cnf_transformation,[],[f57]) ).
% 7.26/1.53  
% 7.26/1.53  cnf(c_0,plain,
% 7.26/1.53      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 7.26/1.53      inference(cnf_transformation,[],[f29]) ).
% 7.26/1.53  
% 7.26/1.53  cnf(c_2,plain,
% 7.26/1.53      ( ~ r1_tarski(X0,X1) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0 ),
% 7.26/1.53      inference(cnf_transformation,[],[f55]) ).
% 7.26/1.53  
% 7.26/1.53  cnf(c_3,plain,
% 7.26/1.53      ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
% 7.26/1.53      inference(cnf_transformation,[],[f33]) ).
% 7.26/1.53  
% 7.26/1.53  cnf(c_48,plain,
% 7.26/1.53      ( X0 != X1
% 7.26/1.53      | k5_xboole_0(X2,k3_xboole_0(X2,X1)) = k1_xboole_0
% 7.26/1.53      | k3_xboole_0(X0,X3) != X2 ),
% 7.26/1.53      inference(resolution_lifted,[status(thm)],[c_2,c_3]) ).
% 7.26/1.53  
% 7.26/1.53  cnf(c_49,plain,
% 7.26/1.53      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X0)) = k1_xboole_0 ),
% 7.26/1.53      inference(unflattening,[status(thm)],[c_48]) ).
% 7.26/1.53  
% 7.26/1.53  cnf(c_216,plain,
% 7.26/1.53      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X1)) = k1_xboole_0 ),
% 7.26/1.53      inference(superposition,[status(thm)],[c_0,c_49]) ).
% 7.26/1.53  
% 7.26/1.53  cnf(c_1,plain,
% 7.26/1.53      ( k3_xboole_0(X0,X0) = X0 ),
% 7.26/1.53      inference(cnf_transformation,[],[f30]) ).
% 7.26/1.53  
% 7.26/1.53  cnf(c_218,plain,
% 7.26/1.53      ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k1_xboole_0 ),
% 7.26/1.53      inference(superposition,[status(thm)],[c_1,c_49]) ).
% 7.26/1.53  
% 7.26/1.53  cnf(c_223,plain,
% 7.26/1.53      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 7.26/1.53      inference(light_normalisation,[status(thm)],[c_218,c_1]) ).
% 7.26/1.53  
% 7.26/1.53  cnf(c_5,plain,
% 7.26/1.53      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 7.26/1.53      inference(cnf_transformation,[],[f35]) ).
% 7.26/1.53  
% 7.26/1.53  cnf(c_235,plain,
% 7.26/1.53      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
% 7.26/1.53      inference(superposition,[status(thm)],[c_223,c_5]) ).
% 7.26/1.53  
% 7.26/1.53  cnf(c_444,plain,
% 7.26/1.53      ( k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(X0,k1_xboole_0) ),
% 7.26/1.53      inference(superposition,[status(thm)],[c_223,c_235]) ).
% 7.26/1.53  
% 7.26/1.53  cnf(c_4,plain,
% 7.26/1.53      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.26/1.53      inference(cnf_transformation,[],[f34]) ).
% 7.26/1.53  
% 7.26/1.53  cnf(c_466,plain,
% 7.26/1.53      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 7.26/1.53      inference(light_normalisation,[status(thm)],[c_444,c_4]) ).
% 7.26/1.53  
% 7.26/1.53  cnf(c_468,plain,
% 7.26/1.53      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
% 7.26/1.53      inference(demodulation,[status(thm)],[c_466,c_235]) ).
% 7.26/1.53  
% 7.26/1.53  cnf(c_700,plain,
% 7.26/1.53      ( k3_xboole_0(k3_xboole_0(X0,X1),X0) = k5_xboole_0(k3_xboole_0(X0,X1),k1_xboole_0) ),
% 7.26/1.53      inference(superposition,[status(thm)],[c_49,c_468]) ).
% 7.26/1.53  
% 7.26/1.53  cnf(c_715,plain,
% 7.26/1.53      ( k3_xboole_0(k3_xboole_0(X0,X1),X0) = k3_xboole_0(X0,X1) ),
% 7.26/1.53      inference(demodulation,[status(thm)],[c_700,c_4]) ).
% 7.26/1.53  
% 7.26/1.53  cnf(c_1217,plain,
% 7.26/1.53      ( k3_xboole_0(k3_xboole_0(X0,X1),X1) = k3_xboole_0(X1,X0) ),
% 7.26/1.53      inference(superposition,[status(thm)],[c_0,c_715]) ).
% 7.26/1.53  
% 7.26/1.53  cnf(c_1818,plain,
% 7.26/1.53      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X0)) = k1_xboole_0 ),
% 7.26/1.53      inference(light_normalisation,[status(thm)],[c_216,c_1217]) ).
% 7.26/1.53  
% 7.26/1.53  cnf(c_236,plain,
% 7.26/1.53      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) = k1_xboole_0 ),
% 7.26/1.53      inference(superposition,[status(thm)],[c_223,c_5]) ).
% 7.26/1.53  
% 7.26/1.53  cnf(c_810,plain,
% 7.26/1.53      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(X1,k1_xboole_0) ),
% 7.26/1.53      inference(superposition,[status(thm)],[c_236,c_468]) ).
% 7.26/1.53  
% 7.26/1.53  cnf(c_828,plain,
% 7.26/1.53      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
% 7.26/1.53      inference(demodulation,[status(thm)],[c_810,c_4]) ).
% 7.26/1.53  
% 7.26/1.53  cnf(c_1138,plain,
% 7.26/1.53      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X0))) = k5_xboole_0(X1,X2) ),
% 7.26/1.53      inference(superposition,[status(thm)],[c_5,c_828]) ).
% 7.26/1.53  
% 7.26/1.53  cnf(c_3081,plain,
% 7.26/1.53      ( k5_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X2,k1_xboole_0)) = k5_xboole_0(X2,k3_xboole_0(X1,X0)) ),
% 7.26/1.53      inference(superposition,[status(thm)],[c_1818,c_1138]) ).
% 7.26/1.53  
% 7.26/1.53  cnf(c_3144,plain,
% 7.26/1.53      ( k5_xboole_0(X0,k3_xboole_0(X1,X2)) = k5_xboole_0(k3_xboole_0(X2,X1),X0) ),
% 7.26/1.53      inference(demodulation,[status(thm)],[c_3081,c_4]) ).
% 7.26/1.53  
% 7.26/1.53  cnf(c_1157,plain,
% 7.26/1.53      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 7.26/1.53      inference(superposition,[status(thm)],[c_828,c_468]) ).
% 7.26/1.53  
% 7.26/1.53  cnf(c_1163,plain,
% 7.26/1.53      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
% 7.26/1.53      inference(superposition,[status(thm)],[c_5,c_1157]) ).
% 7.26/1.53  
% 7.26/1.53  cnf(c_6,plain,
% 7.26/1.53      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
% 7.26/1.53      inference(cnf_transformation,[],[f56]) ).
% 7.26/1.53  
% 7.26/1.53  cnf(c_10,negated_conjecture,
% 7.26/1.53      ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) ),
% 7.26/1.53      inference(cnf_transformation,[],[f60]) ).
% 7.26/1.53  
% 7.26/1.53  cnf(c_285,plain,
% 7.26/1.53      ( k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
% 7.26/1.53      inference(demodulation,[status(thm)],[c_6,c_10]) ).
% 7.26/1.53  
% 7.26/1.53  cnf(c_1434,plain,
% 7.26/1.53      ( k5_xboole_0(k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
% 7.26/1.53      inference(demodulation,[status(thm)],[c_1157,c_285]) ).
% 7.26/1.53  
% 7.26/1.53  cnf(c_3413,plain,
% 7.26/1.53      ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
% 7.26/1.53      inference(demodulation,[status(thm)],[c_1163,c_1434]) ).
% 7.26/1.53  
% 7.26/1.53  cnf(c_11186,plain,
% 7.26/1.53      ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
% 7.26/1.53      inference(demodulation,[status(thm)],[c_3144,c_3413]) ).
% 7.26/1.53  
% 7.26/1.53  cnf(c_11797,plain,
% 7.26/1.53      ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)
% 7.26/1.53      | sK1 = sK0 ),
% 7.26/1.53      inference(superposition,[status(thm)],[c_7,c_11186]) ).
% 7.26/1.53  
% 7.26/1.53  cnf(c_9,plain,
% 7.26/1.53      ( X0 = X1
% 7.26/1.53      | k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
% 7.26/1.53      inference(cnf_transformation,[],[f59]) ).
% 7.26/1.53  
% 7.26/1.53  cnf(c_190,plain,
% 7.26/1.53      ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1)
% 7.26/1.53      | sK1 = X0 ),
% 7.26/1.53      inference(instantiation,[status(thm)],[c_9]) ).
% 7.26/1.53  
% 7.26/1.53  cnf(c_191,plain,
% 7.26/1.53      ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)
% 7.26/1.53      | sK1 = sK0 ),
% 7.26/1.53      inference(instantiation,[status(thm)],[c_190]) ).
% 7.26/1.53  
% 7.26/1.53  cnf(c_12043,plain,
% 7.26/1.53      ( sK1 = sK0 ),
% 7.26/1.53      inference(global_propositional_subsumption,[status(thm)],[c_11797,c_191]) ).
% 7.26/1.53  
% 7.26/1.53  cnf(c_481,plain,
% 7.26/1.53      ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
% 7.26/1.53      inference(superposition,[status(thm)],[c_5,c_285]) ).
% 7.26/1.53  
% 7.26/1.53  cnf(c_12048,plain,
% 7.26/1.53      ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
% 7.26/1.53      inference(demodulation,[status(thm)],[c_12043,c_481]) ).
% 7.26/1.53  
% 7.26/1.53  cnf(c_1145,plain,
% 7.26/1.53      ( k5_xboole_0(k5_xboole_0(X0,X1),X1) = X0 ),
% 7.26/1.53      inference(superposition,[status(thm)],[c_468,c_828]) ).
% 7.26/1.53  
% 7.26/1.53  cnf(c_1839,plain,
% 7.26/1.53      ( k5_xboole_0(k1_xboole_0,k3_xboole_0(X0,X1)) = k3_xboole_0(X1,X0) ),
% 7.26/1.53      inference(superposition,[status(thm)],[c_1818,c_1145]) ).
% 7.26/1.53  
% 7.26/1.53  cnf(c_696,plain,
% 7.26/1.53      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,X2))) = X2 ),
% 7.26/1.53      inference(superposition,[status(thm)],[c_5,c_468]) ).
% 7.26/1.53  
% 7.26/1.53  cnf(c_2159,plain,
% 7.26/1.53      ( k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k5_xboole_0(X0,k3_xboole_0(X1,X2))) = k3_xboole_0(X2,X1) ),
% 7.26/1.53      inference(superposition,[status(thm)],[c_1839,c_696]) ).
% 7.26/1.53  
% 7.26/1.53  cnf(c_2190,plain,
% 7.26/1.53      ( k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X1,X2))) = k3_xboole_0(X2,X1) ),
% 7.26/1.53      inference(light_normalisation,[status(thm)],[c_2159,c_4]) ).
% 7.26/1.53  
% 7.26/1.53  cnf(c_12051,plain,
% 7.26/1.53      ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
% 7.26/1.53      inference(demodulation,[status(thm)],[c_12048,c_1,c_2190]) ).
% 7.26/1.53  
% 7.26/1.53  cnf(c_12052,plain,
% 7.26/1.53      ( $false ),
% 7.26/1.53      inference(equality_resolution_simp,[status(thm)],[c_12051]) ).
% 7.26/1.53  
% 7.26/1.53  
% 7.26/1.53  % SZS output end CNFRefutation for theBenchmark.p
% 7.26/1.53  
% 7.26/1.53  ------                               Statistics
% 7.26/1.53  
% 7.26/1.53  ------ General
% 7.26/1.53  
% 7.26/1.53  abstr_ref_over_cycles:                  0
% 7.26/1.53  abstr_ref_under_cycles:                 0
% 7.26/1.53  gc_basic_clause_elim:                   0
% 7.26/1.53  forced_gc_time:                         0
% 7.26/1.53  parsing_time:                           0.013
% 7.26/1.53  unif_index_cands_time:                  0.
% 7.26/1.53  unif_index_add_time:                    0.
% 7.26/1.53  orderings_time:                         0.
% 7.26/1.53  out_proof_time:                         0.008
% 7.26/1.53  total_time:                             0.876
% 7.26/1.53  num_of_symbols:                         39
% 7.26/1.53  num_of_terms:                           16580
% 7.26/1.53  
% 7.26/1.53  ------ Preprocessing
% 7.26/1.53  
% 7.26/1.53  num_of_splits:                          0
% 7.26/1.53  num_of_split_atoms:                     0
% 7.26/1.53  num_of_reused_defs:                     0
% 7.26/1.53  num_eq_ax_congr_red:                    1
% 7.26/1.53  num_of_sem_filtered_clauses:            0
% 7.26/1.53  num_of_subtypes:                        0
% 7.26/1.53  monotx_restored_types:                  0
% 7.26/1.53  sat_num_of_epr_types:                   0
% 7.26/1.53  sat_num_of_non_cyclic_types:            0
% 7.26/1.53  sat_guarded_non_collapsed_types:        0
% 7.26/1.53  num_pure_diseq_elim:                    0
% 7.26/1.53  simp_replaced_by:                       0
% 7.26/1.53  res_preprocessed:                       37
% 7.26/1.53  prep_upred:                             0
% 7.26/1.53  prep_unflattend:                        2
% 7.26/1.53  smt_new_axioms:                         0
% 7.26/1.53  pred_elim_cands:                        0
% 7.26/1.53  pred_elim:                              1
% 7.26/1.53  pred_elim_cl:                           1
% 7.26/1.53  pred_elim_cycles:                       2
% 7.26/1.53  merged_defs:                            0
% 7.26/1.53  merged_defs_ncl:                        0
% 7.26/1.53  bin_hyper_res:                          0
% 7.26/1.53  prep_cycles:                            3
% 7.26/1.53  pred_elim_time:                         0.
% 7.26/1.53  splitting_time:                         0.
% 7.26/1.53  sem_filter_time:                        0.
% 7.26/1.53  monotx_time:                            0.
% 7.26/1.53  subtype_inf_time:                       0.
% 7.26/1.53  
% 7.26/1.53  ------ Problem properties
% 7.26/1.53  
% 7.26/1.53  clauses:                                10
% 7.26/1.53  conjectures:                            1
% 7.26/1.53  epr:                                    0
% 7.26/1.53  horn:                                   8
% 7.26/1.53  ground:                                 1
% 7.26/1.53  unary:                                  8
% 7.26/1.53  binary:                                 2
% 7.26/1.53  lits:                                   12
% 7.26/1.53  lits_eq:                                12
% 7.26/1.53  fd_pure:                                0
% 7.26/1.53  fd_pseudo:                              0
% 7.26/1.53  fd_cond:                                0
% 7.26/1.53  fd_pseudo_cond:                         2
% 7.26/1.53  ac_symbols:                             1
% 7.26/1.53  
% 7.26/1.53  ------ Propositional Solver
% 7.26/1.53  
% 7.26/1.53  prop_solver_calls:                      25
% 7.26/1.53  prop_fast_solver_calls:                 208
% 7.26/1.53  smt_solver_calls:                       0
% 7.26/1.53  smt_fast_solver_calls:                  0
% 7.26/1.53  prop_num_of_clauses:                    2680
% 7.26/1.53  prop_preprocess_simplified:             2756
% 7.26/1.53  prop_fo_subsumed:                       1
% 7.26/1.53  prop_solver_time:                       0.
% 7.26/1.53  smt_solver_time:                        0.
% 7.26/1.53  smt_fast_solver_time:                   0.
% 7.26/1.53  prop_fast_solver_time:                  0.
% 7.26/1.53  prop_unsat_core_time:                   0.
% 7.26/1.53  
% 7.26/1.53  ------ QBF
% 7.26/1.53  
% 7.26/1.53  qbf_q_res:                              0
% 7.26/1.53  qbf_num_tautologies:                    0
% 7.26/1.53  qbf_prep_cycles:                        0
% 7.26/1.53  
% 7.26/1.53  ------ BMC1
% 7.26/1.53  
% 7.26/1.53  bmc1_current_bound:                     -1
% 7.26/1.53  bmc1_last_solved_bound:                 -1
% 7.26/1.53  bmc1_unsat_core_size:                   -1
% 7.26/1.53  bmc1_unsat_core_parents_size:           -1
% 7.26/1.53  bmc1_merge_next_fun:                    0
% 7.26/1.53  bmc1_unsat_core_clauses_time:           0.
% 7.26/1.53  
% 7.26/1.53  ------ Instantiation
% 7.26/1.53  
% 7.26/1.53  inst_num_of_clauses:                    595
% 7.26/1.53  inst_num_in_passive:                    35
% 7.26/1.53  inst_num_in_active:                     268
% 7.26/1.53  inst_num_in_unprocessed:                292
% 7.26/1.53  inst_num_of_loops:                      360
% 7.26/1.53  inst_num_of_learning_restarts:          0
% 7.26/1.53  inst_num_moves_active_passive:          88
% 7.26/1.53  inst_lit_activity:                      0
% 7.26/1.53  inst_lit_activity_moves:                0
% 7.26/1.53  inst_num_tautologies:                   0
% 7.26/1.53  inst_num_prop_implied:                  0
% 7.26/1.53  inst_num_existing_simplified:           0
% 7.26/1.53  inst_num_eq_res_simplified:             0
% 7.26/1.53  inst_num_child_elim:                    0
% 7.26/1.53  inst_num_of_dismatching_blockings:      897
% 7.26/1.53  inst_num_of_non_proper_insts:           776
% 7.26/1.53  inst_num_of_duplicates:                 0
% 7.26/1.53  inst_inst_num_from_inst_to_res:         0
% 7.26/1.53  inst_dismatching_checking_time:         0.
% 7.26/1.53  
% 7.26/1.53  ------ Resolution
% 7.26/1.53  
% 7.26/1.53  res_num_of_clauses:                     0
% 7.26/1.53  res_num_in_passive:                     0
% 7.26/1.53  res_num_in_active:                      0
% 7.26/1.53  res_num_of_loops:                       40
% 7.26/1.53  res_forward_subset_subsumed:            134
% 7.26/1.53  res_backward_subset_subsumed:           2
% 7.26/1.53  res_forward_subsumed:                   0
% 7.26/1.53  res_backward_subsumed:                  0
% 7.26/1.53  res_forward_subsumption_resolution:     0
% 7.26/1.53  res_backward_subsumption_resolution:    0
% 7.26/1.53  res_clause_to_clause_subsumption:       16919
% 7.26/1.53  res_orphan_elimination:                 0
% 7.26/1.53  res_tautology_del:                      56
% 7.26/1.53  res_num_eq_res_simplified:              0
% 7.26/1.53  res_num_sel_changes:                    0
% 7.26/1.53  res_moves_from_active_to_pass:          0
% 7.26/1.53  
% 7.26/1.53  ------ Superposition
% 7.26/1.53  
% 7.26/1.53  sup_time_total:                         0.
% 7.26/1.53  sup_time_generating:                    0.
% 7.26/1.53  sup_time_sim_full:                      0.
% 7.26/1.53  sup_time_sim_immed:                     0.
% 7.26/1.53  
% 7.26/1.53  sup_num_of_clauses:                     1112
% 7.26/1.53  sup_num_in_active:                      56
% 7.26/1.53  sup_num_in_passive:                     1056
% 7.26/1.53  sup_num_of_loops:                       70
% 7.26/1.53  sup_fw_superposition:                   2163
% 7.26/1.53  sup_bw_superposition:                   1872
% 7.26/1.53  sup_immediate_simplified:               1005
% 7.26/1.53  sup_given_eliminated:                   3
% 7.26/1.53  comparisons_done:                       0
% 7.26/1.53  comparisons_avoided:                    4
% 7.26/1.53  
% 7.26/1.53  ------ Simplifications
% 7.26/1.53  
% 7.26/1.53  
% 7.26/1.53  sim_fw_subset_subsumed:                 0
% 7.26/1.53  sim_bw_subset_subsumed:                 0
% 7.26/1.53  sim_fw_subsumed:                        131
% 7.26/1.53  sim_bw_subsumed:                        1
% 7.26/1.53  sim_fw_subsumption_res:                 0
% 7.26/1.53  sim_bw_subsumption_res:                 0
% 7.26/1.53  sim_tautology_del:                      0
% 7.26/1.53  sim_eq_tautology_del:                   154
% 7.26/1.53  sim_eq_res_simp:                        0
% 7.26/1.53  sim_fw_demodulated:                     320
% 7.26/1.53  sim_bw_demodulated:                     78
% 7.26/1.53  sim_light_normalised:                   528
% 7.26/1.53  sim_joinable_taut:                      58
% 7.26/1.53  sim_joinable_simp:                      0
% 7.26/1.53  sim_ac_normalised:                      0
% 7.26/1.53  sim_smt_subsumption:                    0
% 7.26/1.53  
%------------------------------------------------------------------------------
