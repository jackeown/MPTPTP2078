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
% DateTime   : Thu Dec  3 11:29:22 EST 2020

% Result     : Theorem 11.85s
% Output     : CNFRefutation 11.85s
% Verified   : 
% Statistics : Number of formulae       :  141 (3104 expanded)
%              Number of clauses        :   82 ( 664 expanded)
%              Number of leaves         :   20 ( 929 expanded)
%              Depth                    :   26
%              Number of atoms          :  161 (3369 expanded)
%              Number of equality atoms :  142 (3182 expanded)
%              Maximal formula depth    :    8 (   2 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f54,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f27,f33,f33])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f28,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f21])).

fof(f55,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f28,f33])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f53,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f29,f33])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f8,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f6,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

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

fof(f31,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f31,f33])).

fof(f19,conjecture,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f19])).

fof(f24,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f25,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) )
   => ( sK0 != sK1
      & k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) = k1_tarski(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( sK0 != sK1
    & k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) = k1_tarski(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f25])).

fof(f45,plain,(
    k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) = k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f10,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f17])).

fof(f47,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f42,f43])).

fof(f48,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f41,f47])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f40,f48])).

fof(f50,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f39,f49])).

fof(f51,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f38,f50])).

fof(f52,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f37,f51])).

fof(f59,plain,(
    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f45,f36,f52,f52,f52])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f56,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f30,f33])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f44,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f58,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f44,f52,f52])).

fof(f46,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f26])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_2,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_518,plain,
    ( k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_2,c_0])).

cnf(c_7,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_614,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k5_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_0,c_7])).

cnf(c_3662,plain,
    ( k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_518,c_614])).

cnf(c_6,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_615,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X1)) = k5_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_6,c_7])).

cnf(c_1394,plain,
    ( k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))) = k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X1)) ),
    inference(superposition,[status(thm)],[c_0,c_615])).

cnf(c_5,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_183,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_184,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1190,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_183,c_184])).

cnf(c_1412,plain,
    ( k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X1)) = X0 ),
    inference(demodulation,[status(thm)],[c_1394,c_6,c_1190])).

cnf(c_2118,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1412,c_0])).

cnf(c_2242,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2118,c_1])).

cnf(c_2290,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2242,c_0])).

cnf(c_2302,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_2290,c_6])).

cnf(c_2304,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2302,c_2242])).

cnf(c_3720,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
    inference(demodulation,[status(thm)],[c_3662,c_6,c_2304])).

cnf(c_3736,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = X0 ),
    inference(superposition,[status(thm)],[c_1,c_3720])).

cnf(c_10,negated_conjecture,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_616,plain,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),X0)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0) ),
    inference(superposition,[status(thm)],[c_10,c_7])).

cnf(c_707,plain,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),X0))) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),X0)) ),
    inference(superposition,[status(thm)],[c_0,c_616])).

cnf(c_931,plain,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),X0)) ),
    inference(superposition,[status(thm)],[c_1,c_707])).

cnf(c_5330,plain,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) ),
    inference(superposition,[status(thm)],[c_1,c_931])).

cnf(c_603,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_1,c_0])).

cnf(c_703,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k4_xboole_0(X0,X0),X1) ),
    inference(superposition,[status(thm)],[c_518,c_7])).

cnf(c_3193,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(light_normalisation,[status(thm)],[c_703,c_703,c_2304])).

cnf(c_3214,plain,
    ( k5_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_603,c_3193])).

cnf(c_3528,plain,
    ( k5_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_3214,c_0])).

cnf(c_3964,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1)))) = k5_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_3528,c_615])).

cnf(c_5355,plain,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(demodulation,[status(thm)],[c_5330,c_10,c_3964])).

cnf(c_710,plain,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),X0),X1)) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0),X1) ),
    inference(superposition,[status(thm)],[c_616,c_7])).

cnf(c_807,plain,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(X0,X1))) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0),X1) ),
    inference(superposition,[status(thm)],[c_7,c_710])).

cnf(c_817,plain,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(X0,X1)) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0),X1) ),
    inference(demodulation,[status(thm)],[c_807,c_616])).

cnf(c_6271,plain,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k4_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),X0)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0) ),
    inference(superposition,[status(thm)],[c_5355,c_817])).

cnf(c_6417,plain,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) ),
    inference(superposition,[status(thm)],[c_3736,c_6271])).

cnf(c_6453,plain,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(light_normalisation,[status(thm)],[c_6417,c_10])).

cnf(c_704,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) = k4_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_518,c_7])).

cnf(c_5591,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_704,c_2304])).

cnf(c_5614,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X1,X2)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7,c_5591])).

cnf(c_6074,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),X0),k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X1)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_518,c_5614])).

cnf(c_6195,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),X0),X1) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6074,c_6,c_2304])).

cnf(c_7917,plain,
    ( k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6453,c_6195])).

cnf(c_909,plain,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(X0,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0))) = k4_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0)) ),
    inference(superposition,[status(thm)],[c_817,c_518])).

cnf(c_2476,plain,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(X0,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_909,c_2304])).

cnf(c_519,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,X0)) = k4_xboole_0(X0,k4_xboole_0(X0,X0)) ),
    inference(superposition,[status(thm)],[c_2,c_0])).

cnf(c_520,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_519,c_2])).

cnf(c_819,plain,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),X0),X1)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_817,c_710])).

cnf(c_1507,plain,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),X0),k5_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),X0)))) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),X0)) ),
    inference(superposition,[status(thm)],[c_520,c_819])).

cnf(c_1520,plain,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),X0),k5_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),X0)))) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0) ),
    inference(light_normalisation,[status(thm)],[c_1507,c_616])).

cnf(c_1538,plain,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(k4_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),k4_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))))) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) ),
    inference(superposition,[status(thm)],[c_518,c_1520])).

cnf(c_1557,plain,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(k4_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),k4_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))))) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(light_normalisation,[status(thm)],[c_1538,c_10])).

cnf(c_1655,plain,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(k4_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),k4_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))),X0)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0) ),
    inference(superposition,[status(thm)],[c_1557,c_7])).

cnf(c_2516,plain,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(k4_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),k4_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2476,c_1655])).

cnf(c_2517,plain,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2516,c_1557])).

cnf(c_7948,plain,
    ( k5_xboole_0(k1_xboole_0,k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_7917,c_2517])).

cnf(c_3212,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,X0)) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_518,c_3193])).

cnf(c_3310,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_3212,c_520])).

cnf(c_3952,plain,
    ( k5_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1,c_3528])).

cnf(c_6094,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X1,k5_xboole_0(X0,k4_xboole_0(X1,X1)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_518,c_5614])).

cnf(c_6178,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6094,c_6,c_2304])).

cnf(c_7430,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3528,c_6178])).

cnf(c_605,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1,c_0])).

cnf(c_3138,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_1,c_605])).

cnf(c_7577,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7430,c_6,c_3138])).

cnf(c_7653,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_7577,c_1])).

cnf(c_7661,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_7653,c_2302])).

cnf(c_7949,plain,
    ( k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7948,c_3310,c_3952,c_7661])).

cnf(c_3,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_185,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_606,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_185])).

cnf(c_23036,plain,
    ( r1_tarski(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k1_xboole_0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7949,c_606])).

cnf(c_23073,plain,
    ( r1_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_23036,c_2302])).

cnf(c_8,plain,
    ( ~ r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
    | X1 = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_190,plain,
    ( ~ r1_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | sK0 = sK1 ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_191,plain,
    ( sK0 = sK1
    | r1_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_190])).

cnf(c_9,negated_conjecture,
    ( sK0 != sK1 ),
    inference(cnf_transformation,[],[f46])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_23073,c_191,c_9])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:05:34 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 11.85/1.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.85/1.99  
% 11.85/1.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.85/1.99  
% 11.85/1.99  ------  iProver source info
% 11.85/1.99  
% 11.85/1.99  git: date: 2020-06-30 10:37:57 +0100
% 11.85/1.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.85/1.99  git: non_committed_changes: false
% 11.85/1.99  git: last_make_outside_of_git: false
% 11.85/1.99  
% 11.85/1.99  ------ 
% 11.85/1.99  
% 11.85/1.99  ------ Input Options
% 11.85/1.99  
% 11.85/1.99  --out_options                           all
% 11.85/1.99  --tptp_safe_out                         true
% 11.85/1.99  --problem_path                          ""
% 11.85/1.99  --include_path                          ""
% 11.85/1.99  --clausifier                            res/vclausify_rel
% 11.85/1.99  --clausifier_options                    ""
% 11.85/1.99  --stdin                                 false
% 11.85/1.99  --stats_out                             all
% 11.85/1.99  
% 11.85/1.99  ------ General Options
% 11.85/1.99  
% 11.85/1.99  --fof                                   false
% 11.85/1.99  --time_out_real                         305.
% 11.85/1.99  --time_out_virtual                      -1.
% 11.85/1.99  --symbol_type_check                     false
% 11.85/1.99  --clausify_out                          false
% 11.85/1.99  --sig_cnt_out                           false
% 11.85/1.99  --trig_cnt_out                          false
% 11.85/1.99  --trig_cnt_out_tolerance                1.
% 11.85/1.99  --trig_cnt_out_sk_spl                   false
% 11.85/1.99  --abstr_cl_out                          false
% 11.85/1.99  
% 11.85/1.99  ------ Global Options
% 11.85/1.99  
% 11.85/1.99  --schedule                              default
% 11.85/1.99  --add_important_lit                     false
% 11.85/1.99  --prop_solver_per_cl                    1000
% 11.85/1.99  --min_unsat_core                        false
% 11.85/1.99  --soft_assumptions                      false
% 11.85/1.99  --soft_lemma_size                       3
% 11.85/1.99  --prop_impl_unit_size                   0
% 11.85/1.99  --prop_impl_unit                        []
% 11.85/1.99  --share_sel_clauses                     true
% 11.85/1.99  --reset_solvers                         false
% 11.85/1.99  --bc_imp_inh                            [conj_cone]
% 11.85/1.99  --conj_cone_tolerance                   3.
% 11.85/1.99  --extra_neg_conj                        none
% 11.85/1.99  --large_theory_mode                     true
% 11.85/1.99  --prolific_symb_bound                   200
% 11.85/1.99  --lt_threshold                          2000
% 11.85/1.99  --clause_weak_htbl                      true
% 11.85/1.99  --gc_record_bc_elim                     false
% 11.85/1.99  
% 11.85/1.99  ------ Preprocessing Options
% 11.85/1.99  
% 11.85/1.99  --preprocessing_flag                    true
% 11.85/1.99  --time_out_prep_mult                    0.1
% 11.85/1.99  --splitting_mode                        input
% 11.85/1.99  --splitting_grd                         true
% 11.85/1.99  --splitting_cvd                         false
% 11.85/1.99  --splitting_cvd_svl                     false
% 11.85/1.99  --splitting_nvd                         32
% 11.85/1.99  --sub_typing                            true
% 11.85/1.99  --prep_gs_sim                           true
% 11.85/1.99  --prep_unflatten                        true
% 11.85/1.99  --prep_res_sim                          true
% 11.85/1.99  --prep_upred                            true
% 11.85/1.99  --prep_sem_filter                       exhaustive
% 11.85/1.99  --prep_sem_filter_out                   false
% 11.85/1.99  --pred_elim                             true
% 11.85/1.99  --res_sim_input                         true
% 11.85/1.99  --eq_ax_congr_red                       true
% 11.85/1.99  --pure_diseq_elim                       true
% 11.85/1.99  --brand_transform                       false
% 11.85/1.99  --non_eq_to_eq                          false
% 11.85/1.99  --prep_def_merge                        true
% 11.85/1.99  --prep_def_merge_prop_impl              false
% 11.85/1.99  --prep_def_merge_mbd                    true
% 11.85/1.99  --prep_def_merge_tr_red                 false
% 11.85/1.99  --prep_def_merge_tr_cl                  false
% 11.85/1.99  --smt_preprocessing                     true
% 11.85/1.99  --smt_ac_axioms                         fast
% 11.85/1.99  --preprocessed_out                      false
% 11.85/1.99  --preprocessed_stats                    false
% 11.85/1.99  
% 11.85/1.99  ------ Abstraction refinement Options
% 11.85/1.99  
% 11.85/1.99  --abstr_ref                             []
% 11.85/1.99  --abstr_ref_prep                        false
% 11.85/1.99  --abstr_ref_until_sat                   false
% 11.85/1.99  --abstr_ref_sig_restrict                funpre
% 11.85/1.99  --abstr_ref_af_restrict_to_split_sk     false
% 11.85/1.99  --abstr_ref_under                       []
% 11.85/1.99  
% 11.85/1.99  ------ SAT Options
% 11.85/1.99  
% 11.85/1.99  --sat_mode                              false
% 11.85/1.99  --sat_fm_restart_options                ""
% 11.85/1.99  --sat_gr_def                            false
% 11.85/1.99  --sat_epr_types                         true
% 11.85/1.99  --sat_non_cyclic_types                  false
% 11.85/1.99  --sat_finite_models                     false
% 11.85/1.99  --sat_fm_lemmas                         false
% 11.85/1.99  --sat_fm_prep                           false
% 11.85/1.99  --sat_fm_uc_incr                        true
% 11.85/1.99  --sat_out_model                         small
% 11.85/1.99  --sat_out_clauses                       false
% 11.85/1.99  
% 11.85/1.99  ------ QBF Options
% 11.85/1.99  
% 11.85/1.99  --qbf_mode                              false
% 11.85/1.99  --qbf_elim_univ                         false
% 11.85/1.99  --qbf_dom_inst                          none
% 11.85/1.99  --qbf_dom_pre_inst                      false
% 11.85/1.99  --qbf_sk_in                             false
% 11.85/1.99  --qbf_pred_elim                         true
% 11.85/1.99  --qbf_split                             512
% 11.85/1.99  
% 11.85/1.99  ------ BMC1 Options
% 11.85/1.99  
% 11.85/1.99  --bmc1_incremental                      false
% 11.85/1.99  --bmc1_axioms                           reachable_all
% 11.85/1.99  --bmc1_min_bound                        0
% 11.85/1.99  --bmc1_max_bound                        -1
% 11.85/1.99  --bmc1_max_bound_default                -1
% 11.85/1.99  --bmc1_symbol_reachability              true
% 11.85/1.99  --bmc1_property_lemmas                  false
% 11.85/1.99  --bmc1_k_induction                      false
% 11.85/1.99  --bmc1_non_equiv_states                 false
% 11.85/1.99  --bmc1_deadlock                         false
% 11.85/1.99  --bmc1_ucm                              false
% 11.85/1.99  --bmc1_add_unsat_core                   none
% 11.85/1.99  --bmc1_unsat_core_children              false
% 11.85/1.99  --bmc1_unsat_core_extrapolate_axioms    false
% 11.85/1.99  --bmc1_out_stat                         full
% 11.85/1.99  --bmc1_ground_init                      false
% 11.85/1.99  --bmc1_pre_inst_next_state              false
% 11.85/1.99  --bmc1_pre_inst_state                   false
% 11.85/1.99  --bmc1_pre_inst_reach_state             false
% 11.85/1.99  --bmc1_out_unsat_core                   false
% 11.85/1.99  --bmc1_aig_witness_out                  false
% 11.85/1.99  --bmc1_verbose                          false
% 11.85/1.99  --bmc1_dump_clauses_tptp                false
% 11.85/1.99  --bmc1_dump_unsat_core_tptp             false
% 11.85/1.99  --bmc1_dump_file                        -
% 11.85/1.99  --bmc1_ucm_expand_uc_limit              128
% 11.85/1.99  --bmc1_ucm_n_expand_iterations          6
% 11.85/1.99  --bmc1_ucm_extend_mode                  1
% 11.85/1.99  --bmc1_ucm_init_mode                    2
% 11.85/1.99  --bmc1_ucm_cone_mode                    none
% 11.85/1.99  --bmc1_ucm_reduced_relation_type        0
% 11.85/1.99  --bmc1_ucm_relax_model                  4
% 11.85/1.99  --bmc1_ucm_full_tr_after_sat            true
% 11.85/1.99  --bmc1_ucm_expand_neg_assumptions       false
% 11.85/1.99  --bmc1_ucm_layered_model                none
% 11.85/1.99  --bmc1_ucm_max_lemma_size               10
% 11.85/1.99  
% 11.85/1.99  ------ AIG Options
% 11.85/1.99  
% 11.85/1.99  --aig_mode                              false
% 11.85/1.99  
% 11.85/1.99  ------ Instantiation Options
% 11.85/1.99  
% 11.85/1.99  --instantiation_flag                    true
% 11.85/1.99  --inst_sos_flag                         true
% 11.85/1.99  --inst_sos_phase                        true
% 11.85/1.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.85/1.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.85/1.99  --inst_lit_sel_side                     num_symb
% 11.85/1.99  --inst_solver_per_active                1400
% 11.85/1.99  --inst_solver_calls_frac                1.
% 11.85/1.99  --inst_passive_queue_type               priority_queues
% 11.85/1.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.85/1.99  --inst_passive_queues_freq              [25;2]
% 11.85/1.99  --inst_dismatching                      true
% 11.85/1.99  --inst_eager_unprocessed_to_passive     true
% 11.85/1.99  --inst_prop_sim_given                   true
% 11.85/1.99  --inst_prop_sim_new                     false
% 11.85/1.99  --inst_subs_new                         false
% 11.85/1.99  --inst_eq_res_simp                      false
% 11.85/1.99  --inst_subs_given                       false
% 11.85/1.99  --inst_orphan_elimination               true
% 11.85/1.99  --inst_learning_loop_flag               true
% 11.85/1.99  --inst_learning_start                   3000
% 11.85/1.99  --inst_learning_factor                  2
% 11.85/1.99  --inst_start_prop_sim_after_learn       3
% 11.85/1.99  --inst_sel_renew                        solver
% 11.85/1.99  --inst_lit_activity_flag                true
% 11.85/1.99  --inst_restr_to_given                   false
% 11.85/1.99  --inst_activity_threshold               500
% 11.85/1.99  --inst_out_proof                        true
% 11.85/1.99  
% 11.85/1.99  ------ Resolution Options
% 11.85/1.99  
% 11.85/1.99  --resolution_flag                       true
% 11.85/1.99  --res_lit_sel                           adaptive
% 11.85/1.99  --res_lit_sel_side                      none
% 11.85/1.99  --res_ordering                          kbo
% 11.85/1.99  --res_to_prop_solver                    active
% 11.85/1.99  --res_prop_simpl_new                    false
% 11.85/1.99  --res_prop_simpl_given                  true
% 11.85/1.99  --res_passive_queue_type                priority_queues
% 11.85/1.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.85/1.99  --res_passive_queues_freq               [15;5]
% 11.85/1.99  --res_forward_subs                      full
% 11.85/1.99  --res_backward_subs                     full
% 11.85/1.99  --res_forward_subs_resolution           true
% 11.85/1.99  --res_backward_subs_resolution          true
% 11.85/1.99  --res_orphan_elimination                true
% 11.85/1.99  --res_time_limit                        2.
% 11.85/1.99  --res_out_proof                         true
% 11.85/1.99  
% 11.85/1.99  ------ Superposition Options
% 11.85/1.99  
% 11.85/1.99  --superposition_flag                    true
% 11.85/1.99  --sup_passive_queue_type                priority_queues
% 11.85/1.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.85/1.99  --sup_passive_queues_freq               [8;1;4]
% 11.85/1.99  --demod_completeness_check              fast
% 11.85/1.99  --demod_use_ground                      true
% 11.85/1.99  --sup_to_prop_solver                    passive
% 11.85/1.99  --sup_prop_simpl_new                    true
% 11.85/1.99  --sup_prop_simpl_given                  true
% 11.85/1.99  --sup_fun_splitting                     true
% 11.85/1.99  --sup_smt_interval                      50000
% 11.85/1.99  
% 11.85/1.99  ------ Superposition Simplification Setup
% 11.85/1.99  
% 11.85/1.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.85/1.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.85/1.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.85/1.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.85/1.99  --sup_full_triv                         [TrivRules;PropSubs]
% 11.85/1.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.85/1.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.85/1.99  --sup_immed_triv                        [TrivRules]
% 11.85/1.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.85/1.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.85/1.99  --sup_immed_bw_main                     []
% 11.85/1.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.85/1.99  --sup_input_triv                        [Unflattening;TrivRules]
% 11.85/1.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.85/1.99  --sup_input_bw                          []
% 11.85/1.99  
% 11.85/1.99  ------ Combination Options
% 11.85/1.99  
% 11.85/1.99  --comb_res_mult                         3
% 11.85/1.99  --comb_sup_mult                         2
% 11.85/1.99  --comb_inst_mult                        10
% 11.85/1.99  
% 11.85/1.99  ------ Debug Options
% 11.85/1.99  
% 11.85/1.99  --dbg_backtrace                         false
% 11.85/1.99  --dbg_dump_prop_clauses                 false
% 11.85/1.99  --dbg_dump_prop_clauses_file            -
% 11.85/1.99  --dbg_out_stat                          false
% 11.85/1.99  ------ Parsing...
% 11.85/1.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.85/1.99  
% 11.85/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 11.85/1.99  
% 11.85/1.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.85/1.99  
% 11.85/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.85/1.99  ------ Proving...
% 11.85/1.99  ------ Problem Properties 
% 11.85/1.99  
% 11.85/1.99  
% 11.85/1.99  clauses                                 11
% 11.85/1.99  conjectures                             2
% 11.85/1.99  EPR                                     2
% 11.85/1.99  Horn                                    11
% 11.85/1.99  unary                                   9
% 11.85/1.99  binary                                  2
% 11.85/1.99  lits                                    13
% 11.85/1.99  lits eq                                 9
% 11.85/1.99  fd_pure                                 0
% 11.85/1.99  fd_pseudo                               0
% 11.85/1.99  fd_cond                                 0
% 11.85/1.99  fd_pseudo_cond                          1
% 11.85/1.99  AC symbols                              0
% 11.85/1.99  
% 11.85/1.99  ------ Schedule dynamic 5 is on 
% 11.85/1.99  
% 11.85/1.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.85/1.99  
% 11.85/1.99  
% 11.85/1.99  ------ 
% 11.85/1.99  Current options:
% 11.85/1.99  ------ 
% 11.85/1.99  
% 11.85/1.99  ------ Input Options
% 11.85/1.99  
% 11.85/1.99  --out_options                           all
% 11.85/1.99  --tptp_safe_out                         true
% 11.85/1.99  --problem_path                          ""
% 11.85/1.99  --include_path                          ""
% 11.85/1.99  --clausifier                            res/vclausify_rel
% 11.85/1.99  --clausifier_options                    ""
% 11.85/1.99  --stdin                                 false
% 11.85/1.99  --stats_out                             all
% 11.85/1.99  
% 11.85/1.99  ------ General Options
% 11.85/1.99  
% 11.85/1.99  --fof                                   false
% 11.85/1.99  --time_out_real                         305.
% 11.85/1.99  --time_out_virtual                      -1.
% 11.85/1.99  --symbol_type_check                     false
% 11.85/1.99  --clausify_out                          false
% 11.85/1.99  --sig_cnt_out                           false
% 11.85/1.99  --trig_cnt_out                          false
% 11.85/1.99  --trig_cnt_out_tolerance                1.
% 11.85/1.99  --trig_cnt_out_sk_spl                   false
% 11.85/1.99  --abstr_cl_out                          false
% 11.85/1.99  
% 11.85/1.99  ------ Global Options
% 11.85/1.99  
% 11.85/1.99  --schedule                              default
% 11.85/1.99  --add_important_lit                     false
% 11.85/1.99  --prop_solver_per_cl                    1000
% 11.85/1.99  --min_unsat_core                        false
% 11.85/1.99  --soft_assumptions                      false
% 11.85/1.99  --soft_lemma_size                       3
% 11.85/1.99  --prop_impl_unit_size                   0
% 11.85/1.99  --prop_impl_unit                        []
% 11.85/1.99  --share_sel_clauses                     true
% 11.85/1.99  --reset_solvers                         false
% 11.85/1.99  --bc_imp_inh                            [conj_cone]
% 11.85/1.99  --conj_cone_tolerance                   3.
% 11.85/1.99  --extra_neg_conj                        none
% 11.85/1.99  --large_theory_mode                     true
% 11.85/1.99  --prolific_symb_bound                   200
% 11.85/1.99  --lt_threshold                          2000
% 11.85/1.99  --clause_weak_htbl                      true
% 11.85/1.99  --gc_record_bc_elim                     false
% 11.85/1.99  
% 11.85/1.99  ------ Preprocessing Options
% 11.85/1.99  
% 11.85/1.99  --preprocessing_flag                    true
% 11.85/1.99  --time_out_prep_mult                    0.1
% 11.85/1.99  --splitting_mode                        input
% 11.85/1.99  --splitting_grd                         true
% 11.85/1.99  --splitting_cvd                         false
% 11.85/1.99  --splitting_cvd_svl                     false
% 11.85/1.99  --splitting_nvd                         32
% 11.85/1.99  --sub_typing                            true
% 11.85/1.99  --prep_gs_sim                           true
% 11.85/1.99  --prep_unflatten                        true
% 11.85/1.99  --prep_res_sim                          true
% 11.85/1.99  --prep_upred                            true
% 11.85/1.99  --prep_sem_filter                       exhaustive
% 11.85/1.99  --prep_sem_filter_out                   false
% 11.85/1.99  --pred_elim                             true
% 11.85/1.99  --res_sim_input                         true
% 11.85/1.99  --eq_ax_congr_red                       true
% 11.85/1.99  --pure_diseq_elim                       true
% 11.85/1.99  --brand_transform                       false
% 11.85/1.99  --non_eq_to_eq                          false
% 11.85/1.99  --prep_def_merge                        true
% 11.85/1.99  --prep_def_merge_prop_impl              false
% 11.85/1.99  --prep_def_merge_mbd                    true
% 11.85/1.99  --prep_def_merge_tr_red                 false
% 11.85/1.99  --prep_def_merge_tr_cl                  false
% 11.85/1.99  --smt_preprocessing                     true
% 11.85/1.99  --smt_ac_axioms                         fast
% 11.85/1.99  --preprocessed_out                      false
% 11.85/1.99  --preprocessed_stats                    false
% 11.85/1.99  
% 11.85/1.99  ------ Abstraction refinement Options
% 11.85/1.99  
% 11.85/1.99  --abstr_ref                             []
% 11.85/1.99  --abstr_ref_prep                        false
% 11.85/1.99  --abstr_ref_until_sat                   false
% 11.85/1.99  --abstr_ref_sig_restrict                funpre
% 11.85/1.99  --abstr_ref_af_restrict_to_split_sk     false
% 11.85/1.99  --abstr_ref_under                       []
% 11.85/1.99  
% 11.85/1.99  ------ SAT Options
% 11.85/1.99  
% 11.85/1.99  --sat_mode                              false
% 11.85/1.99  --sat_fm_restart_options                ""
% 11.85/1.99  --sat_gr_def                            false
% 11.85/1.99  --sat_epr_types                         true
% 11.85/1.99  --sat_non_cyclic_types                  false
% 11.85/1.99  --sat_finite_models                     false
% 11.85/1.99  --sat_fm_lemmas                         false
% 11.85/1.99  --sat_fm_prep                           false
% 11.85/1.99  --sat_fm_uc_incr                        true
% 11.85/1.99  --sat_out_model                         small
% 11.85/1.99  --sat_out_clauses                       false
% 11.85/1.99  
% 11.85/1.99  ------ QBF Options
% 11.85/1.99  
% 11.85/1.99  --qbf_mode                              false
% 11.85/1.99  --qbf_elim_univ                         false
% 11.85/1.99  --qbf_dom_inst                          none
% 11.85/1.99  --qbf_dom_pre_inst                      false
% 11.85/1.99  --qbf_sk_in                             false
% 11.85/1.99  --qbf_pred_elim                         true
% 11.85/1.99  --qbf_split                             512
% 11.85/1.99  
% 11.85/1.99  ------ BMC1 Options
% 11.85/1.99  
% 11.85/1.99  --bmc1_incremental                      false
% 11.85/1.99  --bmc1_axioms                           reachable_all
% 11.85/1.99  --bmc1_min_bound                        0
% 11.85/1.99  --bmc1_max_bound                        -1
% 11.85/1.99  --bmc1_max_bound_default                -1
% 11.85/1.99  --bmc1_symbol_reachability              true
% 11.85/1.99  --bmc1_property_lemmas                  false
% 11.85/1.99  --bmc1_k_induction                      false
% 11.85/1.99  --bmc1_non_equiv_states                 false
% 11.85/1.99  --bmc1_deadlock                         false
% 11.85/1.99  --bmc1_ucm                              false
% 11.85/1.99  --bmc1_add_unsat_core                   none
% 11.85/1.99  --bmc1_unsat_core_children              false
% 11.85/1.99  --bmc1_unsat_core_extrapolate_axioms    false
% 11.85/1.99  --bmc1_out_stat                         full
% 11.85/1.99  --bmc1_ground_init                      false
% 11.85/1.99  --bmc1_pre_inst_next_state              false
% 11.85/1.99  --bmc1_pre_inst_state                   false
% 11.85/1.99  --bmc1_pre_inst_reach_state             false
% 11.85/1.99  --bmc1_out_unsat_core                   false
% 11.85/1.99  --bmc1_aig_witness_out                  false
% 11.85/1.99  --bmc1_verbose                          false
% 11.85/1.99  --bmc1_dump_clauses_tptp                false
% 11.85/1.99  --bmc1_dump_unsat_core_tptp             false
% 11.85/1.99  --bmc1_dump_file                        -
% 11.85/1.99  --bmc1_ucm_expand_uc_limit              128
% 11.85/1.99  --bmc1_ucm_n_expand_iterations          6
% 11.85/1.99  --bmc1_ucm_extend_mode                  1
% 11.85/1.99  --bmc1_ucm_init_mode                    2
% 11.85/1.99  --bmc1_ucm_cone_mode                    none
% 11.85/1.99  --bmc1_ucm_reduced_relation_type        0
% 11.85/1.99  --bmc1_ucm_relax_model                  4
% 11.85/1.99  --bmc1_ucm_full_tr_after_sat            true
% 11.85/1.99  --bmc1_ucm_expand_neg_assumptions       false
% 11.85/1.99  --bmc1_ucm_layered_model                none
% 11.85/1.99  --bmc1_ucm_max_lemma_size               10
% 11.85/1.99  
% 11.85/1.99  ------ AIG Options
% 11.85/1.99  
% 11.85/1.99  --aig_mode                              false
% 11.85/1.99  
% 11.85/1.99  ------ Instantiation Options
% 11.85/1.99  
% 11.85/1.99  --instantiation_flag                    true
% 11.85/1.99  --inst_sos_flag                         true
% 11.85/1.99  --inst_sos_phase                        true
% 11.85/1.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.85/1.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.85/1.99  --inst_lit_sel_side                     none
% 11.85/1.99  --inst_solver_per_active                1400
% 11.85/1.99  --inst_solver_calls_frac                1.
% 11.85/1.99  --inst_passive_queue_type               priority_queues
% 11.85/1.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.85/1.99  --inst_passive_queues_freq              [25;2]
% 11.85/1.99  --inst_dismatching                      true
% 11.85/1.99  --inst_eager_unprocessed_to_passive     true
% 11.85/1.99  --inst_prop_sim_given                   true
% 11.85/1.99  --inst_prop_sim_new                     false
% 11.85/1.99  --inst_subs_new                         false
% 11.85/1.99  --inst_eq_res_simp                      false
% 11.85/1.99  --inst_subs_given                       false
% 11.85/1.99  --inst_orphan_elimination               true
% 11.85/1.99  --inst_learning_loop_flag               true
% 11.85/1.99  --inst_learning_start                   3000
% 11.85/1.99  --inst_learning_factor                  2
% 11.85/1.99  --inst_start_prop_sim_after_learn       3
% 11.85/1.99  --inst_sel_renew                        solver
% 11.85/1.99  --inst_lit_activity_flag                true
% 11.85/1.99  --inst_restr_to_given                   false
% 11.85/1.99  --inst_activity_threshold               500
% 11.85/1.99  --inst_out_proof                        true
% 11.85/1.99  
% 11.85/1.99  ------ Resolution Options
% 11.85/1.99  
% 11.85/1.99  --resolution_flag                       false
% 11.85/1.99  --res_lit_sel                           adaptive
% 11.85/1.99  --res_lit_sel_side                      none
% 11.85/1.99  --res_ordering                          kbo
% 11.85/1.99  --res_to_prop_solver                    active
% 11.85/1.99  --res_prop_simpl_new                    false
% 11.85/1.99  --res_prop_simpl_given                  true
% 11.85/1.99  --res_passive_queue_type                priority_queues
% 11.85/1.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.85/1.99  --res_passive_queues_freq               [15;5]
% 11.85/1.99  --res_forward_subs                      full
% 11.85/1.99  --res_backward_subs                     full
% 11.85/1.99  --res_forward_subs_resolution           true
% 11.85/1.99  --res_backward_subs_resolution          true
% 11.85/1.99  --res_orphan_elimination                true
% 11.85/1.99  --res_time_limit                        2.
% 11.85/1.99  --res_out_proof                         true
% 11.85/1.99  
% 11.85/1.99  ------ Superposition Options
% 11.85/1.99  
% 11.85/1.99  --superposition_flag                    true
% 11.85/1.99  --sup_passive_queue_type                priority_queues
% 11.85/1.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.85/1.99  --sup_passive_queues_freq               [8;1;4]
% 11.85/1.99  --demod_completeness_check              fast
% 11.85/1.99  --demod_use_ground                      true
% 11.85/1.99  --sup_to_prop_solver                    passive
% 11.85/1.99  --sup_prop_simpl_new                    true
% 11.85/1.99  --sup_prop_simpl_given                  true
% 11.85/1.99  --sup_fun_splitting                     true
% 11.85/1.99  --sup_smt_interval                      50000
% 11.85/1.99  
% 11.85/1.99  ------ Superposition Simplification Setup
% 11.85/1.99  
% 11.85/1.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.85/1.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.85/1.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.85/1.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.85/1.99  --sup_full_triv                         [TrivRules;PropSubs]
% 11.85/1.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.85/1.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.85/1.99  --sup_immed_triv                        [TrivRules]
% 11.85/1.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.85/1.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.85/1.99  --sup_immed_bw_main                     []
% 11.85/1.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.85/1.99  --sup_input_triv                        [Unflattening;TrivRules]
% 11.85/1.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.85/1.99  --sup_input_bw                          []
% 11.85/1.99  
% 11.85/1.99  ------ Combination Options
% 11.85/1.99  
% 11.85/1.99  --comb_res_mult                         3
% 11.85/1.99  --comb_sup_mult                         2
% 11.85/1.99  --comb_inst_mult                        10
% 11.85/1.99  
% 11.85/1.99  ------ Debug Options
% 11.85/1.99  
% 11.85/1.99  --dbg_backtrace                         false
% 11.85/1.99  --dbg_dump_prop_clauses                 false
% 11.85/1.99  --dbg_dump_prop_clauses_file            -
% 11.85/1.99  --dbg_out_stat                          false
% 11.85/1.99  
% 11.85/1.99  
% 11.85/1.99  
% 11.85/1.99  
% 11.85/1.99  ------ Proving...
% 11.85/1.99  
% 11.85/1.99  
% 11.85/1.99  % SZS status Theorem for theBenchmark.p
% 11.85/1.99  
% 11.85/1.99  % SZS output start CNFRefutation for theBenchmark.p
% 11.85/1.99  
% 11.85/1.99  fof(f1,axiom,(
% 11.85/1.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 11.85/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.85/1.99  
% 11.85/1.99  fof(f27,plain,(
% 11.85/1.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 11.85/1.99    inference(cnf_transformation,[],[f1])).
% 11.85/1.99  
% 11.85/1.99  fof(f7,axiom,(
% 11.85/1.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 11.85/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.85/1.99  
% 11.85/1.99  fof(f33,plain,(
% 11.85/1.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 11.85/1.99    inference(cnf_transformation,[],[f7])).
% 11.85/1.99  
% 11.85/1.99  fof(f54,plain,(
% 11.85/1.99    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 11.85/1.99    inference(definition_unfolding,[],[f27,f33,f33])).
% 11.85/1.99  
% 11.85/1.99  fof(f2,axiom,(
% 11.85/1.99    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 11.85/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.85/1.99  
% 11.85/1.99  fof(f21,plain,(
% 11.85/1.99    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 11.85/1.99    inference(rectify,[],[f2])).
% 11.85/1.99  
% 11.85/1.99  fof(f28,plain,(
% 11.85/1.99    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 11.85/1.99    inference(cnf_transformation,[],[f21])).
% 11.85/1.99  
% 11.85/1.99  fof(f55,plain,(
% 11.85/1.99    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 11.85/1.99    inference(definition_unfolding,[],[f28,f33])).
% 11.85/1.99  
% 11.85/1.99  fof(f3,axiom,(
% 11.85/1.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 11.85/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.85/1.99  
% 11.85/1.99  fof(f29,plain,(
% 11.85/1.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 11.85/1.99    inference(cnf_transformation,[],[f3])).
% 11.85/1.99  
% 11.85/1.99  fof(f53,plain,(
% 11.85/1.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 11.85/1.99    inference(definition_unfolding,[],[f29,f33])).
% 11.85/1.99  
% 11.85/1.99  fof(f9,axiom,(
% 11.85/1.99    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 11.85/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.85/1.99  
% 11.85/1.99  fof(f35,plain,(
% 11.85/1.99    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 11.85/1.99    inference(cnf_transformation,[],[f9])).
% 11.85/1.99  
% 11.85/1.99  fof(f8,axiom,(
% 11.85/1.99    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 11.85/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.85/1.99  
% 11.85/1.99  fof(f34,plain,(
% 11.85/1.99    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 11.85/1.99    inference(cnf_transformation,[],[f8])).
% 11.85/1.99  
% 11.85/1.99  fof(f6,axiom,(
% 11.85/1.99    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 11.85/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.85/1.99  
% 11.85/1.99  fof(f32,plain,(
% 11.85/1.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 11.85/1.99    inference(cnf_transformation,[],[f6])).
% 11.85/1.99  
% 11.85/1.99  fof(f5,axiom,(
% 11.85/1.99    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 11.85/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.85/1.99  
% 11.85/1.99  fof(f22,plain,(
% 11.85/1.99    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 11.85/1.99    inference(ennf_transformation,[],[f5])).
% 11.85/1.99  
% 11.85/1.99  fof(f31,plain,(
% 11.85/1.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 11.85/1.99    inference(cnf_transformation,[],[f22])).
% 11.85/1.99  
% 11.85/1.99  fof(f57,plain,(
% 11.85/1.99    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 11.85/1.99    inference(definition_unfolding,[],[f31,f33])).
% 11.85/1.99  
% 11.85/1.99  fof(f19,conjecture,(
% 11.85/1.99    ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) => X0 = X1)),
% 11.85/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.85/1.99  
% 11.85/1.99  fof(f20,negated_conjecture,(
% 11.85/1.99    ~! [X0,X1] : (k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) => X0 = X1)),
% 11.85/1.99    inference(negated_conjecture,[],[f19])).
% 11.85/1.99  
% 11.85/1.99  fof(f24,plain,(
% 11.85/1.99    ? [X0,X1] : (X0 != X1 & k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0))),
% 11.85/1.99    inference(ennf_transformation,[],[f20])).
% 11.85/1.99  
% 11.85/1.99  fof(f25,plain,(
% 11.85/1.99    ? [X0,X1] : (X0 != X1 & k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)) => (sK0 != sK1 & k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) = k1_tarski(sK0))),
% 11.85/1.99    introduced(choice_axiom,[])).
% 11.85/1.99  
% 11.85/1.99  fof(f26,plain,(
% 11.85/1.99    sK0 != sK1 & k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) = k1_tarski(sK0)),
% 11.85/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f25])).
% 11.85/1.99  
% 11.85/1.99  fof(f45,plain,(
% 11.85/1.99    k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) = k1_tarski(sK0)),
% 11.85/1.99    inference(cnf_transformation,[],[f26])).
% 11.85/1.99  
% 11.85/1.99  fof(f10,axiom,(
% 11.85/1.99    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 11.85/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.85/1.99  
% 11.85/1.99  fof(f36,plain,(
% 11.85/1.99    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 11.85/1.99    inference(cnf_transformation,[],[f10])).
% 11.85/1.99  
% 11.85/1.99  fof(f11,axiom,(
% 11.85/1.99    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 11.85/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.85/1.99  
% 11.85/1.99  fof(f37,plain,(
% 11.85/1.99    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 11.85/1.99    inference(cnf_transformation,[],[f11])).
% 11.85/1.99  
% 11.85/1.99  fof(f12,axiom,(
% 11.85/1.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 11.85/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.85/1.99  
% 11.85/1.99  fof(f38,plain,(
% 11.85/1.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 11.85/1.99    inference(cnf_transformation,[],[f12])).
% 11.85/1.99  
% 11.85/1.99  fof(f13,axiom,(
% 11.85/1.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 11.85/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.85/1.99  
% 11.85/1.99  fof(f39,plain,(
% 11.85/1.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 11.85/1.99    inference(cnf_transformation,[],[f13])).
% 11.85/1.99  
% 11.85/1.99  fof(f14,axiom,(
% 11.85/1.99    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 11.85/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.85/1.99  
% 11.85/1.99  fof(f40,plain,(
% 11.85/1.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 11.85/1.99    inference(cnf_transformation,[],[f14])).
% 11.85/1.99  
% 11.85/1.99  fof(f15,axiom,(
% 11.85/1.99    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 11.85/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.85/1.99  
% 11.85/1.99  fof(f41,plain,(
% 11.85/1.99    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 11.85/1.99    inference(cnf_transformation,[],[f15])).
% 11.85/1.99  
% 11.85/1.99  fof(f16,axiom,(
% 11.85/1.99    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 11.85/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.85/1.99  
% 11.85/1.99  fof(f42,plain,(
% 11.85/1.99    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 11.85/1.99    inference(cnf_transformation,[],[f16])).
% 11.85/1.99  
% 11.85/1.99  fof(f17,axiom,(
% 11.85/1.99    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 11.85/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.85/1.99  
% 11.85/1.99  fof(f43,plain,(
% 11.85/1.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 11.85/1.99    inference(cnf_transformation,[],[f17])).
% 11.85/1.99  
% 11.85/1.99  fof(f47,plain,(
% 11.85/1.99    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 11.85/1.99    inference(definition_unfolding,[],[f42,f43])).
% 11.85/1.99  
% 11.85/1.99  fof(f48,plain,(
% 11.85/1.99    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 11.85/1.99    inference(definition_unfolding,[],[f41,f47])).
% 11.85/1.99  
% 11.85/1.99  fof(f49,plain,(
% 11.85/1.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 11.85/1.99    inference(definition_unfolding,[],[f40,f48])).
% 11.85/1.99  
% 11.85/1.99  fof(f50,plain,(
% 11.85/1.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 11.85/1.99    inference(definition_unfolding,[],[f39,f49])).
% 11.85/1.99  
% 11.85/1.99  fof(f51,plain,(
% 11.85/1.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 11.85/1.99    inference(definition_unfolding,[],[f38,f50])).
% 11.85/1.99  
% 11.85/1.99  fof(f52,plain,(
% 11.85/1.99    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 11.85/1.99    inference(definition_unfolding,[],[f37,f51])).
% 11.85/1.99  
% 11.85/1.99  fof(f59,plain,(
% 11.85/1.99    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 11.85/1.99    inference(definition_unfolding,[],[f45,f36,f52,f52,f52])).
% 11.85/1.99  
% 11.85/1.99  fof(f4,axiom,(
% 11.85/1.99    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 11.85/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.85/1.99  
% 11.85/1.99  fof(f30,plain,(
% 11.85/1.99    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 11.85/1.99    inference(cnf_transformation,[],[f4])).
% 11.85/1.99  
% 11.85/1.99  fof(f56,plain,(
% 11.85/1.99    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) )),
% 11.85/1.99    inference(definition_unfolding,[],[f30,f33])).
% 11.85/1.99  
% 11.85/1.99  fof(f18,axiom,(
% 11.85/1.99    ! [X0,X1] : (r1_tarski(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 11.85/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.85/1.99  
% 11.85/1.99  fof(f23,plain,(
% 11.85/1.99    ! [X0,X1] : (X0 = X1 | ~r1_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 11.85/1.99    inference(ennf_transformation,[],[f18])).
% 11.85/1.99  
% 11.85/1.99  fof(f44,plain,(
% 11.85/1.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(k1_tarski(X0),k1_tarski(X1))) )),
% 11.85/1.99    inference(cnf_transformation,[],[f23])).
% 11.85/1.99  
% 11.85/1.99  fof(f58,plain,(
% 11.85/1.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) )),
% 11.85/1.99    inference(definition_unfolding,[],[f44,f52,f52])).
% 11.85/1.99  
% 11.85/1.99  fof(f46,plain,(
% 11.85/1.99    sK0 != sK1),
% 11.85/1.99    inference(cnf_transformation,[],[f26])).
% 11.85/1.99  
% 11.85/1.99  cnf(c_1,plain,
% 11.85/1.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 11.85/1.99      inference(cnf_transformation,[],[f54]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_2,plain,
% 11.85/1.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
% 11.85/1.99      inference(cnf_transformation,[],[f55]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_0,plain,
% 11.85/1.99      ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 11.85/1.99      inference(cnf_transformation,[],[f53]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_518,plain,
% 11.85/1.99      ( k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0) ),
% 11.85/1.99      inference(superposition,[status(thm)],[c_2,c_0]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_7,plain,
% 11.85/1.99      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 11.85/1.99      inference(cnf_transformation,[],[f35]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_614,plain,
% 11.85/1.99      ( k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k5_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 11.85/1.99      inference(superposition,[status(thm)],[c_0,c_7]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_3662,plain,
% 11.85/1.99      ( k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 11.85/1.99      inference(superposition,[status(thm)],[c_518,c_614]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_6,plain,
% 11.85/1.99      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 11.85/1.99      inference(cnf_transformation,[],[f34]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_615,plain,
% 11.85/1.99      ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X1)) = k5_xboole_0(X0,X1) ),
% 11.85/1.99      inference(superposition,[status(thm)],[c_6,c_7]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_1394,plain,
% 11.85/1.99      ( k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))) = k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X1)) ),
% 11.85/1.99      inference(superposition,[status(thm)],[c_0,c_615]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_5,plain,
% 11.85/1.99      ( r1_tarski(k1_xboole_0,X0) ),
% 11.85/1.99      inference(cnf_transformation,[],[f32]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_183,plain,
% 11.85/1.99      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 11.85/1.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_4,plain,
% 11.85/1.99      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 11.85/1.99      inference(cnf_transformation,[],[f57]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_184,plain,
% 11.85/1.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
% 11.85/1.99      | r1_tarski(X0,X1) != iProver_top ),
% 11.85/1.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_1190,plain,
% 11.85/1.99      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
% 11.85/1.99      inference(superposition,[status(thm)],[c_183,c_184]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_1412,plain,
% 11.85/1.99      ( k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X1)) = X0 ),
% 11.85/1.99      inference(demodulation,[status(thm)],[c_1394,c_6,c_1190]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_2118,plain,
% 11.85/1.99      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 11.85/1.99      inference(superposition,[status(thm)],[c_1412,c_0]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_2242,plain,
% 11.85/1.99      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 11.85/1.99      inference(superposition,[status(thm)],[c_2118,c_1]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_2290,plain,
% 11.85/1.99      ( k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
% 11.85/1.99      inference(superposition,[status(thm)],[c_2242,c_0]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_2302,plain,
% 11.85/1.99      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 11.85/1.99      inference(light_normalisation,[status(thm)],[c_2290,c_6]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_2304,plain,
% 11.85/1.99      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 11.85/1.99      inference(demodulation,[status(thm)],[c_2302,c_2242]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_3720,plain,
% 11.85/1.99      ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
% 11.85/1.99      inference(demodulation,[status(thm)],[c_3662,c_6,c_2304]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_3736,plain,
% 11.85/1.99      ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = X0 ),
% 11.85/1.99      inference(superposition,[status(thm)],[c_1,c_3720]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_10,negated_conjecture,
% 11.85/1.99      ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
% 11.85/1.99      inference(cnf_transformation,[],[f59]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_616,plain,
% 11.85/1.99      ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),X0)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0) ),
% 11.85/1.99      inference(superposition,[status(thm)],[c_10,c_7]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_707,plain,
% 11.85/1.99      ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),X0))) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),X0)) ),
% 11.85/1.99      inference(superposition,[status(thm)],[c_0,c_616]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_931,plain,
% 11.85/1.99      ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),X0)) ),
% 11.85/1.99      inference(superposition,[status(thm)],[c_1,c_707]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_5330,plain,
% 11.85/1.99      ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) ),
% 11.85/1.99      inference(superposition,[status(thm)],[c_1,c_931]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_603,plain,
% 11.85/1.99      ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 11.85/1.99      inference(superposition,[status(thm)],[c_1,c_0]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_703,plain,
% 11.85/1.99      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k4_xboole_0(X0,X0),X1) ),
% 11.85/1.99      inference(superposition,[status(thm)],[c_518,c_7]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_3193,plain,
% 11.85/1.99      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
% 11.85/1.99      inference(light_normalisation,[status(thm)],[c_703,c_703,c_2304]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_3214,plain,
% 11.85/1.99      ( k5_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 11.85/1.99      inference(superposition,[status(thm)],[c_603,c_3193]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_3528,plain,
% 11.85/1.99      ( k5_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(X0,X1) ),
% 11.85/1.99      inference(light_normalisation,[status(thm)],[c_3214,c_0]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_3964,plain,
% 11.85/1.99      ( k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1)))) = k5_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 11.85/1.99      inference(superposition,[status(thm)],[c_3528,c_615]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_5355,plain,
% 11.85/1.99      ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
% 11.85/1.99      inference(demodulation,[status(thm)],[c_5330,c_10,c_3964]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_710,plain,
% 11.85/1.99      ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),X0),X1)) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0),X1) ),
% 11.85/1.99      inference(superposition,[status(thm)],[c_616,c_7]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_807,plain,
% 11.85/1.99      ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(X0,X1))) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0),X1) ),
% 11.85/1.99      inference(superposition,[status(thm)],[c_7,c_710]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_817,plain,
% 11.85/1.99      ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(X0,X1)) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0),X1) ),
% 11.85/1.99      inference(demodulation,[status(thm)],[c_807,c_616]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_6271,plain,
% 11.85/1.99      ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k4_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),X0)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0) ),
% 11.85/1.99      inference(superposition,[status(thm)],[c_5355,c_817]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_6417,plain,
% 11.85/1.99      ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) ),
% 11.85/1.99      inference(superposition,[status(thm)],[c_3736,c_6271]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_6453,plain,
% 11.85/1.99      ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
% 11.85/1.99      inference(light_normalisation,[status(thm)],[c_6417,c_10]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_704,plain,
% 11.85/1.99      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) = k4_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
% 11.85/1.99      inference(superposition,[status(thm)],[c_518,c_7]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_5591,plain,
% 11.85/1.99      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) = k1_xboole_0 ),
% 11.85/1.99      inference(demodulation,[status(thm)],[c_704,c_2304]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_5614,plain,
% 11.85/1.99      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X1,X2)))) = k1_xboole_0 ),
% 11.85/1.99      inference(superposition,[status(thm)],[c_7,c_5591]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_6074,plain,
% 11.85/1.99      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),X0),k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X1)))) = k1_xboole_0 ),
% 11.85/1.99      inference(superposition,[status(thm)],[c_518,c_5614]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_6195,plain,
% 11.85/1.99      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),X0),X1) = k1_xboole_0 ),
% 11.85/1.99      inference(demodulation,[status(thm)],[c_6074,c_6,c_2304]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_7917,plain,
% 11.85/1.99      ( k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))) = k1_xboole_0 ),
% 11.85/1.99      inference(superposition,[status(thm)],[c_6453,c_6195]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_909,plain,
% 11.85/1.99      ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(X0,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0))) = k4_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0)) ),
% 11.85/1.99      inference(superposition,[status(thm)],[c_817,c_518]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_2476,plain,
% 11.85/1.99      ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(X0,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0))) = k1_xboole_0 ),
% 11.85/1.99      inference(demodulation,[status(thm)],[c_909,c_2304]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_519,plain,
% 11.85/1.99      ( k5_xboole_0(X0,k4_xboole_0(X0,X0)) = k4_xboole_0(X0,k4_xboole_0(X0,X0)) ),
% 11.85/1.99      inference(superposition,[status(thm)],[c_2,c_0]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_520,plain,
% 11.85/1.99      ( k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
% 11.85/1.99      inference(light_normalisation,[status(thm)],[c_519,c_2]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_819,plain,
% 11.85/1.99      ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),X0),X1)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(X0,X1)) ),
% 11.85/1.99      inference(demodulation,[status(thm)],[c_817,c_710]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_1507,plain,
% 11.85/1.99      ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),X0),k5_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),X0)))) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),X0)) ),
% 11.85/1.99      inference(superposition,[status(thm)],[c_520,c_819]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_1520,plain,
% 11.85/1.99      ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),X0),k5_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),X0)))) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0) ),
% 11.85/1.99      inference(light_normalisation,[status(thm)],[c_1507,c_616]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_1538,plain,
% 11.85/1.99      ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(k4_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),k4_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))))) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) ),
% 11.85/1.99      inference(superposition,[status(thm)],[c_518,c_1520]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_1557,plain,
% 11.85/1.99      ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(k4_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),k4_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))))) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
% 11.85/1.99      inference(light_normalisation,[status(thm)],[c_1538,c_10]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_1655,plain,
% 11.85/1.99      ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(k4_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),k4_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))),X0)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0) ),
% 11.85/1.99      inference(superposition,[status(thm)],[c_1557,c_7]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_2516,plain,
% 11.85/1.99      ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(k4_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),k4_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))))) = k1_xboole_0 ),
% 11.85/1.99      inference(superposition,[status(thm)],[c_2476,c_1655]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_2517,plain,
% 11.85/1.99      ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = k1_xboole_0 ),
% 11.85/1.99      inference(light_normalisation,[status(thm)],[c_2516,c_1557]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_7948,plain,
% 11.85/1.99      ( k5_xboole_0(k1_xboole_0,k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))) = k1_xboole_0 ),
% 11.85/1.99      inference(light_normalisation,[status(thm)],[c_7917,c_2517]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_3212,plain,
% 11.85/1.99      ( k5_xboole_0(X0,k4_xboole_0(X0,X0)) = k5_xboole_0(k1_xboole_0,X0) ),
% 11.85/1.99      inference(superposition,[status(thm)],[c_518,c_3193]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_3310,plain,
% 11.85/1.99      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 11.85/1.99      inference(light_normalisation,[status(thm)],[c_3212,c_520]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_3952,plain,
% 11.85/1.99      ( k5_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(X0,X1) ),
% 11.85/1.99      inference(superposition,[status(thm)],[c_1,c_3528]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_6094,plain,
% 11.85/1.99      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X1,k5_xboole_0(X0,k4_xboole_0(X1,X1)))) = k1_xboole_0 ),
% 11.85/1.99      inference(superposition,[status(thm)],[c_518,c_5614]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_6178,plain,
% 11.85/1.99      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X1,X0)) = k1_xboole_0 ),
% 11.85/1.99      inference(demodulation,[status(thm)],[c_6094,c_6,c_2304]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_7430,plain,
% 11.85/1.99      ( k5_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),k1_xboole_0)) = k1_xboole_0 ),
% 11.85/1.99      inference(superposition,[status(thm)],[c_3528,c_6178]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_605,plain,
% 11.85/1.99      ( k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
% 11.85/1.99      inference(superposition,[status(thm)],[c_1,c_0]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_3138,plain,
% 11.85/1.99      ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 11.85/1.99      inference(superposition,[status(thm)],[c_1,c_605]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_7577,plain,
% 11.85/1.99      ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
% 11.85/1.99      inference(demodulation,[status(thm)],[c_7430,c_6,c_3138]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_7653,plain,
% 11.85/1.99      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) ),
% 11.85/1.99      inference(superposition,[status(thm)],[c_7577,c_1]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_7661,plain,
% 11.85/1.99      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 11.85/1.99      inference(demodulation,[status(thm)],[c_7653,c_2302]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_7949,plain,
% 11.85/1.99      ( k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = k1_xboole_0 ),
% 11.85/1.99      inference(demodulation,[status(thm)],[c_7948,c_3310,c_3952,c_7661]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_3,plain,
% 11.85/1.99      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
% 11.85/1.99      inference(cnf_transformation,[],[f56]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_185,plain,
% 11.85/1.99      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = iProver_top ),
% 11.85/1.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_606,plain,
% 11.85/1.99      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = iProver_top ),
% 11.85/1.99      inference(superposition,[status(thm)],[c_1,c_185]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_23036,plain,
% 11.85/1.99      ( r1_tarski(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k1_xboole_0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = iProver_top ),
% 11.85/1.99      inference(superposition,[status(thm)],[c_7949,c_606]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_23073,plain,
% 11.85/1.99      ( r1_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = iProver_top ),
% 11.85/1.99      inference(demodulation,[status(thm)],[c_23036,c_2302]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_8,plain,
% 11.85/1.99      ( ~ r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
% 11.85/1.99      | X1 = X0 ),
% 11.85/1.99      inference(cnf_transformation,[],[f58]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_190,plain,
% 11.85/1.99      ( ~ r1_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
% 11.85/1.99      | sK0 = sK1 ),
% 11.85/1.99      inference(instantiation,[status(thm)],[c_8]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_191,plain,
% 11.85/1.99      ( sK0 = sK1
% 11.85/1.99      | r1_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) != iProver_top ),
% 11.85/1.99      inference(predicate_to_equality,[status(thm)],[c_190]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_9,negated_conjecture,
% 11.85/1.99      ( sK0 != sK1 ),
% 11.85/1.99      inference(cnf_transformation,[],[f46]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(contradiction,plain,
% 11.85/1.99      ( $false ),
% 11.85/1.99      inference(minisat,[status(thm)],[c_23073,c_191,c_9]) ).
% 11.85/1.99  
% 11.85/1.99  
% 11.85/1.99  % SZS output end CNFRefutation for theBenchmark.p
% 11.85/1.99  
% 11.85/1.99  ------                               Statistics
% 11.85/1.99  
% 11.85/1.99  ------ General
% 11.85/1.99  
% 11.85/1.99  abstr_ref_over_cycles:                  0
% 11.85/1.99  abstr_ref_under_cycles:                 0
% 11.85/1.99  gc_basic_clause_elim:                   0
% 11.85/1.99  forced_gc_time:                         0
% 11.85/1.99  parsing_time:                           0.008
% 11.85/1.99  unif_index_cands_time:                  0.
% 11.85/1.99  unif_index_add_time:                    0.
% 11.85/1.99  orderings_time:                         0.
% 11.85/1.99  out_proof_time:                         0.01
% 11.85/1.99  total_time:                             1.176
% 11.85/1.99  num_of_symbols:                         40
% 11.85/1.99  num_of_terms:                           57081
% 11.85/1.99  
% 11.85/1.99  ------ Preprocessing
% 11.85/1.99  
% 11.85/1.99  num_of_splits:                          0
% 11.85/1.99  num_of_split_atoms:                     2
% 11.85/1.99  num_of_reused_defs:                     0
% 11.85/1.99  num_eq_ax_congr_red:                    0
% 11.85/1.99  num_of_sem_filtered_clauses:            1
% 11.85/1.99  num_of_subtypes:                        0
% 11.85/1.99  monotx_restored_types:                  0
% 11.85/1.99  sat_num_of_epr_types:                   0
% 11.85/1.99  sat_num_of_non_cyclic_types:            0
% 11.85/1.99  sat_guarded_non_collapsed_types:        0
% 11.85/1.99  num_pure_diseq_elim:                    0
% 11.85/1.99  simp_replaced_by:                       0
% 11.85/1.99  res_preprocessed:                       46
% 11.85/1.99  prep_upred:                             0
% 11.85/1.99  prep_unflattend:                        6
% 11.85/1.99  smt_new_axioms:                         0
% 11.85/1.99  pred_elim_cands:                        1
% 11.85/1.99  pred_elim:                              0
% 11.85/1.99  pred_elim_cl:                           0
% 11.85/1.99  pred_elim_cycles:                       1
% 11.85/1.99  merged_defs:                            0
% 11.85/1.99  merged_defs_ncl:                        0
% 11.85/1.99  bin_hyper_res:                          0
% 11.85/1.99  prep_cycles:                            3
% 11.85/1.99  pred_elim_time:                         0.
% 11.85/1.99  splitting_time:                         0.
% 11.85/1.99  sem_filter_time:                        0.
% 11.85/1.99  monotx_time:                            0.
% 11.85/1.99  subtype_inf_time:                       0.
% 11.85/1.99  
% 11.85/1.99  ------ Problem properties
% 11.85/1.99  
% 11.85/1.99  clauses:                                11
% 11.85/1.99  conjectures:                            2
% 11.85/1.99  epr:                                    2
% 11.85/1.99  horn:                                   11
% 11.85/1.99  ground:                                 2
% 11.85/1.99  unary:                                  9
% 11.85/1.99  binary:                                 2
% 11.85/1.99  lits:                                   13
% 11.85/1.99  lits_eq:                                9
% 11.85/1.99  fd_pure:                                0
% 11.85/1.99  fd_pseudo:                              0
% 11.85/1.99  fd_cond:                                0
% 11.85/1.99  fd_pseudo_cond:                         1
% 11.85/1.99  ac_symbols:                             0
% 11.85/1.99  
% 11.85/1.99  ------ Propositional Solver
% 11.85/1.99  
% 11.85/1.99  prop_solver_calls:                      29
% 11.85/1.99  prop_fast_solver_calls:                 472
% 11.85/1.99  smt_solver_calls:                       0
% 11.85/1.99  smt_fast_solver_calls:                  0
% 11.85/1.99  prop_num_of_clauses:                    7460
% 11.85/1.99  prop_preprocess_simplified:             9138
% 11.85/1.99  prop_fo_subsumed:                       0
% 11.85/1.99  prop_solver_time:                       0.
% 11.85/1.99  smt_solver_time:                        0.
% 11.85/1.99  smt_fast_solver_time:                   0.
% 11.85/1.99  prop_fast_solver_time:                  0.
% 11.85/1.99  prop_unsat_core_time:                   0.
% 11.85/1.99  
% 11.85/1.99  ------ QBF
% 11.85/1.99  
% 11.85/1.99  qbf_q_res:                              0
% 11.85/1.99  qbf_num_tautologies:                    0
% 11.85/1.99  qbf_prep_cycles:                        0
% 11.85/1.99  
% 11.85/1.99  ------ BMC1
% 11.85/1.99  
% 11.85/1.99  bmc1_current_bound:                     -1
% 11.85/1.99  bmc1_last_solved_bound:                 -1
% 11.85/1.99  bmc1_unsat_core_size:                   -1
% 11.85/1.99  bmc1_unsat_core_parents_size:           -1
% 11.85/1.99  bmc1_merge_next_fun:                    0
% 11.85/1.99  bmc1_unsat_core_clauses_time:           0.
% 11.85/1.99  
% 11.85/1.99  ------ Instantiation
% 11.85/1.99  
% 11.85/1.99  inst_num_of_clauses:                    2024
% 11.85/1.99  inst_num_in_passive:                    724
% 11.85/1.99  inst_num_in_active:                     630
% 11.85/1.99  inst_num_in_unprocessed:                670
% 11.85/1.99  inst_num_of_loops:                      660
% 11.85/1.99  inst_num_of_learning_restarts:          0
% 11.85/1.99  inst_num_moves_active_passive:          26
% 11.85/1.99  inst_lit_activity:                      0
% 11.85/1.99  inst_lit_activity_moves:                0
% 11.85/1.99  inst_num_tautologies:                   0
% 11.85/1.99  inst_num_prop_implied:                  0
% 11.85/1.99  inst_num_existing_simplified:           0
% 11.85/1.99  inst_num_eq_res_simplified:             0
% 11.85/1.99  inst_num_child_elim:                    0
% 11.85/1.99  inst_num_of_dismatching_blockings:      449
% 11.85/1.99  inst_num_of_non_proper_insts:           2665
% 11.85/1.99  inst_num_of_duplicates:                 0
% 11.85/1.99  inst_inst_num_from_inst_to_res:         0
% 11.85/1.99  inst_dismatching_checking_time:         0.
% 11.85/1.99  
% 11.85/1.99  ------ Resolution
% 11.85/1.99  
% 11.85/1.99  res_num_of_clauses:                     0
% 11.85/1.99  res_num_in_passive:                     0
% 11.85/1.99  res_num_in_active:                      0
% 11.85/1.99  res_num_of_loops:                       49
% 11.85/1.99  res_forward_subset_subsumed:            297
% 11.85/1.99  res_backward_subset_subsumed:           0
% 11.85/1.99  res_forward_subsumed:                   0
% 11.85/1.99  res_backward_subsumed:                  0
% 11.85/1.99  res_forward_subsumption_resolution:     0
% 11.85/1.99  res_backward_subsumption_resolution:    0
% 11.85/1.99  res_clause_to_clause_subsumption:       18020
% 11.85/1.99  res_orphan_elimination:                 0
% 11.85/1.99  res_tautology_del:                      141
% 11.85/1.99  res_num_eq_res_simplified:              0
% 11.85/1.99  res_num_sel_changes:                    0
% 11.85/1.99  res_moves_from_active_to_pass:          0
% 11.85/1.99  
% 11.85/1.99  ------ Superposition
% 11.85/1.99  
% 11.85/1.99  sup_time_total:                         0.
% 11.85/1.99  sup_time_generating:                    0.
% 11.85/1.99  sup_time_sim_full:                      0.
% 11.85/1.99  sup_time_sim_immed:                     0.
% 11.85/1.99  
% 11.85/1.99  sup_num_of_clauses:                     1810
% 11.85/1.99  sup_num_in_active:                      85
% 11.85/1.99  sup_num_in_passive:                     1725
% 11.85/1.99  sup_num_of_loops:                       130
% 11.85/1.99  sup_fw_superposition:                   3271
% 11.85/1.99  sup_bw_superposition:                   2110
% 11.85/1.99  sup_immediate_simplified:               3727
% 11.85/1.99  sup_given_eliminated:                   14
% 11.85/1.99  comparisons_done:                       0
% 11.85/1.99  comparisons_avoided:                    0
% 11.85/1.99  
% 11.85/1.99  ------ Simplifications
% 11.85/1.99  
% 11.85/1.99  
% 11.85/1.99  sim_fw_subset_subsumed:                 0
% 11.85/1.99  sim_bw_subset_subsumed:                 0
% 11.85/1.99  sim_fw_subsumed:                        169
% 11.85/1.99  sim_bw_subsumed:                        124
% 11.85/1.99  sim_fw_subsumption_res:                 0
% 11.85/1.99  sim_bw_subsumption_res:                 0
% 11.85/1.99  sim_tautology_del:                      0
% 11.85/1.99  sim_eq_tautology_del:                   1688
% 11.85/1.99  sim_eq_res_simp:                        0
% 11.85/1.99  sim_fw_demodulated:                     6765
% 11.85/1.99  sim_bw_demodulated:                     386
% 11.85/1.99  sim_light_normalised:                   1897
% 11.85/1.99  sim_joinable_taut:                      0
% 11.85/1.99  sim_joinable_simp:                      0
% 11.85/1.99  sim_ac_normalised:                      0
% 11.85/1.99  sim_smt_subsumption:                    0
% 11.85/1.99  
%------------------------------------------------------------------------------
