%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:23:52 EST 2020

% Result     : Theorem 35.47s
% Output     : CNFRefutation 35.47s
% Verified   : 
% Statistics : Number of formulae       :  273 (123725 expanded)
%              Number of clauses        :  230 (45337 expanded)
%              Number of leaves         :   17 (30120 expanded)
%              Depth                    :   38
%              Number of atoms          :  321 (221365 expanded)
%              Number of equality atoms :  281 (150589 expanded)
%              Maximal formula depth    :    9 (   2 average)
%              Maximal clause size      :    8 (   1 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X3,X1)
          & r1_xboole_0(X2,X0)
          & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
       => X1 = X2 ) ),
    inference(negated_conjecture,[],[f15])).

fof(f22,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f23,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(flattening,[],[f22])).

fof(f24,plain,
    ( ? [X0,X1,X2,X3] :
        ( X1 != X2
        & r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
   => ( sK1 != sK2
      & r1_xboole_0(sK3,sK1)
      & r1_xboole_0(sK2,sK0)
      & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( sK1 != sK2
    & r1_xboole_0(sK3,sK1)
    & r1_xboole_0(sK2,sK0)
    & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f24])).

fof(f40,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f25])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f27,f36])).

fof(f41,plain,(
    r1_xboole_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f10,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f45,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f35,f36])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f12,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f46,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(definition_unfolding,[],[f39,f36])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f42,plain,(
    r1_xboole_0(sK3,sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f43,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_16,negated_conjecture,
    ( k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_11,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_198,negated_conjecture,
    ( k2_xboole_0(sK1,sK0) = k2_xboole_0(sK2,sK3) ),
    inference(theory_normalisation,[status(thm)],[c_16,c_11,c_0])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_15,negated_conjecture,
    ( r1_xboole_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_133,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
    | sK0 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_15])).

cnf(c_134,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_133])).

cnf(c_9,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_722,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k1_xboole_0)) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) ),
    inference(superposition,[status(thm)],[c_134,c_9])).

cnf(c_731,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k1_xboole_0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_722,c_134])).

cnf(c_4,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_732,plain,
    ( k4_xboole_0(sK2,sK2) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_731,c_4])).

cnf(c_6,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_1341,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(sK2,X0)) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_732,c_6])).

cnf(c_10,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_1347,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(sK2,X0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1341,c_10])).

cnf(c_2460,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(sK1,sK0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_198,c_1347])).

cnf(c_2582,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(k2_xboole_0(sK1,sK0),X0)) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_2460,c_6])).

cnf(c_2587,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(k2_xboole_0(sK1,sK0),X0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2582,c_10])).

cnf(c_12,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_5,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_607,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = k2_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_5,c_4])).

cnf(c_608,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_607,c_4])).

cnf(c_1328,plain,
    ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_608,c_0])).

cnf(c_2011,plain,
    ( k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_1328,c_5])).

cnf(c_2016,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2011,c_10])).

cnf(c_2417,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_2016,c_6])).

cnf(c_2429,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2417,c_10])).

cnf(c_3218,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_12,c_2429])).

cnf(c_33572,plain,
    ( k4_xboole_0(k4_xboole_0(X0,sK2),k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2587,c_3218])).

cnf(c_33668,plain,
    ( k4_xboole_0(k4_xboole_0(X0,sK2),X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_33572,c_4])).

cnf(c_1215,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X2),k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1))) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,X1)) ),
    inference(superposition,[status(thm)],[c_5,c_12])).

cnf(c_115691,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,sK2),X0),X1),k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,sK2),X0),k1_xboole_0)) = k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,sK2),X0),k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_33668,c_1215])).

cnf(c_3,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_352,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_353,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1719,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(superposition,[status(thm)],[c_352,c_353])).

cnf(c_2421,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k1_xboole_0)) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_2016,c_12])).

cnf(c_2428,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_2421,c_4,c_1719])).

cnf(c_1199,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,X1)) ),
    inference(superposition,[status(thm)],[c_4,c_12])).

cnf(c_1256,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
    inference(demodulation,[status(thm)],[c_1199,c_4,c_10])).

cnf(c_7057,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(superposition,[status(thm)],[c_9,c_1256])).

cnf(c_360,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,k2_xboole_0(X2,X0)) ),
    inference(superposition,[status(thm)],[c_11,c_0])).

cnf(c_7190,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X0)) = k2_xboole_0(X2,X0) ),
    inference(superposition,[status(thm)],[c_7057,c_360])).

cnf(c_116108,plain,
    ( k2_xboole_0(k4_xboole_0(X0,sK2),X0) = X0 ),
    inference(demodulation,[status(thm)],[c_115691,c_4,c_1719,c_2428,c_7190])).

cnf(c_604,plain,
    ( k4_xboole_0(k2_xboole_0(sK1,sK0),sK3) = k4_xboole_0(sK2,sK3) ),
    inference(superposition,[status(thm)],[c_198,c_5])).

cnf(c_812,plain,
    ( k4_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK3,X0)) = k4_xboole_0(k4_xboole_0(sK2,sK3),X0) ),
    inference(superposition,[status(thm)],[c_604,c_6])).

cnf(c_815,plain,
    ( k4_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK3,X0)) = k4_xboole_0(sK2,k2_xboole_0(sK3,X0)) ),
    inference(demodulation,[status(thm)],[c_812,c_6])).

cnf(c_14,negated_conjecture,
    ( r1_xboole_0(sK3,sK1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_128,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
    | sK3 != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_14])).

cnf(c_129,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_128])).

cnf(c_715,plain,
    ( k4_xboole_0(sK3,k1_xboole_0) = k4_xboole_0(sK3,sK1) ),
    inference(superposition,[status(thm)],[c_129,c_9])).

cnf(c_742,plain,
    ( k4_xboole_0(sK3,sK1) = sK3 ),
    inference(demodulation,[status(thm)],[c_715,c_4])).

cnf(c_2585,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(X0,k2_xboole_0(sK1,sK0))) = k2_xboole_0(k4_xboole_0(sK2,X0),k4_xboole_0(sK2,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_2460,c_12])).

cnf(c_1212,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(X0,sK0)) = k2_xboole_0(k4_xboole_0(sK2,X0),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_134,c_12])).

cnf(c_1240,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(X0,sK0)) = k4_xboole_0(sK2,X0) ),
    inference(demodulation,[status(thm)],[c_1212,c_608])).

cnf(c_2132,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(X0,k2_xboole_0(X1,sK0))) = k4_xboole_0(sK2,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_6,c_1240])).

cnf(c_2586,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(X0,sK1)) = sK2 ),
    inference(demodulation,[status(thm)],[c_2585,c_4,c_1719,c_2132])).

cnf(c_2786,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(k4_xboole_0(X0,sK1),X1)) = k4_xboole_0(sK2,X1) ),
    inference(superposition,[status(thm)],[c_2586,c_6])).

cnf(c_28255,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(sK3,X0)) = k4_xboole_0(sK2,X0) ),
    inference(superposition,[status(thm)],[c_742,c_2786])).

cnf(c_33122,plain,
    ( k4_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK3,X0)) = k4_xboole_0(sK2,X0) ),
    inference(light_normalisation,[status(thm)],[c_815,c_815,c_28255])).

cnf(c_718,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1))) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(superposition,[status(thm)],[c_5,c_9])).

cnf(c_739,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_718,c_5])).

cnf(c_33154,plain,
    ( k4_xboole_0(k2_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK3,X0)),k4_xboole_0(k2_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK3,X0)),k4_xboole_0(sK2,X0))) = k4_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK3,X0)) ),
    inference(superposition,[status(thm)],[c_33122,c_739])).

cnf(c_33214,plain,
    ( k4_xboole_0(k2_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK3,X0)),k4_xboole_0(k2_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK3,X0)),k4_xboole_0(sK2,X0))) = k4_xboole_0(sK2,X0) ),
    inference(demodulation,[status(thm)],[c_33154,c_33122])).

cnf(c_8,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X2))
    | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_350,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X2)) = iProver_top
    | r1_tarski(k4_xboole_0(X0,X1),X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_585,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_352,c_350])).

cnf(c_5778,plain,
    ( r1_tarski(sK3,k2_xboole_0(sK1,sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_198,c_585])).

cnf(c_6300,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(sK1,sK0)) = k2_xboole_0(sK1,sK0) ),
    inference(superposition,[status(thm)],[c_5778,c_353])).

cnf(c_359,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X2,k2_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_11,c_0])).

cnf(c_3007,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(sK2,X0)) = k2_xboole_0(X0,k2_xboole_0(sK1,sK0)) ),
    inference(superposition,[status(thm)],[c_198,c_359])).

cnf(c_3542,plain,
    ( k2_xboole_0(k2_xboole_0(sK2,X0),k2_xboole_0(sK3,X1)) = k2_xboole_0(X1,k2_xboole_0(X0,k2_xboole_0(sK1,sK0))) ),
    inference(superposition,[status(thm)],[c_3007,c_359])).

cnf(c_6428,plain,
    ( k2_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK3,X0)) = k2_xboole_0(X0,k2_xboole_0(sK1,sK0)) ),
    inference(superposition,[status(thm)],[c_6300,c_3542])).

cnf(c_6444,plain,
    ( k2_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK3,X0)) = k2_xboole_0(X0,k2_xboole_0(sK1,sK0)) ),
    inference(light_normalisation,[status(thm)],[c_6428,c_198])).

cnf(c_33215,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK1,sK0)),k4_xboole_0(sK2,X0))) = k4_xboole_0(sK2,X0) ),
    inference(light_normalisation,[status(thm)],[c_33214,c_6444])).

cnf(c_118363,plain,
    ( k4_xboole_0(k2_xboole_0(sK1,sK0),k4_xboole_0(k2_xboole_0(sK1,sK0),k4_xboole_0(sK2,k4_xboole_0(k2_xboole_0(sK1,sK0),sK2)))) = k4_xboole_0(sK2,k4_xboole_0(k2_xboole_0(sK1,sK0),sK2)) ),
    inference(superposition,[status(thm)],[c_116108,c_33215])).

cnf(c_3541,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK1,sK0)),k2_xboole_0(sK2,X0)) = k4_xboole_0(sK3,k2_xboole_0(sK2,X0)) ),
    inference(superposition,[status(thm)],[c_3007,c_5])).

cnf(c_3969,plain,
    ( k4_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK2,k1_xboole_0)) = k4_xboole_0(sK3,k2_xboole_0(sK2,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_1328,c_3541])).

cnf(c_3993,plain,
    ( k4_xboole_0(k2_xboole_0(sK1,sK0),sK2) = k4_xboole_0(sK3,sK2) ),
    inference(demodulation,[status(thm)],[c_3969,c_608])).

cnf(c_33135,plain,
    ( k4_xboole_0(k2_xboole_0(sK1,sK0),sK3) = k4_xboole_0(sK2,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_608,c_33122])).

cnf(c_33233,plain,
    ( k4_xboole_0(k2_xboole_0(sK1,sK0),sK3) = sK2 ),
    inference(demodulation,[status(thm)],[c_33135,c_4,c_604])).

cnf(c_1200,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),X2))) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_5,c_12])).

cnf(c_106153,plain,
    ( k2_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(k2_xboole_0(sK1,sK0),sK2)) = k4_xboole_0(k2_xboole_0(sK1,sK0),k4_xboole_0(sK0,sK3)) ),
    inference(superposition,[status(thm)],[c_33233,c_1200])).

cnf(c_106647,plain,
    ( k4_xboole_0(k2_xboole_0(sK1,sK0),k4_xboole_0(sK0,sK3)) = k2_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(sK3,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_106153,c_3993])).

cnf(c_716,plain,
    ( k4_xboole_0(sK2,k1_xboole_0) = k4_xboole_0(sK2,sK0) ),
    inference(superposition,[status(thm)],[c_134,c_9])).

cnf(c_741,plain,
    ( k4_xboole_0(sK2,sK0) = sK2 ),
    inference(demodulation,[status(thm)],[c_716,c_4])).

cnf(c_721,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,k1_xboole_0)) = k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)) ),
    inference(superposition,[status(thm)],[c_129,c_9])).

cnf(c_733,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,k1_xboole_0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_721,c_129])).

cnf(c_734,plain,
    ( k4_xboole_0(sK3,sK3) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_733,c_4])).

cnf(c_1869,plain,
    ( k4_xboole_0(sK3,k2_xboole_0(sK3,X0)) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_734,c_6])).

cnf(c_1875,plain,
    ( k4_xboole_0(sK3,k2_xboole_0(sK3,X0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1869,c_10])).

cnf(c_2486,plain,
    ( k4_xboole_0(sK3,k2_xboole_0(X0,sK3)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_1875])).

cnf(c_3385,plain,
    ( k4_xboole_0(sK3,k2_xboole_0(sK1,sK0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_198,c_2486])).

cnf(c_3511,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(X0,k2_xboole_0(sK1,sK0))) = k2_xboole_0(k4_xboole_0(sK3,X0),k4_xboole_0(sK3,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_3385,c_12])).

cnf(c_1211,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(X0,sK1)) = k2_xboole_0(k4_xboole_0(sK3,X0),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_129,c_12])).

cnf(c_1241,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(X0,sK1)) = k4_xboole_0(sK3,X0) ),
    inference(demodulation,[status(thm)],[c_1211,c_608])).

cnf(c_2257,plain,
    ( k2_xboole_0(k4_xboole_0(sK3,X0),k4_xboole_0(sK3,k4_xboole_0(sK3,X1))) = k4_xboole_0(sK3,k4_xboole_0(k4_xboole_0(X0,sK1),X1)) ),
    inference(superposition,[status(thm)],[c_1241,c_12])).

cnf(c_2268,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(X0,k2_xboole_0(sK1,X1))) = k4_xboole_0(sK3,k4_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_2257,c_6,c_12])).

cnf(c_3513,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(X0,sK0)) = sK3 ),
    inference(demodulation,[status(thm)],[c_3511,c_4,c_1719,c_2268])).

cnf(c_4608,plain,
    ( k4_xboole_0(sK3,sK2) = sK3 ),
    inference(superposition,[status(thm)],[c_741,c_3513])).

cnf(c_1221,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(sK1,sK0),X0),k4_xboole_0(k2_xboole_0(sK1,sK0),k4_xboole_0(sK2,sK3))) = k4_xboole_0(k2_xboole_0(sK1,sK0),k4_xboole_0(X0,sK3)) ),
    inference(superposition,[status(thm)],[c_604,c_12])).

cnf(c_33176,plain,
    ( k2_xboole_0(k4_xboole_0(sK2,X0),k4_xboole_0(k2_xboole_0(sK1,sK0),k4_xboole_0(sK2,sK3))) = k4_xboole_0(k2_xboole_0(sK1,sK0),k4_xboole_0(k2_xboole_0(sK3,X0),sK3)) ),
    inference(superposition,[status(thm)],[c_33122,c_1221])).

cnf(c_2782,plain,
    ( k4_xboole_0(sK2,sK3) = sK2 ),
    inference(superposition,[status(thm)],[c_742,c_2586])).

cnf(c_33194,plain,
    ( k4_xboole_0(k2_xboole_0(sK1,sK0),k4_xboole_0(k2_xboole_0(sK3,X0),sK3)) = k2_xboole_0(k4_xboole_0(sK2,X0),k4_xboole_0(sK3,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_33176,c_2782,c_3993])).

cnf(c_602,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_5])).

cnf(c_33195,plain,
    ( k4_xboole_0(k2_xboole_0(sK1,sK0),k4_xboole_0(X0,sK3)) = k2_xboole_0(k4_xboole_0(sK2,X0),sK3) ),
    inference(demodulation,[status(thm)],[c_33194,c_602,c_4608])).

cnf(c_106648,plain,
    ( k2_xboole_0(k4_xboole_0(sK1,sK0),sK3) = k2_xboole_0(sK1,sK0) ),
    inference(demodulation,[status(thm)],[c_106647,c_198,c_741,c_4608,c_33195])).

cnf(c_108890,plain,
    ( k2_xboole_0(sK3,k4_xboole_0(sK1,sK0)) = k2_xboole_0(sK1,sK0) ),
    inference(superposition,[status(thm)],[c_106648,c_0])).

cnf(c_6683,plain,
    ( k2_xboole_0(sK1,k2_xboole_0(sK0,k2_xboole_0(sK3,X0))) = k2_xboole_0(X0,k2_xboole_0(sK1,sK0)) ),
    inference(superposition,[status(thm)],[c_6444,c_11])).

cnf(c_109078,plain,
    ( k2_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(sK1,sK0)) = k2_xboole_0(sK1,k2_xboole_0(sK0,k2_xboole_0(sK1,sK0))) ),
    inference(superposition,[status(thm)],[c_108890,c_6683])).

cnf(c_807,plain,
    ( k2_xboole_0(sK2,k2_xboole_0(sK3,X0)) = k2_xboole_0(k2_xboole_0(sK1,sK0),X0) ),
    inference(superposition,[status(thm)],[c_198,c_11])).

cnf(c_876,plain,
    ( k2_xboole_0(sK1,k2_xboole_0(sK0,X0)) = k2_xboole_0(sK2,k2_xboole_0(sK3,X0)) ),
    inference(superposition,[status(thm)],[c_807,c_11])).

cnf(c_7194,plain,
    ( k2_xboole_0(sK1,k2_xboole_0(sK0,k4_xboole_0(sK3,X0))) = k2_xboole_0(sK2,sK3) ),
    inference(superposition,[status(thm)],[c_7057,c_876])).

cnf(c_7209,plain,
    ( k2_xboole_0(sK1,k2_xboole_0(sK0,k4_xboole_0(sK3,X0))) = k2_xboole_0(sK1,sK0) ),
    inference(light_normalisation,[status(thm)],[c_7194,c_198])).

cnf(c_7579,plain,
    ( k2_xboole_0(k2_xboole_0(sK0,k4_xboole_0(sK3,X0)),k2_xboole_0(sK1,X1)) = k2_xboole_0(X1,k2_xboole_0(sK1,sK0)) ),
    inference(superposition,[status(thm)],[c_7209,c_359])).

cnf(c_358,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_11,c_0])).

cnf(c_3548,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(X0,k2_xboole_0(sK2,X1))) = k2_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(sK1,sK0))) ),
    inference(superposition,[status(thm)],[c_3007,c_358])).

cnf(c_6435,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(X0,k2_xboole_0(sK2,sK3))) = k2_xboole_0(X0,k2_xboole_0(sK1,sK0)) ),
    inference(superposition,[status(thm)],[c_6300,c_3548])).

cnf(c_6438,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(X0,k2_xboole_0(sK1,sK0))) = k2_xboole_0(X0,k2_xboole_0(sK1,sK0)) ),
    inference(light_normalisation,[status(thm)],[c_6435,c_198])).

cnf(c_11301,plain,
    ( k2_xboole_0(k2_xboole_0(sK0,k4_xboole_0(sK3,X0)),k2_xboole_0(sK1,sK0)) = k2_xboole_0(sK3,k2_xboole_0(sK0,k2_xboole_0(sK1,sK0))) ),
    inference(superposition,[status(thm)],[c_7579,c_6438])).

cnf(c_11347,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(sK0,k2_xboole_0(sK1,sK0))) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK0)) ),
    inference(demodulation,[status(thm)],[c_11301,c_7579])).

cnf(c_512,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4,c_352])).

cnf(c_1721,plain,
    ( k2_xboole_0(X0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_512,c_353])).

cnf(c_874,plain,
    ( k2_xboole_0(X0,k2_xboole_0(sK1,sK0)) = k2_xboole_0(sK2,k2_xboole_0(sK3,X0)) ),
    inference(superposition,[status(thm)],[c_807,c_0])).

cnf(c_3038,plain,
    ( k2_xboole_0(sK0,k2_xboole_0(sK1,X0)) = k2_xboole_0(sK2,k2_xboole_0(sK3,X0)) ),
    inference(superposition,[status(thm)],[c_359,c_874])).

cnf(c_2393,plain,
    ( k2_xboole_0(sK1,k2_xboole_0(X0,sK0)) = k2_xboole_0(sK2,k2_xboole_0(sK3,X0)) ),
    inference(superposition,[status(thm)],[c_358,c_874])).

cnf(c_3040,plain,
    ( k2_xboole_0(sK0,k2_xboole_0(sK1,X0)) = k2_xboole_0(sK1,k2_xboole_0(X0,sK0)) ),
    inference(light_normalisation,[status(thm)],[c_3038,c_2393])).

cnf(c_3565,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(sK2,k2_xboole_0(X0,X1))) = k2_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(sK1,sK0))) ),
    inference(superposition,[status(thm)],[c_3007,c_11])).

cnf(c_6434,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(sK2,k2_xboole_0(X0,sK3))) = k2_xboole_0(X0,k2_xboole_0(sK1,sK0)) ),
    inference(superposition,[status(thm)],[c_6300,c_3565])).

cnf(c_1022,plain,
    ( k2_xboole_0(sK2,k2_xboole_0(X0,sK3)) = k2_xboole_0(sK1,k2_xboole_0(sK0,X0)) ),
    inference(superposition,[status(thm)],[c_0,c_876])).

cnf(c_6439,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(sK1,k2_xboole_0(sK0,X0))) = k2_xboole_0(X0,k2_xboole_0(sK1,sK0)) ),
    inference(light_normalisation,[status(thm)],[c_6434,c_1022])).

cnf(c_11348,plain,
    ( k2_xboole_0(sK0,k2_xboole_0(sK1,sK0)) = k2_xboole_0(sK1,sK0) ),
    inference(demodulation,[status(thm)],[c_11347,c_1721,c_3040,c_6438,c_6439])).

cnf(c_808,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),X2) = k4_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_11,c_5])).

cnf(c_29637,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,sK1),sK0) = k4_xboole_0(k2_xboole_0(sK1,sK0),sK0) ),
    inference(superposition,[status(thm)],[c_6300,c_808])).

cnf(c_29903,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,sK1),sK0) = k4_xboole_0(sK1,sK0) ),
    inference(demodulation,[status(thm)],[c_29637,c_5])).

cnf(c_6676,plain,
    ( k2_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(k2_xboole_0(sK3,X0),X1)) = k2_xboole_0(X1,k2_xboole_0(X0,k2_xboole_0(sK1,sK0))) ),
    inference(superposition,[status(thm)],[c_6444,c_360])).

cnf(c_31643,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(sK3,X0),X1),k2_xboole_0(X0,k2_xboole_0(sK1,sK0))) = k2_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK3,X0)) ),
    inference(superposition,[status(thm)],[c_7057,c_6676])).

cnf(c_31795,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(sK3,X0),X1),k2_xboole_0(X0,k2_xboole_0(sK1,sK0))) = k2_xboole_0(X0,k2_xboole_0(sK1,sK0)) ),
    inference(light_normalisation,[status(thm)],[c_31643,c_6444])).

cnf(c_37028,plain,
    ( k2_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(sK1,k2_xboole_0(sK1,sK0))) = k2_xboole_0(sK1,k2_xboole_0(sK1,sK0)) ),
    inference(superposition,[status(thm)],[c_29903,c_31795])).

cnf(c_11513,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(sK2,sK0)) = k2_xboole_0(sK1,sK0) ),
    inference(superposition,[status(thm)],[c_11348,c_3007])).

cnf(c_11719,plain,
    ( k2_xboole_0(k2_xboole_0(sK2,sK0),k2_xboole_0(sK1,sK0)) = k2_xboole_0(sK1,k2_xboole_0(sK0,k2_xboole_0(sK1,sK0))) ),
    inference(superposition,[status(thm)],[c_11513,c_6683])).

cnf(c_11720,plain,
    ( k2_xboole_0(k2_xboole_0(sK2,sK0),k2_xboole_0(sK1,sK0)) = k2_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK1,sK0)) ),
    inference(superposition,[status(thm)],[c_11513,c_6444])).

cnf(c_6658,plain,
    ( k2_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK2,k2_xboole_0(sK3,sK3))) = k2_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK1,sK0)) ),
    inference(superposition,[status(thm)],[c_874,c_6444])).

cnf(c_6684,plain,
    ( k2_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(X0,k2_xboole_0(sK3,X1))) = k2_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(sK1,sK0))) ),
    inference(superposition,[status(thm)],[c_6444,c_358])).

cnf(c_6709,plain,
    ( k2_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK1,sK0)) = k2_xboole_0(sK2,k2_xboole_0(sK3,k2_xboole_0(sK1,sK0))) ),
    inference(demodulation,[status(thm)],[c_6658,c_6684])).

cnf(c_814,plain,
    ( r1_tarski(k4_xboole_0(sK2,sK3),k2_xboole_0(sK1,sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_604,c_352])).

cnf(c_962,plain,
    ( r1_tarski(sK2,k2_xboole_0(sK3,k2_xboole_0(sK1,sK0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_814,c_350])).

cnf(c_2127,plain,
    ( k2_xboole_0(sK2,k2_xboole_0(sK3,k2_xboole_0(sK1,sK0))) = k2_xboole_0(sK3,k2_xboole_0(sK1,sK0)) ),
    inference(superposition,[status(thm)],[c_962,c_353])).

cnf(c_6710,plain,
    ( k2_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK1,sK0)) = k2_xboole_0(sK1,sK0) ),
    inference(light_normalisation,[status(thm)],[c_6709,c_2127,c_6300])).

cnf(c_11730,plain,
    ( k2_xboole_0(k2_xboole_0(sK2,sK0),k2_xboole_0(sK1,sK0)) = k2_xboole_0(sK1,sK0) ),
    inference(light_normalisation,[status(thm)],[c_11720,c_6710])).

cnf(c_11731,plain,
    ( k2_xboole_0(sK1,k2_xboole_0(sK0,k2_xboole_0(sK1,sK0))) = k2_xboole_0(sK1,sK0) ),
    inference(demodulation,[status(thm)],[c_11719,c_11730])).

cnf(c_11732,plain,
    ( k2_xboole_0(sK1,k2_xboole_0(sK1,sK0)) = k2_xboole_0(sK1,sK0) ),
    inference(light_normalisation,[status(thm)],[c_11731,c_11348])).

cnf(c_37195,plain,
    ( k2_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(sK1,sK0)) = k2_xboole_0(sK1,sK0) ),
    inference(light_normalisation,[status(thm)],[c_37028,c_11732])).

cnf(c_7180,plain,
    ( k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k2_xboole_0(X0,X2) ),
    inference(superposition,[status(thm)],[c_7057,c_11])).

cnf(c_108926,plain,
    ( k2_xboole_0(sK1,k2_xboole_0(sK1,sK0)) = k2_xboole_0(sK1,sK3) ),
    inference(superposition,[status(thm)],[c_106648,c_7180])).

cnf(c_109100,plain,
    ( k2_xboole_0(sK1,sK3) = k2_xboole_0(sK1,sK0) ),
    inference(light_normalisation,[status(thm)],[c_109078,c_11348,c_37195,c_108926])).

cnf(c_118669,plain,
    ( k4_xboole_0(k2_xboole_0(sK1,sK3),k4_xboole_0(k2_xboole_0(sK1,sK3),k4_xboole_0(sK2,k4_xboole_0(sK3,sK2)))) = k4_xboole_0(sK2,k4_xboole_0(sK3,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_118363,c_3993,c_109100])).

cnf(c_1995,plain,
    ( k4_xboole_0(sK3,k2_xboole_0(sK1,X0)) = k4_xboole_0(sK3,X0) ),
    inference(superposition,[status(thm)],[c_742,c_6])).

cnf(c_2784,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(X0,sK1),X1)) = k2_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK2,X1))) ),
    inference(superposition,[status(thm)],[c_2586,c_12])).

cnf(c_2797,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(X0,k2_xboole_0(sK1,X1))) = sK2 ),
    inference(demodulation,[status(thm)],[c_2784,c_6,c_1256])).

cnf(c_12519,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK3,X0)) = sK2 ),
    inference(superposition,[status(thm)],[c_1995,c_2797])).

cnf(c_1209,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,X2))) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_9,c_12])).

cnf(c_110801,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(sK1,sK0),X0),k4_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK3,X1))) = k4_xboole_0(k2_xboole_0(sK1,sK0),k4_xboole_0(X0,k4_xboole_0(sK2,X1))) ),
    inference(superposition,[status(thm)],[c_33122,c_1209])).

cnf(c_111415,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(sK1,sK3),X0),k4_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK3,X1))) = k4_xboole_0(k2_xboole_0(sK1,sK3),k4_xboole_0(X0,k4_xboole_0(sK2,X1))) ),
    inference(light_normalisation,[status(thm)],[c_110801,c_109100])).

cnf(c_688,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_5,c_6])).

cnf(c_702,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_688,c_6])).

cnf(c_111416,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(sK1,sK3),X0),k4_xboole_0(sK1,k2_xboole_0(sK3,X1))) = k4_xboole_0(k2_xboole_0(sK1,sK3),k4_xboole_0(X0,k4_xboole_0(sK2,X1))) ),
    inference(demodulation,[status(thm)],[c_111415,c_702])).

cnf(c_3181,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X0),X2)) = k4_xboole_0(X0,X2) ),
    inference(superposition,[status(thm)],[c_2428,c_6])).

cnf(c_30316,plain,
    ( k4_xboole_0(sK1,k2_xboole_0(sK3,X0)) = k4_xboole_0(sK1,X0) ),
    inference(superposition,[status(thm)],[c_742,c_3181])).

cnf(c_111417,plain,
    ( k4_xboole_0(k2_xboole_0(sK1,sK3),k4_xboole_0(X0,k4_xboole_0(sK2,X1))) = k2_xboole_0(k4_xboole_0(k2_xboole_0(sK1,sK3),X0),k4_xboole_0(sK1,X1)) ),
    inference(demodulation,[status(thm)],[c_111416,c_30316])).

cnf(c_108880,plain,
    ( k2_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(sK3,X0)) = k2_xboole_0(k2_xboole_0(sK1,sK0),X0) ),
    inference(superposition,[status(thm)],[c_106648,c_11])).

cnf(c_108903,plain,
    ( k2_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(sK3,X0)) = k2_xboole_0(X0,k2_xboole_0(sK1,sK0)) ),
    inference(superposition,[status(thm)],[c_106648,c_360])).

cnf(c_109444,plain,
    ( k2_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(sK3,X0)) = k2_xboole_0(k2_xboole_0(sK1,sK3),X0) ),
    inference(light_normalisation,[status(thm)],[c_108880,c_108903,c_109100])).

cnf(c_4331,plain,
    ( k2_xboole_0(k2_xboole_0(sK2,X0),k2_xboole_0(X1,sK3)) = k2_xboole_0(X1,k2_xboole_0(X0,k2_xboole_0(sK1,sK0))) ),
    inference(superposition,[status(thm)],[c_3007,c_360])).

cnf(c_109579,plain,
    ( k2_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(k4_xboole_0(sK1,sK0),sK3)) = k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK1,sK0)) ),
    inference(superposition,[status(thm)],[c_109444,c_4331])).

cnf(c_109639,plain,
    ( k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK1,sK3)) = k2_xboole_0(sK1,sK0) ),
    inference(light_normalisation,[status(thm)],[c_109579,c_198,c_6710,c_106648,c_109100])).

cnf(c_109117,plain,
    ( k2_xboole_0(sK1,k2_xboole_0(sK1,sK3)) = k2_xboole_0(sK1,sK3) ),
    inference(light_normalisation,[status(thm)],[c_108926,c_108926,c_109100])).

cnf(c_109161,plain,
    ( k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK1,X0)) = k2_xboole_0(X0,k2_xboole_0(sK1,sK3)) ),
    inference(superposition,[status(thm)],[c_109117,c_359])).

cnf(c_109640,plain,
    ( k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK1,sK3)) = k2_xboole_0(sK1,sK3) ),
    inference(demodulation,[status(thm)],[c_109639,c_109100,c_109161])).

cnf(c_109927,plain,
    ( k4_xboole_0(k2_xboole_0(k2_xboole_0(sK1,sK3),sK1),sK3) = k4_xboole_0(k2_xboole_0(sK1,sK3),sK3) ),
    inference(superposition,[status(thm)],[c_109640,c_808])).

cnf(c_3167,plain,
    ( k4_xboole_0(sK1,sK3) = sK1 ),
    inference(superposition,[status(thm)],[c_742,c_2428])).

cnf(c_109964,plain,
    ( k4_xboole_0(k2_xboole_0(k2_xboole_0(sK1,sK3),sK1),sK3) = sK1 ),
    inference(demodulation,[status(thm)],[c_109927,c_5,c_3167])).

cnf(c_111743,plain,
    ( k4_xboole_0(k2_xboole_0(sK1,k2_xboole_0(sK1,sK3)),sK3) = sK1 ),
    inference(superposition,[status(thm)],[c_0,c_109964])).

cnf(c_111811,plain,
    ( k4_xboole_0(k2_xboole_0(sK1,sK3),sK3) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_111743,c_109117])).

cnf(c_726,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X2)))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_9,c_6])).

cnf(c_728,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X2))))) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_726,c_6])).

cnf(c_729,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2)))))) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_728,c_6])).

cnf(c_108898,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(X0,k2_xboole_0(sK1,sK0)))))) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(sK1,sK0),sK3)) ),
    inference(superposition,[status(thm)],[c_106648,c_729])).

cnf(c_108943,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(X0,k2_xboole_0(sK1,sK0)))))) = k4_xboole_0(X0,k2_xboole_0(sK1,sK0)) ),
    inference(demodulation,[status(thm)],[c_108898,c_106648])).

cnf(c_114825,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(X0,k2_xboole_0(sK1,sK3)))))) = k4_xboole_0(X0,k2_xboole_0(sK1,sK3)) ),
    inference(light_normalisation,[status(thm)],[c_108943,c_108943,c_109100])).

cnf(c_114919,plain,
    ( k4_xboole_0(k2_xboole_0(sK1,sK0),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK1,sK3))))),sK3)) = k2_xboole_0(k4_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK1,sK3)),k4_xboole_0(k2_xboole_0(sK1,sK0),k4_xboole_0(sK2,sK3))) ),
    inference(superposition,[status(thm)],[c_114825,c_1221])).

cnf(c_115099,plain,
    ( k4_xboole_0(k2_xboole_0(sK1,sK3),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK1,sK3))))),sK3)) = k2_xboole_0(k4_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK1,sK3)),k4_xboole_0(k2_xboole_0(sK1,sK3),sK2)) ),
    inference(light_normalisation,[status(thm)],[c_114919,c_2782,c_109100])).

cnf(c_4731,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(k4_xboole_0(X1,X0),X2) ),
    inference(superposition,[status(thm)],[c_602,c_6])).

cnf(c_4750,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(X1,k2_xboole_0(X0,X2)) ),
    inference(demodulation,[status(thm)],[c_4731,c_6])).

cnf(c_109022,plain,
    ( k4_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(k4_xboole_0(sK1,sK0),X0)) = k4_xboole_0(sK3,k2_xboole_0(k4_xboole_0(sK1,sK0),X0)) ),
    inference(superposition,[status(thm)],[c_108890,c_702])).

cnf(c_109279,plain,
    ( k4_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(k4_xboole_0(sK1,sK0),X0)) = k4_xboole_0(sK3,k2_xboole_0(k4_xboole_0(sK1,sK0),X0)) ),
    inference(light_normalisation,[status(thm)],[c_109022,c_109100])).

cnf(c_67738,plain,
    ( k4_xboole_0(sK3,k2_xboole_0(k4_xboole_0(sK1,X0),X1)) = k4_xboole_0(sK3,k2_xboole_0(sK1,X1)) ),
    inference(superposition,[status(thm)],[c_7180,c_1995])).

cnf(c_67828,plain,
    ( k4_xboole_0(sK3,k2_xboole_0(k4_xboole_0(sK1,X0),X1)) = k4_xboole_0(sK3,X1) ),
    inference(demodulation,[status(thm)],[c_67738,c_1995])).

cnf(c_109280,plain,
    ( k4_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(k4_xboole_0(sK1,sK0),X0)) = k4_xboole_0(sK3,X0) ),
    inference(demodulation,[status(thm)],[c_109279,c_67828])).

cnf(c_115100,plain,
    ( k4_xboole_0(k2_xboole_0(sK1,sK3),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(sK3,k4_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK1,sK3)))),sK3)) = k2_xboole_0(k4_xboole_0(sK3,k2_xboole_0(sK1,sK3)),k4_xboole_0(k2_xboole_0(sK1,sK3),sK2)) ),
    inference(demodulation,[status(thm)],[c_115099,c_4750,c_109280])).

cnf(c_7435,plain,
    ( k2_xboole_0(k4_xboole_0(sK3,X0),k4_xboole_0(sK3,k4_xboole_0(sK3,X1))) = k4_xboole_0(sK3,k4_xboole_0(k2_xboole_0(sK1,X0),X1)) ),
    inference(superposition,[status(thm)],[c_1995,c_12])).

cnf(c_7448,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(k2_xboole_0(sK1,X0),X1)) = k4_xboole_0(sK3,k4_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_7435,c_12])).

cnf(c_115101,plain,
    ( k4_xboole_0(k2_xboole_0(sK1,sK3),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(sK3,k4_xboole_0(sK3,k2_xboole_0(sK1,sK3)))),sK3)) = k2_xboole_0(k4_xboole_0(sK3,sK3),k4_xboole_0(k2_xboole_0(sK1,sK3),sK2)) ),
    inference(demodulation,[status(thm)],[c_115100,c_1995,c_7448])).

cnf(c_115102,plain,
    ( k4_xboole_0(k2_xboole_0(sK1,sK3),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(sK3,k4_xboole_0(sK3,sK3))),sK3)) = k4_xboole_0(k2_xboole_0(sK1,sK3),sK2) ),
    inference(demodulation,[status(thm)],[c_115101,c_1328,c_2016,c_2268])).

cnf(c_1219,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(X0,k4_xboole_0(sK3,sK1))) = k2_xboole_0(k4_xboole_0(sK3,X0),k4_xboole_0(sK3,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_129,c_12])).

cnf(c_1232,plain,
    ( k2_xboole_0(k4_xboole_0(sK3,X0),k4_xboole_0(sK3,k1_xboole_0)) = k4_xboole_0(sK3,k4_xboole_0(X0,sK3)) ),
    inference(light_normalisation,[status(thm)],[c_1219,c_742])).

cnf(c_1233,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(X0,sK3)) = k2_xboole_0(k4_xboole_0(sK3,X0),sK3) ),
    inference(demodulation,[status(thm)],[c_1232,c_4])).

cnf(c_67607,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X2),X0) = k4_xboole_0(k2_xboole_0(X0,X2),X0) ),
    inference(superposition,[status(thm)],[c_7180,c_602])).

cnf(c_67906,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X2),X0) = k4_xboole_0(X2,X0) ),
    inference(demodulation,[status(thm)],[c_67607,c_602])).

cnf(c_112319,plain,
    ( k2_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(sK3,X0)) = k2_xboole_0(X0,k2_xboole_0(sK1,sK3)) ),
    inference(light_normalisation,[status(thm)],[c_108903,c_109100,c_109444])).

cnf(c_112336,plain,
    ( k2_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(X0,sK3)) = k2_xboole_0(X0,k2_xboole_0(sK1,sK3)) ),
    inference(superposition,[status(thm)],[c_0,c_112319])).

cnf(c_115103,plain,
    ( k4_xboole_0(k2_xboole_0(sK1,sK3),k4_xboole_0(k2_xboole_0(sK1,sK3),sK3)) = k4_xboole_0(k2_xboole_0(sK1,sK3),sK2) ),
    inference(demodulation,[status(thm)],[c_115102,c_1233,c_67906,c_112336])).

cnf(c_109020,plain,
    ( k4_xboole_0(k2_xboole_0(sK1,sK0),k4_xboole_0(k2_xboole_0(sK1,sK0),k4_xboole_0(sK3,k4_xboole_0(sK1,sK0)))) = k4_xboole_0(sK3,k4_xboole_0(sK1,sK0)) ),
    inference(superposition,[status(thm)],[c_108890,c_739])).

cnf(c_109281,plain,
    ( k4_xboole_0(k2_xboole_0(sK1,sK3),k4_xboole_0(k2_xboole_0(sK1,sK3),k4_xboole_0(sK3,k4_xboole_0(sK1,sK0)))) = k4_xboole_0(sK3,k4_xboole_0(sK1,sK0)) ),
    inference(light_normalisation,[status(thm)],[c_109020,c_109100])).

cnf(c_1993,plain,
    ( k2_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK3,X0))) = k4_xboole_0(sK3,k4_xboole_0(sK1,X0)) ),
    inference(superposition,[status(thm)],[c_742,c_12])).

cnf(c_2002,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK1,X0)) = sK3 ),
    inference(demodulation,[status(thm)],[c_1993,c_1256])).

cnf(c_109282,plain,
    ( k4_xboole_0(k2_xboole_0(sK1,sK3),k4_xboole_0(sK1,sK3)) = sK3 ),
    inference(demodulation,[status(thm)],[c_109281,c_5,c_2002])).

cnf(c_109283,plain,
    ( k4_xboole_0(k2_xboole_0(sK1,sK3),sK1) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_109282,c_3167])).

cnf(c_115104,plain,
    ( k4_xboole_0(k2_xboole_0(sK1,sK3),sK2) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_115103,c_109283,c_111811])).

cnf(c_118670,plain,
    ( sK2 = sK1 ),
    inference(demodulation,[status(thm)],[c_118669,c_12519,c_111417,c_111811,c_115104])).

cnf(c_201,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_362,plain,
    ( sK2 != X0
    | sK1 != X0
    | sK1 = sK2 ),
    inference(instantiation,[status(thm)],[c_201])).

cnf(c_34916,plain,
    ( sK2 != sK1
    | sK1 = sK2
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_362])).

cnf(c_200,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_490,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_200])).

cnf(c_13,negated_conjecture,
    ( sK1 != sK2 ),
    inference(cnf_transformation,[],[f43])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_118670,c_34916,c_490,c_13])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:05:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 35.47/5.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 35.47/5.00  
% 35.47/5.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 35.47/5.00  
% 35.47/5.00  ------  iProver source info
% 35.47/5.00  
% 35.47/5.00  git: date: 2020-06-30 10:37:57 +0100
% 35.47/5.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 35.47/5.00  git: non_committed_changes: false
% 35.47/5.00  git: last_make_outside_of_git: false
% 35.47/5.00  
% 35.47/5.00  ------ 
% 35.47/5.00  
% 35.47/5.00  ------ Input Options
% 35.47/5.00  
% 35.47/5.00  --out_options                           all
% 35.47/5.00  --tptp_safe_out                         true
% 35.47/5.00  --problem_path                          ""
% 35.47/5.00  --include_path                          ""
% 35.47/5.00  --clausifier                            res/vclausify_rel
% 35.47/5.00  --clausifier_options                    ""
% 35.47/5.00  --stdin                                 false
% 35.47/5.00  --stats_out                             all
% 35.47/5.00  
% 35.47/5.00  ------ General Options
% 35.47/5.00  
% 35.47/5.00  --fof                                   false
% 35.47/5.00  --time_out_real                         305.
% 35.47/5.00  --time_out_virtual                      -1.
% 35.47/5.00  --symbol_type_check                     false
% 35.47/5.00  --clausify_out                          false
% 35.47/5.00  --sig_cnt_out                           false
% 35.47/5.00  --trig_cnt_out                          false
% 35.47/5.00  --trig_cnt_out_tolerance                1.
% 35.47/5.00  --trig_cnt_out_sk_spl                   false
% 35.47/5.00  --abstr_cl_out                          false
% 35.47/5.00  
% 35.47/5.00  ------ Global Options
% 35.47/5.00  
% 35.47/5.00  --schedule                              default
% 35.47/5.00  --add_important_lit                     false
% 35.47/5.00  --prop_solver_per_cl                    1000
% 35.47/5.00  --min_unsat_core                        false
% 35.47/5.00  --soft_assumptions                      false
% 35.47/5.00  --soft_lemma_size                       3
% 35.47/5.00  --prop_impl_unit_size                   0
% 35.47/5.00  --prop_impl_unit                        []
% 35.47/5.00  --share_sel_clauses                     true
% 35.47/5.00  --reset_solvers                         false
% 35.47/5.00  --bc_imp_inh                            [conj_cone]
% 35.47/5.00  --conj_cone_tolerance                   3.
% 35.47/5.00  --extra_neg_conj                        none
% 35.47/5.00  --large_theory_mode                     true
% 35.47/5.00  --prolific_symb_bound                   200
% 35.47/5.00  --lt_threshold                          2000
% 35.47/5.00  --clause_weak_htbl                      true
% 35.47/5.00  --gc_record_bc_elim                     false
% 35.47/5.00  
% 35.47/5.00  ------ Preprocessing Options
% 35.47/5.00  
% 35.47/5.00  --preprocessing_flag                    true
% 35.47/5.00  --time_out_prep_mult                    0.1
% 35.47/5.00  --splitting_mode                        input
% 35.47/5.00  --splitting_grd                         true
% 35.47/5.00  --splitting_cvd                         false
% 35.47/5.00  --splitting_cvd_svl                     false
% 35.47/5.00  --splitting_nvd                         32
% 35.47/5.00  --sub_typing                            true
% 35.47/5.00  --prep_gs_sim                           true
% 35.47/5.00  --prep_unflatten                        true
% 35.47/5.00  --prep_res_sim                          true
% 35.47/5.00  --prep_upred                            true
% 35.47/5.00  --prep_sem_filter                       exhaustive
% 35.47/5.00  --prep_sem_filter_out                   false
% 35.47/5.00  --pred_elim                             true
% 35.47/5.00  --res_sim_input                         true
% 35.47/5.00  --eq_ax_congr_red                       true
% 35.47/5.00  --pure_diseq_elim                       true
% 35.47/5.00  --brand_transform                       false
% 35.47/5.00  --non_eq_to_eq                          false
% 35.47/5.00  --prep_def_merge                        true
% 35.47/5.00  --prep_def_merge_prop_impl              false
% 35.47/5.00  --prep_def_merge_mbd                    true
% 35.47/5.00  --prep_def_merge_tr_red                 false
% 35.47/5.00  --prep_def_merge_tr_cl                  false
% 35.47/5.00  --smt_preprocessing                     true
% 35.47/5.00  --smt_ac_axioms                         fast
% 35.47/5.00  --preprocessed_out                      false
% 35.47/5.00  --preprocessed_stats                    false
% 35.47/5.00  
% 35.47/5.00  ------ Abstraction refinement Options
% 35.47/5.00  
% 35.47/5.00  --abstr_ref                             []
% 35.47/5.00  --abstr_ref_prep                        false
% 35.47/5.00  --abstr_ref_until_sat                   false
% 35.47/5.00  --abstr_ref_sig_restrict                funpre
% 35.47/5.00  --abstr_ref_af_restrict_to_split_sk     false
% 35.47/5.00  --abstr_ref_under                       []
% 35.47/5.00  
% 35.47/5.00  ------ SAT Options
% 35.47/5.00  
% 35.47/5.00  --sat_mode                              false
% 35.47/5.00  --sat_fm_restart_options                ""
% 35.47/5.00  --sat_gr_def                            false
% 35.47/5.00  --sat_epr_types                         true
% 35.47/5.00  --sat_non_cyclic_types                  false
% 35.47/5.00  --sat_finite_models                     false
% 35.47/5.00  --sat_fm_lemmas                         false
% 35.47/5.00  --sat_fm_prep                           false
% 35.47/5.00  --sat_fm_uc_incr                        true
% 35.47/5.00  --sat_out_model                         small
% 35.47/5.00  --sat_out_clauses                       false
% 35.47/5.00  
% 35.47/5.00  ------ QBF Options
% 35.47/5.00  
% 35.47/5.00  --qbf_mode                              false
% 35.47/5.00  --qbf_elim_univ                         false
% 35.47/5.00  --qbf_dom_inst                          none
% 35.47/5.00  --qbf_dom_pre_inst                      false
% 35.47/5.00  --qbf_sk_in                             false
% 35.47/5.00  --qbf_pred_elim                         true
% 35.47/5.00  --qbf_split                             512
% 35.47/5.00  
% 35.47/5.00  ------ BMC1 Options
% 35.47/5.00  
% 35.47/5.00  --bmc1_incremental                      false
% 35.47/5.00  --bmc1_axioms                           reachable_all
% 35.47/5.00  --bmc1_min_bound                        0
% 35.47/5.00  --bmc1_max_bound                        -1
% 35.47/5.00  --bmc1_max_bound_default                -1
% 35.47/5.00  --bmc1_symbol_reachability              true
% 35.47/5.00  --bmc1_property_lemmas                  false
% 35.47/5.00  --bmc1_k_induction                      false
% 35.47/5.00  --bmc1_non_equiv_states                 false
% 35.47/5.00  --bmc1_deadlock                         false
% 35.47/5.00  --bmc1_ucm                              false
% 35.47/5.00  --bmc1_add_unsat_core                   none
% 35.47/5.00  --bmc1_unsat_core_children              false
% 35.47/5.00  --bmc1_unsat_core_extrapolate_axioms    false
% 35.47/5.00  --bmc1_out_stat                         full
% 35.47/5.00  --bmc1_ground_init                      false
% 35.47/5.00  --bmc1_pre_inst_next_state              false
% 35.47/5.00  --bmc1_pre_inst_state                   false
% 35.47/5.00  --bmc1_pre_inst_reach_state             false
% 35.47/5.00  --bmc1_out_unsat_core                   false
% 35.47/5.00  --bmc1_aig_witness_out                  false
% 35.47/5.00  --bmc1_verbose                          false
% 35.47/5.00  --bmc1_dump_clauses_tptp                false
% 35.47/5.00  --bmc1_dump_unsat_core_tptp             false
% 35.47/5.00  --bmc1_dump_file                        -
% 35.47/5.00  --bmc1_ucm_expand_uc_limit              128
% 35.47/5.00  --bmc1_ucm_n_expand_iterations          6
% 35.47/5.00  --bmc1_ucm_extend_mode                  1
% 35.47/5.00  --bmc1_ucm_init_mode                    2
% 35.47/5.00  --bmc1_ucm_cone_mode                    none
% 35.47/5.00  --bmc1_ucm_reduced_relation_type        0
% 35.47/5.00  --bmc1_ucm_relax_model                  4
% 35.47/5.00  --bmc1_ucm_full_tr_after_sat            true
% 35.47/5.00  --bmc1_ucm_expand_neg_assumptions       false
% 35.47/5.00  --bmc1_ucm_layered_model                none
% 35.47/5.00  --bmc1_ucm_max_lemma_size               10
% 35.47/5.00  
% 35.47/5.00  ------ AIG Options
% 35.47/5.00  
% 35.47/5.00  --aig_mode                              false
% 35.47/5.00  
% 35.47/5.00  ------ Instantiation Options
% 35.47/5.00  
% 35.47/5.00  --instantiation_flag                    true
% 35.47/5.00  --inst_sos_flag                         true
% 35.47/5.00  --inst_sos_phase                        true
% 35.47/5.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 35.47/5.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 35.47/5.00  --inst_lit_sel_side                     num_symb
% 35.47/5.00  --inst_solver_per_active                1400
% 35.47/5.00  --inst_solver_calls_frac                1.
% 35.47/5.00  --inst_passive_queue_type               priority_queues
% 35.47/5.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 35.47/5.00  --inst_passive_queues_freq              [25;2]
% 35.47/5.00  --inst_dismatching                      true
% 35.47/5.00  --inst_eager_unprocessed_to_passive     true
% 35.47/5.00  --inst_prop_sim_given                   true
% 35.47/5.00  --inst_prop_sim_new                     false
% 35.47/5.00  --inst_subs_new                         false
% 35.47/5.00  --inst_eq_res_simp                      false
% 35.47/5.00  --inst_subs_given                       false
% 35.47/5.00  --inst_orphan_elimination               true
% 35.47/5.00  --inst_learning_loop_flag               true
% 35.47/5.00  --inst_learning_start                   3000
% 35.47/5.00  --inst_learning_factor                  2
% 35.47/5.00  --inst_start_prop_sim_after_learn       3
% 35.47/5.00  --inst_sel_renew                        solver
% 35.47/5.00  --inst_lit_activity_flag                true
% 35.47/5.00  --inst_restr_to_given                   false
% 35.47/5.00  --inst_activity_threshold               500
% 35.47/5.00  --inst_out_proof                        true
% 35.47/5.00  
% 35.47/5.00  ------ Resolution Options
% 35.47/5.00  
% 35.47/5.00  --resolution_flag                       true
% 35.47/5.00  --res_lit_sel                           adaptive
% 35.47/5.00  --res_lit_sel_side                      none
% 35.47/5.00  --res_ordering                          kbo
% 35.47/5.00  --res_to_prop_solver                    active
% 35.47/5.00  --res_prop_simpl_new                    false
% 35.47/5.00  --res_prop_simpl_given                  true
% 35.47/5.00  --res_passive_queue_type                priority_queues
% 35.47/5.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 35.47/5.00  --res_passive_queues_freq               [15;5]
% 35.47/5.00  --res_forward_subs                      full
% 35.47/5.00  --res_backward_subs                     full
% 35.47/5.00  --res_forward_subs_resolution           true
% 35.47/5.00  --res_backward_subs_resolution          true
% 35.47/5.00  --res_orphan_elimination                true
% 35.47/5.00  --res_time_limit                        2.
% 35.47/5.00  --res_out_proof                         true
% 35.47/5.00  
% 35.47/5.00  ------ Superposition Options
% 35.47/5.00  
% 35.47/5.00  --superposition_flag                    true
% 35.47/5.00  --sup_passive_queue_type                priority_queues
% 35.47/5.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 35.47/5.00  --sup_passive_queues_freq               [8;1;4]
% 35.47/5.00  --demod_completeness_check              fast
% 35.47/5.00  --demod_use_ground                      true
% 35.47/5.00  --sup_to_prop_solver                    passive
% 35.47/5.00  --sup_prop_simpl_new                    true
% 35.47/5.00  --sup_prop_simpl_given                  true
% 35.47/5.00  --sup_fun_splitting                     true
% 35.47/5.00  --sup_smt_interval                      50000
% 35.47/5.00  
% 35.47/5.00  ------ Superposition Simplification Setup
% 35.47/5.00  
% 35.47/5.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 35.47/5.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 35.47/5.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 35.47/5.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 35.47/5.00  --sup_full_triv                         [TrivRules;PropSubs]
% 35.47/5.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 35.47/5.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 35.47/5.00  --sup_immed_triv                        [TrivRules]
% 35.47/5.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 35.47/5.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 35.47/5.00  --sup_immed_bw_main                     []
% 35.47/5.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 35.47/5.00  --sup_input_triv                        [Unflattening;TrivRules]
% 35.47/5.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 35.47/5.00  --sup_input_bw                          []
% 35.47/5.00  
% 35.47/5.00  ------ Combination Options
% 35.47/5.00  
% 35.47/5.00  --comb_res_mult                         3
% 35.47/5.00  --comb_sup_mult                         2
% 35.47/5.00  --comb_inst_mult                        10
% 35.47/5.00  
% 35.47/5.00  ------ Debug Options
% 35.47/5.00  
% 35.47/5.00  --dbg_backtrace                         false
% 35.47/5.00  --dbg_dump_prop_clauses                 false
% 35.47/5.00  --dbg_dump_prop_clauses_file            -
% 35.47/5.00  --dbg_out_stat                          false
% 35.47/5.00  ------ Parsing...
% 35.47/5.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 35.47/5.00  
% 35.47/5.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 35.47/5.00  
% 35.47/5.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 35.47/5.00  
% 35.47/5.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.47/5.00  ------ Proving...
% 35.47/5.00  ------ Problem Properties 
% 35.47/5.00  
% 35.47/5.00  
% 35.47/5.00  clauses                                 16
% 35.47/5.00  conjectures                             2
% 35.47/5.00  EPR                                     1
% 35.47/5.00  Horn                                    16
% 35.47/5.00  unary                                   13
% 35.47/5.00  binary                                  3
% 35.47/5.00  lits                                    19
% 35.47/5.00  lits eq                                 13
% 35.47/5.00  fd_pure                                 0
% 35.47/5.00  fd_pseudo                               0
% 35.47/5.00  fd_cond                                 0
% 35.47/5.00  fd_pseudo_cond                          0
% 35.47/5.00  AC symbols                              1
% 35.47/5.00  
% 35.47/5.00  ------ Schedule dynamic 5 is on 
% 35.47/5.00  
% 35.47/5.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 35.47/5.00  
% 35.47/5.00  
% 35.47/5.00  ------ 
% 35.47/5.00  Current options:
% 35.47/5.00  ------ 
% 35.47/5.00  
% 35.47/5.00  ------ Input Options
% 35.47/5.00  
% 35.47/5.00  --out_options                           all
% 35.47/5.00  --tptp_safe_out                         true
% 35.47/5.00  --problem_path                          ""
% 35.47/5.00  --include_path                          ""
% 35.47/5.00  --clausifier                            res/vclausify_rel
% 35.47/5.00  --clausifier_options                    ""
% 35.47/5.00  --stdin                                 false
% 35.47/5.00  --stats_out                             all
% 35.47/5.00  
% 35.47/5.00  ------ General Options
% 35.47/5.00  
% 35.47/5.00  --fof                                   false
% 35.47/5.00  --time_out_real                         305.
% 35.47/5.00  --time_out_virtual                      -1.
% 35.47/5.00  --symbol_type_check                     false
% 35.47/5.00  --clausify_out                          false
% 35.47/5.00  --sig_cnt_out                           false
% 35.47/5.00  --trig_cnt_out                          false
% 35.47/5.00  --trig_cnt_out_tolerance                1.
% 35.47/5.00  --trig_cnt_out_sk_spl                   false
% 35.47/5.00  --abstr_cl_out                          false
% 35.47/5.00  
% 35.47/5.00  ------ Global Options
% 35.47/5.00  
% 35.47/5.00  --schedule                              default
% 35.47/5.00  --add_important_lit                     false
% 35.47/5.00  --prop_solver_per_cl                    1000
% 35.47/5.00  --min_unsat_core                        false
% 35.47/5.00  --soft_assumptions                      false
% 35.47/5.00  --soft_lemma_size                       3
% 35.47/5.00  --prop_impl_unit_size                   0
% 35.47/5.00  --prop_impl_unit                        []
% 35.47/5.00  --share_sel_clauses                     true
% 35.47/5.00  --reset_solvers                         false
% 35.47/5.00  --bc_imp_inh                            [conj_cone]
% 35.47/5.00  --conj_cone_tolerance                   3.
% 35.47/5.00  --extra_neg_conj                        none
% 35.47/5.00  --large_theory_mode                     true
% 35.47/5.00  --prolific_symb_bound                   200
% 35.47/5.00  --lt_threshold                          2000
% 35.47/5.00  --clause_weak_htbl                      true
% 35.47/5.00  --gc_record_bc_elim                     false
% 35.47/5.00  
% 35.47/5.00  ------ Preprocessing Options
% 35.47/5.00  
% 35.47/5.00  --preprocessing_flag                    true
% 35.47/5.00  --time_out_prep_mult                    0.1
% 35.47/5.00  --splitting_mode                        input
% 35.47/5.00  --splitting_grd                         true
% 35.47/5.00  --splitting_cvd                         false
% 35.47/5.00  --splitting_cvd_svl                     false
% 35.47/5.00  --splitting_nvd                         32
% 35.47/5.00  --sub_typing                            true
% 35.47/5.00  --prep_gs_sim                           true
% 35.47/5.00  --prep_unflatten                        true
% 35.47/5.00  --prep_res_sim                          true
% 35.47/5.00  --prep_upred                            true
% 35.47/5.00  --prep_sem_filter                       exhaustive
% 35.47/5.00  --prep_sem_filter_out                   false
% 35.47/5.00  --pred_elim                             true
% 35.47/5.00  --res_sim_input                         true
% 35.47/5.00  --eq_ax_congr_red                       true
% 35.47/5.00  --pure_diseq_elim                       true
% 35.47/5.00  --brand_transform                       false
% 35.47/5.00  --non_eq_to_eq                          false
% 35.47/5.00  --prep_def_merge                        true
% 35.47/5.00  --prep_def_merge_prop_impl              false
% 35.47/5.00  --prep_def_merge_mbd                    true
% 35.47/5.00  --prep_def_merge_tr_red                 false
% 35.47/5.00  --prep_def_merge_tr_cl                  false
% 35.47/5.00  --smt_preprocessing                     true
% 35.47/5.00  --smt_ac_axioms                         fast
% 35.47/5.00  --preprocessed_out                      false
% 35.47/5.00  --preprocessed_stats                    false
% 35.47/5.00  
% 35.47/5.00  ------ Abstraction refinement Options
% 35.47/5.00  
% 35.47/5.00  --abstr_ref                             []
% 35.47/5.00  --abstr_ref_prep                        false
% 35.47/5.00  --abstr_ref_until_sat                   false
% 35.47/5.00  --abstr_ref_sig_restrict                funpre
% 35.47/5.00  --abstr_ref_af_restrict_to_split_sk     false
% 35.47/5.00  --abstr_ref_under                       []
% 35.47/5.00  
% 35.47/5.00  ------ SAT Options
% 35.47/5.00  
% 35.47/5.00  --sat_mode                              false
% 35.47/5.00  --sat_fm_restart_options                ""
% 35.47/5.00  --sat_gr_def                            false
% 35.47/5.00  --sat_epr_types                         true
% 35.47/5.00  --sat_non_cyclic_types                  false
% 35.47/5.00  --sat_finite_models                     false
% 35.47/5.00  --sat_fm_lemmas                         false
% 35.47/5.00  --sat_fm_prep                           false
% 35.47/5.00  --sat_fm_uc_incr                        true
% 35.47/5.00  --sat_out_model                         small
% 35.47/5.00  --sat_out_clauses                       false
% 35.47/5.00  
% 35.47/5.00  ------ QBF Options
% 35.47/5.00  
% 35.47/5.00  --qbf_mode                              false
% 35.47/5.00  --qbf_elim_univ                         false
% 35.47/5.00  --qbf_dom_inst                          none
% 35.47/5.00  --qbf_dom_pre_inst                      false
% 35.47/5.00  --qbf_sk_in                             false
% 35.47/5.00  --qbf_pred_elim                         true
% 35.47/5.00  --qbf_split                             512
% 35.47/5.00  
% 35.47/5.00  ------ BMC1 Options
% 35.47/5.00  
% 35.47/5.00  --bmc1_incremental                      false
% 35.47/5.00  --bmc1_axioms                           reachable_all
% 35.47/5.00  --bmc1_min_bound                        0
% 35.47/5.00  --bmc1_max_bound                        -1
% 35.47/5.00  --bmc1_max_bound_default                -1
% 35.47/5.00  --bmc1_symbol_reachability              true
% 35.47/5.00  --bmc1_property_lemmas                  false
% 35.47/5.00  --bmc1_k_induction                      false
% 35.47/5.00  --bmc1_non_equiv_states                 false
% 35.47/5.00  --bmc1_deadlock                         false
% 35.47/5.00  --bmc1_ucm                              false
% 35.47/5.00  --bmc1_add_unsat_core                   none
% 35.47/5.00  --bmc1_unsat_core_children              false
% 35.47/5.00  --bmc1_unsat_core_extrapolate_axioms    false
% 35.47/5.00  --bmc1_out_stat                         full
% 35.47/5.00  --bmc1_ground_init                      false
% 35.47/5.00  --bmc1_pre_inst_next_state              false
% 35.47/5.00  --bmc1_pre_inst_state                   false
% 35.47/5.00  --bmc1_pre_inst_reach_state             false
% 35.47/5.00  --bmc1_out_unsat_core                   false
% 35.47/5.00  --bmc1_aig_witness_out                  false
% 35.47/5.00  --bmc1_verbose                          false
% 35.47/5.00  --bmc1_dump_clauses_tptp                false
% 35.47/5.00  --bmc1_dump_unsat_core_tptp             false
% 35.47/5.00  --bmc1_dump_file                        -
% 35.47/5.00  --bmc1_ucm_expand_uc_limit              128
% 35.47/5.00  --bmc1_ucm_n_expand_iterations          6
% 35.47/5.00  --bmc1_ucm_extend_mode                  1
% 35.47/5.00  --bmc1_ucm_init_mode                    2
% 35.47/5.00  --bmc1_ucm_cone_mode                    none
% 35.47/5.00  --bmc1_ucm_reduced_relation_type        0
% 35.47/5.00  --bmc1_ucm_relax_model                  4
% 35.47/5.00  --bmc1_ucm_full_tr_after_sat            true
% 35.47/5.00  --bmc1_ucm_expand_neg_assumptions       false
% 35.47/5.00  --bmc1_ucm_layered_model                none
% 35.47/5.00  --bmc1_ucm_max_lemma_size               10
% 35.47/5.00  
% 35.47/5.00  ------ AIG Options
% 35.47/5.00  
% 35.47/5.00  --aig_mode                              false
% 35.47/5.00  
% 35.47/5.00  ------ Instantiation Options
% 35.47/5.00  
% 35.47/5.00  --instantiation_flag                    true
% 35.47/5.00  --inst_sos_flag                         true
% 35.47/5.00  --inst_sos_phase                        true
% 35.47/5.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 35.47/5.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 35.47/5.00  --inst_lit_sel_side                     none
% 35.47/5.00  --inst_solver_per_active                1400
% 35.47/5.00  --inst_solver_calls_frac                1.
% 35.47/5.00  --inst_passive_queue_type               priority_queues
% 35.47/5.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 35.47/5.00  --inst_passive_queues_freq              [25;2]
% 35.47/5.00  --inst_dismatching                      true
% 35.47/5.00  --inst_eager_unprocessed_to_passive     true
% 35.47/5.00  --inst_prop_sim_given                   true
% 35.47/5.00  --inst_prop_sim_new                     false
% 35.47/5.00  --inst_subs_new                         false
% 35.47/5.00  --inst_eq_res_simp                      false
% 35.47/5.00  --inst_subs_given                       false
% 35.47/5.00  --inst_orphan_elimination               true
% 35.47/5.00  --inst_learning_loop_flag               true
% 35.47/5.00  --inst_learning_start                   3000
% 35.47/5.00  --inst_learning_factor                  2
% 35.47/5.00  --inst_start_prop_sim_after_learn       3
% 35.47/5.00  --inst_sel_renew                        solver
% 35.47/5.00  --inst_lit_activity_flag                true
% 35.47/5.00  --inst_restr_to_given                   false
% 35.47/5.00  --inst_activity_threshold               500
% 35.47/5.00  --inst_out_proof                        true
% 35.47/5.00  
% 35.47/5.00  ------ Resolution Options
% 35.47/5.00  
% 35.47/5.00  --resolution_flag                       false
% 35.47/5.00  --res_lit_sel                           adaptive
% 35.47/5.00  --res_lit_sel_side                      none
% 35.47/5.00  --res_ordering                          kbo
% 35.47/5.00  --res_to_prop_solver                    active
% 35.47/5.00  --res_prop_simpl_new                    false
% 35.47/5.00  --res_prop_simpl_given                  true
% 35.47/5.00  --res_passive_queue_type                priority_queues
% 35.47/5.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 35.47/5.00  --res_passive_queues_freq               [15;5]
% 35.47/5.00  --res_forward_subs                      full
% 35.47/5.00  --res_backward_subs                     full
% 35.47/5.00  --res_forward_subs_resolution           true
% 35.47/5.00  --res_backward_subs_resolution          true
% 35.47/5.00  --res_orphan_elimination                true
% 35.47/5.00  --res_time_limit                        2.
% 35.47/5.00  --res_out_proof                         true
% 35.47/5.00  
% 35.47/5.00  ------ Superposition Options
% 35.47/5.00  
% 35.47/5.00  --superposition_flag                    true
% 35.47/5.00  --sup_passive_queue_type                priority_queues
% 35.47/5.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 35.47/5.00  --sup_passive_queues_freq               [8;1;4]
% 35.47/5.00  --demod_completeness_check              fast
% 35.47/5.00  --demod_use_ground                      true
% 35.47/5.00  --sup_to_prop_solver                    passive
% 35.47/5.00  --sup_prop_simpl_new                    true
% 35.47/5.00  --sup_prop_simpl_given                  true
% 35.47/5.00  --sup_fun_splitting                     true
% 35.47/5.00  --sup_smt_interval                      50000
% 35.47/5.00  
% 35.47/5.00  ------ Superposition Simplification Setup
% 35.47/5.00  
% 35.47/5.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 35.47/5.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 35.47/5.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 35.47/5.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 35.47/5.00  --sup_full_triv                         [TrivRules;PropSubs]
% 35.47/5.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 35.47/5.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 35.47/5.00  --sup_immed_triv                        [TrivRules]
% 35.47/5.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 35.47/5.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 35.47/5.00  --sup_immed_bw_main                     []
% 35.47/5.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 35.47/5.00  --sup_input_triv                        [Unflattening;TrivRules]
% 35.47/5.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 35.47/5.00  --sup_input_bw                          []
% 35.47/5.00  
% 35.47/5.00  ------ Combination Options
% 35.47/5.00  
% 35.47/5.00  --comb_res_mult                         3
% 35.47/5.00  --comb_sup_mult                         2
% 35.47/5.00  --comb_inst_mult                        10
% 35.47/5.00  
% 35.47/5.00  ------ Debug Options
% 35.47/5.00  
% 35.47/5.00  --dbg_backtrace                         false
% 35.47/5.00  --dbg_dump_prop_clauses                 false
% 35.47/5.00  --dbg_dump_prop_clauses_file            -
% 35.47/5.00  --dbg_out_stat                          false
% 35.47/5.00  
% 35.47/5.00  
% 35.47/5.00  
% 35.47/5.00  
% 35.47/5.00  ------ Proving...
% 35.47/5.00  
% 35.47/5.00  
% 35.47/5.00  % SZS status Theorem for theBenchmark.p
% 35.47/5.00  
% 35.47/5.00  % SZS output start CNFRefutation for theBenchmark.p
% 35.47/5.00  
% 35.47/5.00  fof(f15,conjecture,(
% 35.47/5.00    ! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 35.47/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.47/5.00  
% 35.47/5.00  fof(f16,negated_conjecture,(
% 35.47/5.00    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 35.47/5.00    inference(negated_conjecture,[],[f15])).
% 35.47/5.00  
% 35.47/5.00  fof(f22,plain,(
% 35.47/5.00    ? [X0,X1,X2,X3] : (X1 != X2 & (r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)))),
% 35.47/5.00    inference(ennf_transformation,[],[f16])).
% 35.47/5.00  
% 35.47/5.00  fof(f23,plain,(
% 35.47/5.00    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3))),
% 35.47/5.00    inference(flattening,[],[f22])).
% 35.47/5.00  
% 35.47/5.00  fof(f24,plain,(
% 35.47/5.00    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => (sK1 != sK2 & r1_xboole_0(sK3,sK1) & r1_xboole_0(sK2,sK0) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3))),
% 35.47/5.00    introduced(choice_axiom,[])).
% 35.47/5.00  
% 35.47/5.00  fof(f25,plain,(
% 35.47/5.00    sK1 != sK2 & r1_xboole_0(sK3,sK1) & r1_xboole_0(sK2,sK0) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 35.47/5.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f24])).
% 35.47/5.00  
% 35.47/5.00  fof(f40,plain,(
% 35.47/5.00    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 35.47/5.00    inference(cnf_transformation,[],[f25])).
% 35.47/5.00  
% 35.47/5.00  fof(f13,axiom,(
% 35.47/5.00    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2)),
% 35.47/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.47/5.00  
% 35.47/5.00  fof(f38,plain,(
% 35.47/5.00    ( ! [X2,X0,X1] : (k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2)) )),
% 35.47/5.00    inference(cnf_transformation,[],[f13])).
% 35.47/5.00  
% 35.47/5.00  fof(f1,axiom,(
% 35.47/5.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 35.47/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.47/5.00  
% 35.47/5.00  fof(f26,plain,(
% 35.47/5.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 35.47/5.00    inference(cnf_transformation,[],[f1])).
% 35.47/5.00  
% 35.47/5.00  fof(f2,axiom,(
% 35.47/5.00    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 35.47/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.47/5.00  
% 35.47/5.00  fof(f17,plain,(
% 35.47/5.00    ! [X0,X1] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,X1) = k1_xboole_0)),
% 35.47/5.00    inference(unused_predicate_definition_removal,[],[f2])).
% 35.47/5.00  
% 35.47/5.00  fof(f18,plain,(
% 35.47/5.00    ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1))),
% 35.47/5.00    inference(ennf_transformation,[],[f17])).
% 35.47/5.00  
% 35.47/5.00  fof(f27,plain,(
% 35.47/5.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 35.47/5.00    inference(cnf_transformation,[],[f18])).
% 35.47/5.00  
% 35.47/5.00  fof(f11,axiom,(
% 35.47/5.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 35.47/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.47/5.00  
% 35.47/5.00  fof(f36,plain,(
% 35.47/5.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 35.47/5.00    inference(cnf_transformation,[],[f11])).
% 35.47/5.00  
% 35.47/5.00  fof(f44,plain,(
% 35.47/5.00    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 35.47/5.00    inference(definition_unfolding,[],[f27,f36])).
% 35.47/5.00  
% 35.47/5.00  fof(f41,plain,(
% 35.47/5.00    r1_xboole_0(sK2,sK0)),
% 35.47/5.00    inference(cnf_transformation,[],[f25])).
% 35.47/5.00  
% 35.47/5.00  fof(f10,axiom,(
% 35.47/5.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 35.47/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.47/5.00  
% 35.47/5.00  fof(f35,plain,(
% 35.47/5.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 35.47/5.00    inference(cnf_transformation,[],[f10])).
% 35.47/5.00  
% 35.47/5.00  fof(f45,plain,(
% 35.47/5.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 35.47/5.00    inference(definition_unfolding,[],[f35,f36])).
% 35.47/5.00  
% 35.47/5.00  fof(f5,axiom,(
% 35.47/5.00    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 35.47/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.47/5.00  
% 35.47/5.00  fof(f30,plain,(
% 35.47/5.00    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 35.47/5.00    inference(cnf_transformation,[],[f5])).
% 35.47/5.00  
% 35.47/5.00  fof(f7,axiom,(
% 35.47/5.00    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 35.47/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.47/5.00  
% 35.47/5.00  fof(f32,plain,(
% 35.47/5.00    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 35.47/5.00    inference(cnf_transformation,[],[f7])).
% 35.47/5.00  
% 35.47/5.00  fof(f12,axiom,(
% 35.47/5.00    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 35.47/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.47/5.00  
% 35.47/5.00  fof(f37,plain,(
% 35.47/5.00    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 35.47/5.00    inference(cnf_transformation,[],[f12])).
% 35.47/5.00  
% 35.47/5.00  fof(f14,axiom,(
% 35.47/5.00    ! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,X2))),
% 35.47/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.47/5.00  
% 35.47/5.00  fof(f39,plain,(
% 35.47/5.00    ( ! [X2,X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,X2))) )),
% 35.47/5.00    inference(cnf_transformation,[],[f14])).
% 35.47/5.00  
% 35.47/5.00  fof(f46,plain,(
% 35.47/5.00    ( ! [X2,X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(X1,X2))) )),
% 35.47/5.00    inference(definition_unfolding,[],[f39,f36])).
% 35.47/5.00  
% 35.47/5.00  fof(f6,axiom,(
% 35.47/5.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 35.47/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.47/5.00  
% 35.47/5.00  fof(f31,plain,(
% 35.47/5.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 35.47/5.00    inference(cnf_transformation,[],[f6])).
% 35.47/5.00  
% 35.47/5.00  fof(f4,axiom,(
% 35.47/5.00    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 35.47/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.47/5.00  
% 35.47/5.00  fof(f29,plain,(
% 35.47/5.00    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 35.47/5.00    inference(cnf_transformation,[],[f4])).
% 35.47/5.00  
% 35.47/5.00  fof(f3,axiom,(
% 35.47/5.00    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 35.47/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.47/5.00  
% 35.47/5.00  fof(f19,plain,(
% 35.47/5.00    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 35.47/5.00    inference(ennf_transformation,[],[f3])).
% 35.47/5.00  
% 35.47/5.00  fof(f28,plain,(
% 35.47/5.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 35.47/5.00    inference(cnf_transformation,[],[f19])).
% 35.47/5.00  
% 35.47/5.00  fof(f42,plain,(
% 35.47/5.00    r1_xboole_0(sK3,sK1)),
% 35.47/5.00    inference(cnf_transformation,[],[f25])).
% 35.47/5.00  
% 35.47/5.00  fof(f9,axiom,(
% 35.47/5.00    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 35.47/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.47/5.00  
% 35.47/5.00  fof(f21,plain,(
% 35.47/5.00    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 35.47/5.00    inference(ennf_transformation,[],[f9])).
% 35.47/5.00  
% 35.47/5.00  fof(f34,plain,(
% 35.47/5.00    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 35.47/5.00    inference(cnf_transformation,[],[f21])).
% 35.47/5.00  
% 35.47/5.00  fof(f43,plain,(
% 35.47/5.00    sK1 != sK2),
% 35.47/5.00    inference(cnf_transformation,[],[f25])).
% 35.47/5.00  
% 35.47/5.00  cnf(c_16,negated_conjecture,
% 35.47/5.00      ( k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
% 35.47/5.00      inference(cnf_transformation,[],[f40]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_11,plain,
% 35.47/5.00      ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 35.47/5.00      inference(cnf_transformation,[],[f38]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_0,plain,
% 35.47/5.00      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 35.47/5.00      inference(cnf_transformation,[],[f26]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_198,negated_conjecture,
% 35.47/5.00      ( k2_xboole_0(sK1,sK0) = k2_xboole_0(sK2,sK3) ),
% 35.47/5.00      inference(theory_normalisation,[status(thm)],[c_16,c_11,c_0]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_1,plain,
% 35.47/5.00      ( ~ r1_xboole_0(X0,X1)
% 35.47/5.00      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 35.47/5.00      inference(cnf_transformation,[],[f44]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_15,negated_conjecture,
% 35.47/5.00      ( r1_xboole_0(sK2,sK0) ),
% 35.47/5.00      inference(cnf_transformation,[],[f41]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_133,plain,
% 35.47/5.00      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
% 35.47/5.00      | sK0 != X1
% 35.47/5.00      | sK2 != X0 ),
% 35.47/5.00      inference(resolution_lifted,[status(thm)],[c_1,c_15]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_134,plain,
% 35.47/5.00      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) = k1_xboole_0 ),
% 35.47/5.00      inference(unflattening,[status(thm)],[c_133]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_9,plain,
% 35.47/5.00      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 35.47/5.00      inference(cnf_transformation,[],[f45]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_722,plain,
% 35.47/5.00      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k1_xboole_0)) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) ),
% 35.47/5.00      inference(superposition,[status(thm)],[c_134,c_9]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_731,plain,
% 35.47/5.00      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k1_xboole_0)) = k1_xboole_0 ),
% 35.47/5.00      inference(light_normalisation,[status(thm)],[c_722,c_134]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_4,plain,
% 35.47/5.00      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 35.47/5.00      inference(cnf_transformation,[],[f30]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_732,plain,
% 35.47/5.00      ( k4_xboole_0(sK2,sK2) = k1_xboole_0 ),
% 35.47/5.00      inference(demodulation,[status(thm)],[c_731,c_4]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_6,plain,
% 35.47/5.00      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 35.47/5.00      inference(cnf_transformation,[],[f32]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_1341,plain,
% 35.47/5.00      ( k4_xboole_0(sK2,k2_xboole_0(sK2,X0)) = k4_xboole_0(k1_xboole_0,X0) ),
% 35.47/5.00      inference(superposition,[status(thm)],[c_732,c_6]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_10,plain,
% 35.47/5.00      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 35.47/5.00      inference(cnf_transformation,[],[f37]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_1347,plain,
% 35.47/5.00      ( k4_xboole_0(sK2,k2_xboole_0(sK2,X0)) = k1_xboole_0 ),
% 35.47/5.00      inference(light_normalisation,[status(thm)],[c_1341,c_10]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_2460,plain,
% 35.47/5.00      ( k4_xboole_0(sK2,k2_xboole_0(sK1,sK0)) = k1_xboole_0 ),
% 35.47/5.00      inference(superposition,[status(thm)],[c_198,c_1347]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_2582,plain,
% 35.47/5.00      ( k4_xboole_0(sK2,k2_xboole_0(k2_xboole_0(sK1,sK0),X0)) = k4_xboole_0(k1_xboole_0,X0) ),
% 35.47/5.00      inference(superposition,[status(thm)],[c_2460,c_6]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_2587,plain,
% 35.47/5.00      ( k4_xboole_0(sK2,k2_xboole_0(k2_xboole_0(sK1,sK0),X0)) = k1_xboole_0 ),
% 35.47/5.00      inference(light_normalisation,[status(thm)],[c_2582,c_10]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_12,plain,
% 35.47/5.00      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 35.47/5.00      inference(cnf_transformation,[],[f46]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_5,plain,
% 35.47/5.00      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
% 35.47/5.00      inference(cnf_transformation,[],[f31]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_607,plain,
% 35.47/5.00      ( k4_xboole_0(X0,k1_xboole_0) = k2_xboole_0(X0,k1_xboole_0) ),
% 35.47/5.00      inference(superposition,[status(thm)],[c_5,c_4]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_608,plain,
% 35.47/5.00      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 35.47/5.00      inference(light_normalisation,[status(thm)],[c_607,c_4]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_1328,plain,
% 35.47/5.00      ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
% 35.47/5.00      inference(superposition,[status(thm)],[c_608,c_0]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_2011,plain,
% 35.47/5.00      ( k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,X0) ),
% 35.47/5.00      inference(superposition,[status(thm)],[c_1328,c_5]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_2016,plain,
% 35.47/5.00      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 35.47/5.00      inference(light_normalisation,[status(thm)],[c_2011,c_10]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_2417,plain,
% 35.47/5.00      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(k1_xboole_0,X1) ),
% 35.47/5.00      inference(superposition,[status(thm)],[c_2016,c_6]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_2429,plain,
% 35.47/5.00      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
% 35.47/5.00      inference(demodulation,[status(thm)],[c_2417,c_10]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_3218,plain,
% 35.47/5.00      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k1_xboole_0 ),
% 35.47/5.00      inference(superposition,[status(thm)],[c_12,c_2429]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_33572,plain,
% 35.47/5.00      ( k4_xboole_0(k4_xboole_0(X0,sK2),k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 35.47/5.00      inference(superposition,[status(thm)],[c_2587,c_3218]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_33668,plain,
% 35.47/5.00      ( k4_xboole_0(k4_xboole_0(X0,sK2),X0) = k1_xboole_0 ),
% 35.47/5.00      inference(light_normalisation,[status(thm)],[c_33572,c_4]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_1215,plain,
% 35.47/5.00      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X2),k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1))) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,X1)) ),
% 35.47/5.00      inference(superposition,[status(thm)],[c_5,c_12]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_115691,plain,
% 35.47/5.00      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,sK2),X0),X1),k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,sK2),X0),k1_xboole_0)) = k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,sK2),X0),k4_xboole_0(X1,X0)) ),
% 35.47/5.00      inference(superposition,[status(thm)],[c_33668,c_1215]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_3,plain,
% 35.47/5.00      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 35.47/5.00      inference(cnf_transformation,[],[f29]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_352,plain,
% 35.47/5.00      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 35.47/5.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_2,plain,
% 35.47/5.00      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 35.47/5.00      inference(cnf_transformation,[],[f28]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_353,plain,
% 35.47/5.00      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 35.47/5.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_1719,plain,
% 35.47/5.00      ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
% 35.47/5.00      inference(superposition,[status(thm)],[c_352,c_353]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_2421,plain,
% 35.47/5.00      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k1_xboole_0)) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 35.47/5.00      inference(superposition,[status(thm)],[c_2016,c_12]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_2428,plain,
% 35.47/5.00      ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
% 35.47/5.00      inference(light_normalisation,[status(thm)],[c_2421,c_4,c_1719]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_1199,plain,
% 35.47/5.00      ( k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,X1)) ),
% 35.47/5.00      inference(superposition,[status(thm)],[c_4,c_12]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_1256,plain,
% 35.47/5.00      ( k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
% 35.47/5.00      inference(demodulation,[status(thm)],[c_1199,c_4,c_10]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_7057,plain,
% 35.47/5.00      ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 35.47/5.00      inference(superposition,[status(thm)],[c_9,c_1256]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_360,plain,
% 35.47/5.00      ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,k2_xboole_0(X2,X0)) ),
% 35.47/5.00      inference(superposition,[status(thm)],[c_11,c_0]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_7190,plain,
% 35.47/5.00      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X0)) = k2_xboole_0(X2,X0) ),
% 35.47/5.00      inference(superposition,[status(thm)],[c_7057,c_360]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_116108,plain,
% 35.47/5.00      ( k2_xboole_0(k4_xboole_0(X0,sK2),X0) = X0 ),
% 35.47/5.00      inference(demodulation,
% 35.47/5.00                [status(thm)],
% 35.47/5.00                [c_115691,c_4,c_1719,c_2428,c_7190]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_604,plain,
% 35.47/5.00      ( k4_xboole_0(k2_xboole_0(sK1,sK0),sK3) = k4_xboole_0(sK2,sK3) ),
% 35.47/5.00      inference(superposition,[status(thm)],[c_198,c_5]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_812,plain,
% 35.47/5.00      ( k4_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK3,X0)) = k4_xboole_0(k4_xboole_0(sK2,sK3),X0) ),
% 35.47/5.00      inference(superposition,[status(thm)],[c_604,c_6]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_815,plain,
% 35.47/5.00      ( k4_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK3,X0)) = k4_xboole_0(sK2,k2_xboole_0(sK3,X0)) ),
% 35.47/5.00      inference(demodulation,[status(thm)],[c_812,c_6]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_14,negated_conjecture,
% 35.47/5.00      ( r1_xboole_0(sK3,sK1) ),
% 35.47/5.00      inference(cnf_transformation,[],[f42]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_128,plain,
% 35.47/5.00      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
% 35.47/5.00      | sK3 != X0
% 35.47/5.00      | sK1 != X1 ),
% 35.47/5.00      inference(resolution_lifted,[status(thm)],[c_1,c_14]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_129,plain,
% 35.47/5.00      ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)) = k1_xboole_0 ),
% 35.47/5.00      inference(unflattening,[status(thm)],[c_128]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_715,plain,
% 35.47/5.00      ( k4_xboole_0(sK3,k1_xboole_0) = k4_xboole_0(sK3,sK1) ),
% 35.47/5.00      inference(superposition,[status(thm)],[c_129,c_9]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_742,plain,
% 35.47/5.00      ( k4_xboole_0(sK3,sK1) = sK3 ),
% 35.47/5.00      inference(demodulation,[status(thm)],[c_715,c_4]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_2585,plain,
% 35.47/5.00      ( k4_xboole_0(sK2,k4_xboole_0(X0,k2_xboole_0(sK1,sK0))) = k2_xboole_0(k4_xboole_0(sK2,X0),k4_xboole_0(sK2,k1_xboole_0)) ),
% 35.47/5.00      inference(superposition,[status(thm)],[c_2460,c_12]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_1212,plain,
% 35.47/5.00      ( k4_xboole_0(sK2,k4_xboole_0(X0,sK0)) = k2_xboole_0(k4_xboole_0(sK2,X0),k1_xboole_0) ),
% 35.47/5.00      inference(superposition,[status(thm)],[c_134,c_12]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_1240,plain,
% 35.47/5.00      ( k4_xboole_0(sK2,k4_xboole_0(X0,sK0)) = k4_xboole_0(sK2,X0) ),
% 35.47/5.00      inference(demodulation,[status(thm)],[c_1212,c_608]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_2132,plain,
% 35.47/5.00      ( k4_xboole_0(sK2,k4_xboole_0(X0,k2_xboole_0(X1,sK0))) = k4_xboole_0(sK2,k4_xboole_0(X0,X1)) ),
% 35.47/5.00      inference(superposition,[status(thm)],[c_6,c_1240]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_2586,plain,
% 35.47/5.00      ( k4_xboole_0(sK2,k4_xboole_0(X0,sK1)) = sK2 ),
% 35.47/5.00      inference(demodulation,[status(thm)],[c_2585,c_4,c_1719,c_2132]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_2786,plain,
% 35.47/5.00      ( k4_xboole_0(sK2,k2_xboole_0(k4_xboole_0(X0,sK1),X1)) = k4_xboole_0(sK2,X1) ),
% 35.47/5.00      inference(superposition,[status(thm)],[c_2586,c_6]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_28255,plain,
% 35.47/5.00      ( k4_xboole_0(sK2,k2_xboole_0(sK3,X0)) = k4_xboole_0(sK2,X0) ),
% 35.47/5.00      inference(superposition,[status(thm)],[c_742,c_2786]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_33122,plain,
% 35.47/5.00      ( k4_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK3,X0)) = k4_xboole_0(sK2,X0) ),
% 35.47/5.00      inference(light_normalisation,[status(thm)],[c_815,c_815,c_28255]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_718,plain,
% 35.47/5.00      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1))) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
% 35.47/5.00      inference(superposition,[status(thm)],[c_5,c_9]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_739,plain,
% 35.47/5.00      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 35.47/5.00      inference(light_normalisation,[status(thm)],[c_718,c_5]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_33154,plain,
% 35.47/5.00      ( k4_xboole_0(k2_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK3,X0)),k4_xboole_0(k2_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK3,X0)),k4_xboole_0(sK2,X0))) = k4_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK3,X0)) ),
% 35.47/5.00      inference(superposition,[status(thm)],[c_33122,c_739]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_33214,plain,
% 35.47/5.00      ( k4_xboole_0(k2_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK3,X0)),k4_xboole_0(k2_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK3,X0)),k4_xboole_0(sK2,X0))) = k4_xboole_0(sK2,X0) ),
% 35.47/5.00      inference(demodulation,[status(thm)],[c_33154,c_33122]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_8,plain,
% 35.47/5.00      ( r1_tarski(X0,k2_xboole_0(X1,X2))
% 35.47/5.00      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ),
% 35.47/5.00      inference(cnf_transformation,[],[f34]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_350,plain,
% 35.47/5.00      ( r1_tarski(X0,k2_xboole_0(X1,X2)) = iProver_top
% 35.47/5.00      | r1_tarski(k4_xboole_0(X0,X1),X2) != iProver_top ),
% 35.47/5.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_585,plain,
% 35.47/5.00      ( r1_tarski(X0,k2_xboole_0(X1,X0)) = iProver_top ),
% 35.47/5.00      inference(superposition,[status(thm)],[c_352,c_350]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_5778,plain,
% 35.47/5.00      ( r1_tarski(sK3,k2_xboole_0(sK1,sK0)) = iProver_top ),
% 35.47/5.00      inference(superposition,[status(thm)],[c_198,c_585]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_6300,plain,
% 35.47/5.00      ( k2_xboole_0(sK3,k2_xboole_0(sK1,sK0)) = k2_xboole_0(sK1,sK0) ),
% 35.47/5.00      inference(superposition,[status(thm)],[c_5778,c_353]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_359,plain,
% 35.47/5.00      ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X2,k2_xboole_0(X1,X0)) ),
% 35.47/5.00      inference(superposition,[status(thm)],[c_11,c_0]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_3007,plain,
% 35.47/5.00      ( k2_xboole_0(sK3,k2_xboole_0(sK2,X0)) = k2_xboole_0(X0,k2_xboole_0(sK1,sK0)) ),
% 35.47/5.00      inference(superposition,[status(thm)],[c_198,c_359]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_3542,plain,
% 35.47/5.00      ( k2_xboole_0(k2_xboole_0(sK2,X0),k2_xboole_0(sK3,X1)) = k2_xboole_0(X1,k2_xboole_0(X0,k2_xboole_0(sK1,sK0))) ),
% 35.47/5.00      inference(superposition,[status(thm)],[c_3007,c_359]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_6428,plain,
% 35.47/5.00      ( k2_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK3,X0)) = k2_xboole_0(X0,k2_xboole_0(sK1,sK0)) ),
% 35.47/5.00      inference(superposition,[status(thm)],[c_6300,c_3542]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_6444,plain,
% 35.47/5.00      ( k2_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK3,X0)) = k2_xboole_0(X0,k2_xboole_0(sK1,sK0)) ),
% 35.47/5.00      inference(light_normalisation,[status(thm)],[c_6428,c_198]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_33215,plain,
% 35.47/5.00      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK1,sK0)),k4_xboole_0(sK2,X0))) = k4_xboole_0(sK2,X0) ),
% 35.47/5.00      inference(light_normalisation,[status(thm)],[c_33214,c_6444]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_118363,plain,
% 35.47/5.00      ( k4_xboole_0(k2_xboole_0(sK1,sK0),k4_xboole_0(k2_xboole_0(sK1,sK0),k4_xboole_0(sK2,k4_xboole_0(k2_xboole_0(sK1,sK0),sK2)))) = k4_xboole_0(sK2,k4_xboole_0(k2_xboole_0(sK1,sK0),sK2)) ),
% 35.47/5.00      inference(superposition,[status(thm)],[c_116108,c_33215]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_3541,plain,
% 35.47/5.00      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK1,sK0)),k2_xboole_0(sK2,X0)) = k4_xboole_0(sK3,k2_xboole_0(sK2,X0)) ),
% 35.47/5.00      inference(superposition,[status(thm)],[c_3007,c_5]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_3969,plain,
% 35.47/5.00      ( k4_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK2,k1_xboole_0)) = k4_xboole_0(sK3,k2_xboole_0(sK2,k1_xboole_0)) ),
% 35.47/5.00      inference(superposition,[status(thm)],[c_1328,c_3541]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_3993,plain,
% 35.47/5.00      ( k4_xboole_0(k2_xboole_0(sK1,sK0),sK2) = k4_xboole_0(sK3,sK2) ),
% 35.47/5.00      inference(demodulation,[status(thm)],[c_3969,c_608]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_33135,plain,
% 35.47/5.00      ( k4_xboole_0(k2_xboole_0(sK1,sK0),sK3) = k4_xboole_0(sK2,k1_xboole_0) ),
% 35.47/5.00      inference(superposition,[status(thm)],[c_608,c_33122]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_33233,plain,
% 35.47/5.00      ( k4_xboole_0(k2_xboole_0(sK1,sK0),sK3) = sK2 ),
% 35.47/5.00      inference(demodulation,[status(thm)],[c_33135,c_4,c_604]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_1200,plain,
% 35.47/5.00      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),X2))) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X2)) ),
% 35.47/5.00      inference(superposition,[status(thm)],[c_5,c_12]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_106153,plain,
% 35.47/5.00      ( k2_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(k2_xboole_0(sK1,sK0),sK2)) = k4_xboole_0(k2_xboole_0(sK1,sK0),k4_xboole_0(sK0,sK3)) ),
% 35.47/5.00      inference(superposition,[status(thm)],[c_33233,c_1200]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_106647,plain,
% 35.47/5.00      ( k4_xboole_0(k2_xboole_0(sK1,sK0),k4_xboole_0(sK0,sK3)) = k2_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(sK3,sK2)) ),
% 35.47/5.00      inference(light_normalisation,[status(thm)],[c_106153,c_3993]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_716,plain,
% 35.47/5.00      ( k4_xboole_0(sK2,k1_xboole_0) = k4_xboole_0(sK2,sK0) ),
% 35.47/5.00      inference(superposition,[status(thm)],[c_134,c_9]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_741,plain,
% 35.47/5.00      ( k4_xboole_0(sK2,sK0) = sK2 ),
% 35.47/5.00      inference(demodulation,[status(thm)],[c_716,c_4]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_721,plain,
% 35.47/5.00      ( k4_xboole_0(sK3,k4_xboole_0(sK3,k1_xboole_0)) = k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)) ),
% 35.47/5.00      inference(superposition,[status(thm)],[c_129,c_9]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_733,plain,
% 35.47/5.00      ( k4_xboole_0(sK3,k4_xboole_0(sK3,k1_xboole_0)) = k1_xboole_0 ),
% 35.47/5.00      inference(light_normalisation,[status(thm)],[c_721,c_129]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_734,plain,
% 35.47/5.00      ( k4_xboole_0(sK3,sK3) = k1_xboole_0 ),
% 35.47/5.00      inference(demodulation,[status(thm)],[c_733,c_4]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_1869,plain,
% 35.47/5.00      ( k4_xboole_0(sK3,k2_xboole_0(sK3,X0)) = k4_xboole_0(k1_xboole_0,X0) ),
% 35.47/5.00      inference(superposition,[status(thm)],[c_734,c_6]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_1875,plain,
% 35.47/5.00      ( k4_xboole_0(sK3,k2_xboole_0(sK3,X0)) = k1_xboole_0 ),
% 35.47/5.00      inference(light_normalisation,[status(thm)],[c_1869,c_10]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_2486,plain,
% 35.47/5.00      ( k4_xboole_0(sK3,k2_xboole_0(X0,sK3)) = k1_xboole_0 ),
% 35.47/5.00      inference(superposition,[status(thm)],[c_0,c_1875]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_3385,plain,
% 35.47/5.00      ( k4_xboole_0(sK3,k2_xboole_0(sK1,sK0)) = k1_xboole_0 ),
% 35.47/5.00      inference(superposition,[status(thm)],[c_198,c_2486]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_3511,plain,
% 35.47/5.00      ( k4_xboole_0(sK3,k4_xboole_0(X0,k2_xboole_0(sK1,sK0))) = k2_xboole_0(k4_xboole_0(sK3,X0),k4_xboole_0(sK3,k1_xboole_0)) ),
% 35.47/5.00      inference(superposition,[status(thm)],[c_3385,c_12]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_1211,plain,
% 35.47/5.00      ( k4_xboole_0(sK3,k4_xboole_0(X0,sK1)) = k2_xboole_0(k4_xboole_0(sK3,X0),k1_xboole_0) ),
% 35.47/5.00      inference(superposition,[status(thm)],[c_129,c_12]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_1241,plain,
% 35.47/5.00      ( k4_xboole_0(sK3,k4_xboole_0(X0,sK1)) = k4_xboole_0(sK3,X0) ),
% 35.47/5.00      inference(demodulation,[status(thm)],[c_1211,c_608]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_2257,plain,
% 35.47/5.00      ( k2_xboole_0(k4_xboole_0(sK3,X0),k4_xboole_0(sK3,k4_xboole_0(sK3,X1))) = k4_xboole_0(sK3,k4_xboole_0(k4_xboole_0(X0,sK1),X1)) ),
% 35.47/5.00      inference(superposition,[status(thm)],[c_1241,c_12]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_2268,plain,
% 35.47/5.00      ( k4_xboole_0(sK3,k4_xboole_0(X0,k2_xboole_0(sK1,X1))) = k4_xboole_0(sK3,k4_xboole_0(X0,X1)) ),
% 35.47/5.00      inference(demodulation,[status(thm)],[c_2257,c_6,c_12]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_3513,plain,
% 35.47/5.00      ( k4_xboole_0(sK3,k4_xboole_0(X0,sK0)) = sK3 ),
% 35.47/5.00      inference(demodulation,[status(thm)],[c_3511,c_4,c_1719,c_2268]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_4608,plain,
% 35.47/5.00      ( k4_xboole_0(sK3,sK2) = sK3 ),
% 35.47/5.00      inference(superposition,[status(thm)],[c_741,c_3513]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_1221,plain,
% 35.47/5.00      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(sK1,sK0),X0),k4_xboole_0(k2_xboole_0(sK1,sK0),k4_xboole_0(sK2,sK3))) = k4_xboole_0(k2_xboole_0(sK1,sK0),k4_xboole_0(X0,sK3)) ),
% 35.47/5.00      inference(superposition,[status(thm)],[c_604,c_12]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_33176,plain,
% 35.47/5.00      ( k2_xboole_0(k4_xboole_0(sK2,X0),k4_xboole_0(k2_xboole_0(sK1,sK0),k4_xboole_0(sK2,sK3))) = k4_xboole_0(k2_xboole_0(sK1,sK0),k4_xboole_0(k2_xboole_0(sK3,X0),sK3)) ),
% 35.47/5.00      inference(superposition,[status(thm)],[c_33122,c_1221]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_2782,plain,
% 35.47/5.00      ( k4_xboole_0(sK2,sK3) = sK2 ),
% 35.47/5.00      inference(superposition,[status(thm)],[c_742,c_2586]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_33194,plain,
% 35.47/5.00      ( k4_xboole_0(k2_xboole_0(sK1,sK0),k4_xboole_0(k2_xboole_0(sK3,X0),sK3)) = k2_xboole_0(k4_xboole_0(sK2,X0),k4_xboole_0(sK3,sK2)) ),
% 35.47/5.00      inference(light_normalisation,
% 35.47/5.00                [status(thm)],
% 35.47/5.00                [c_33176,c_2782,c_3993]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_602,plain,
% 35.47/5.00      ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(X1,X0) ),
% 35.47/5.00      inference(superposition,[status(thm)],[c_0,c_5]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_33195,plain,
% 35.47/5.00      ( k4_xboole_0(k2_xboole_0(sK1,sK0),k4_xboole_0(X0,sK3)) = k2_xboole_0(k4_xboole_0(sK2,X0),sK3) ),
% 35.47/5.00      inference(demodulation,[status(thm)],[c_33194,c_602,c_4608]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_106648,plain,
% 35.47/5.00      ( k2_xboole_0(k4_xboole_0(sK1,sK0),sK3) = k2_xboole_0(sK1,sK0) ),
% 35.47/5.00      inference(demodulation,
% 35.47/5.00                [status(thm)],
% 35.47/5.00                [c_106647,c_198,c_741,c_4608,c_33195]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_108890,plain,
% 35.47/5.00      ( k2_xboole_0(sK3,k4_xboole_0(sK1,sK0)) = k2_xboole_0(sK1,sK0) ),
% 35.47/5.00      inference(superposition,[status(thm)],[c_106648,c_0]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_6683,plain,
% 35.47/5.00      ( k2_xboole_0(sK1,k2_xboole_0(sK0,k2_xboole_0(sK3,X0))) = k2_xboole_0(X0,k2_xboole_0(sK1,sK0)) ),
% 35.47/5.00      inference(superposition,[status(thm)],[c_6444,c_11]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_109078,plain,
% 35.47/5.00      ( k2_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(sK1,sK0)) = k2_xboole_0(sK1,k2_xboole_0(sK0,k2_xboole_0(sK1,sK0))) ),
% 35.47/5.00      inference(superposition,[status(thm)],[c_108890,c_6683]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_807,plain,
% 35.47/5.00      ( k2_xboole_0(sK2,k2_xboole_0(sK3,X0)) = k2_xboole_0(k2_xboole_0(sK1,sK0),X0) ),
% 35.47/5.00      inference(superposition,[status(thm)],[c_198,c_11]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_876,plain,
% 35.47/5.00      ( k2_xboole_0(sK1,k2_xboole_0(sK0,X0)) = k2_xboole_0(sK2,k2_xboole_0(sK3,X0)) ),
% 35.47/5.00      inference(superposition,[status(thm)],[c_807,c_11]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_7194,plain,
% 35.47/5.00      ( k2_xboole_0(sK1,k2_xboole_0(sK0,k4_xboole_0(sK3,X0))) = k2_xboole_0(sK2,sK3) ),
% 35.47/5.00      inference(superposition,[status(thm)],[c_7057,c_876]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_7209,plain,
% 35.47/5.00      ( k2_xboole_0(sK1,k2_xboole_0(sK0,k4_xboole_0(sK3,X0))) = k2_xboole_0(sK1,sK0) ),
% 35.47/5.00      inference(light_normalisation,[status(thm)],[c_7194,c_198]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_7579,plain,
% 35.47/5.00      ( k2_xboole_0(k2_xboole_0(sK0,k4_xboole_0(sK3,X0)),k2_xboole_0(sK1,X1)) = k2_xboole_0(X1,k2_xboole_0(sK1,sK0)) ),
% 35.47/5.00      inference(superposition,[status(thm)],[c_7209,c_359]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_358,plain,
% 35.47/5.00      ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
% 35.47/5.00      inference(superposition,[status(thm)],[c_11,c_0]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_3548,plain,
% 35.47/5.00      ( k2_xboole_0(sK3,k2_xboole_0(X0,k2_xboole_0(sK2,X1))) = k2_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(sK1,sK0))) ),
% 35.47/5.00      inference(superposition,[status(thm)],[c_3007,c_358]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_6435,plain,
% 35.47/5.00      ( k2_xboole_0(sK3,k2_xboole_0(X0,k2_xboole_0(sK2,sK3))) = k2_xboole_0(X0,k2_xboole_0(sK1,sK0)) ),
% 35.47/5.00      inference(superposition,[status(thm)],[c_6300,c_3548]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_6438,plain,
% 35.47/5.00      ( k2_xboole_0(sK3,k2_xboole_0(X0,k2_xboole_0(sK1,sK0))) = k2_xboole_0(X0,k2_xboole_0(sK1,sK0)) ),
% 35.47/5.00      inference(light_normalisation,[status(thm)],[c_6435,c_198]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_11301,plain,
% 35.47/5.00      ( k2_xboole_0(k2_xboole_0(sK0,k4_xboole_0(sK3,X0)),k2_xboole_0(sK1,sK0)) = k2_xboole_0(sK3,k2_xboole_0(sK0,k2_xboole_0(sK1,sK0))) ),
% 35.47/5.00      inference(superposition,[status(thm)],[c_7579,c_6438]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_11347,plain,
% 35.47/5.00      ( k2_xboole_0(sK3,k2_xboole_0(sK0,k2_xboole_0(sK1,sK0))) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK0)) ),
% 35.47/5.00      inference(demodulation,[status(thm)],[c_11301,c_7579]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_512,plain,
% 35.47/5.00      ( r1_tarski(X0,X0) = iProver_top ),
% 35.47/5.00      inference(superposition,[status(thm)],[c_4,c_352]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_1721,plain,
% 35.47/5.00      ( k2_xboole_0(X0,X0) = X0 ),
% 35.47/5.00      inference(superposition,[status(thm)],[c_512,c_353]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_874,plain,
% 35.47/5.00      ( k2_xboole_0(X0,k2_xboole_0(sK1,sK0)) = k2_xboole_0(sK2,k2_xboole_0(sK3,X0)) ),
% 35.47/5.00      inference(superposition,[status(thm)],[c_807,c_0]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_3038,plain,
% 35.47/5.00      ( k2_xboole_0(sK0,k2_xboole_0(sK1,X0)) = k2_xboole_0(sK2,k2_xboole_0(sK3,X0)) ),
% 35.47/5.00      inference(superposition,[status(thm)],[c_359,c_874]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_2393,plain,
% 35.47/5.00      ( k2_xboole_0(sK1,k2_xboole_0(X0,sK0)) = k2_xboole_0(sK2,k2_xboole_0(sK3,X0)) ),
% 35.47/5.00      inference(superposition,[status(thm)],[c_358,c_874]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_3040,plain,
% 35.47/5.00      ( k2_xboole_0(sK0,k2_xboole_0(sK1,X0)) = k2_xboole_0(sK1,k2_xboole_0(X0,sK0)) ),
% 35.47/5.00      inference(light_normalisation,[status(thm)],[c_3038,c_2393]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_3565,plain,
% 35.47/5.00      ( k2_xboole_0(sK3,k2_xboole_0(sK2,k2_xboole_0(X0,X1))) = k2_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(sK1,sK0))) ),
% 35.47/5.00      inference(superposition,[status(thm)],[c_3007,c_11]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_6434,plain,
% 35.47/5.00      ( k2_xboole_0(sK3,k2_xboole_0(sK2,k2_xboole_0(X0,sK3))) = k2_xboole_0(X0,k2_xboole_0(sK1,sK0)) ),
% 35.47/5.00      inference(superposition,[status(thm)],[c_6300,c_3565]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_1022,plain,
% 35.47/5.00      ( k2_xboole_0(sK2,k2_xboole_0(X0,sK3)) = k2_xboole_0(sK1,k2_xboole_0(sK0,X0)) ),
% 35.47/5.00      inference(superposition,[status(thm)],[c_0,c_876]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_6439,plain,
% 35.47/5.00      ( k2_xboole_0(sK3,k2_xboole_0(sK1,k2_xboole_0(sK0,X0))) = k2_xboole_0(X0,k2_xboole_0(sK1,sK0)) ),
% 35.47/5.00      inference(light_normalisation,[status(thm)],[c_6434,c_1022]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_11348,plain,
% 35.47/5.00      ( k2_xboole_0(sK0,k2_xboole_0(sK1,sK0)) = k2_xboole_0(sK1,sK0) ),
% 35.47/5.00      inference(demodulation,
% 35.47/5.00                [status(thm)],
% 35.47/5.00                [c_11347,c_1721,c_3040,c_6438,c_6439]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_808,plain,
% 35.47/5.00      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),X2) = k4_xboole_0(k2_xboole_0(X0,X1),X2) ),
% 35.47/5.00      inference(superposition,[status(thm)],[c_11,c_5]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_29637,plain,
% 35.47/5.00      ( k4_xboole_0(k2_xboole_0(sK3,sK1),sK0) = k4_xboole_0(k2_xboole_0(sK1,sK0),sK0) ),
% 35.47/5.00      inference(superposition,[status(thm)],[c_6300,c_808]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_29903,plain,
% 35.47/5.00      ( k4_xboole_0(k2_xboole_0(sK3,sK1),sK0) = k4_xboole_0(sK1,sK0) ),
% 35.47/5.00      inference(demodulation,[status(thm)],[c_29637,c_5]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_6676,plain,
% 35.47/5.00      ( k2_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(k2_xboole_0(sK3,X0),X1)) = k2_xboole_0(X1,k2_xboole_0(X0,k2_xboole_0(sK1,sK0))) ),
% 35.47/5.00      inference(superposition,[status(thm)],[c_6444,c_360]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_31643,plain,
% 35.47/5.00      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(sK3,X0),X1),k2_xboole_0(X0,k2_xboole_0(sK1,sK0))) = k2_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK3,X0)) ),
% 35.47/5.00      inference(superposition,[status(thm)],[c_7057,c_6676]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_31795,plain,
% 35.47/5.00      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(sK3,X0),X1),k2_xboole_0(X0,k2_xboole_0(sK1,sK0))) = k2_xboole_0(X0,k2_xboole_0(sK1,sK0)) ),
% 35.47/5.00      inference(light_normalisation,[status(thm)],[c_31643,c_6444]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_37028,plain,
% 35.47/5.00      ( k2_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(sK1,k2_xboole_0(sK1,sK0))) = k2_xboole_0(sK1,k2_xboole_0(sK1,sK0)) ),
% 35.47/5.00      inference(superposition,[status(thm)],[c_29903,c_31795]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_11513,plain,
% 35.47/5.00      ( k2_xboole_0(sK3,k2_xboole_0(sK2,sK0)) = k2_xboole_0(sK1,sK0) ),
% 35.47/5.00      inference(superposition,[status(thm)],[c_11348,c_3007]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_11719,plain,
% 35.47/5.00      ( k2_xboole_0(k2_xboole_0(sK2,sK0),k2_xboole_0(sK1,sK0)) = k2_xboole_0(sK1,k2_xboole_0(sK0,k2_xboole_0(sK1,sK0))) ),
% 35.47/5.00      inference(superposition,[status(thm)],[c_11513,c_6683]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_11720,plain,
% 35.47/5.00      ( k2_xboole_0(k2_xboole_0(sK2,sK0),k2_xboole_0(sK1,sK0)) = k2_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK1,sK0)) ),
% 35.47/5.00      inference(superposition,[status(thm)],[c_11513,c_6444]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_6658,plain,
% 35.47/5.00      ( k2_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK2,k2_xboole_0(sK3,sK3))) = k2_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK1,sK0)) ),
% 35.47/5.00      inference(superposition,[status(thm)],[c_874,c_6444]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_6684,plain,
% 35.47/5.00      ( k2_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(X0,k2_xboole_0(sK3,X1))) = k2_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(sK1,sK0))) ),
% 35.47/5.00      inference(superposition,[status(thm)],[c_6444,c_358]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_6709,plain,
% 35.47/5.00      ( k2_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK1,sK0)) = k2_xboole_0(sK2,k2_xboole_0(sK3,k2_xboole_0(sK1,sK0))) ),
% 35.47/5.00      inference(demodulation,[status(thm)],[c_6658,c_6684]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_814,plain,
% 35.47/5.00      ( r1_tarski(k4_xboole_0(sK2,sK3),k2_xboole_0(sK1,sK0)) = iProver_top ),
% 35.47/5.00      inference(superposition,[status(thm)],[c_604,c_352]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_962,plain,
% 35.47/5.00      ( r1_tarski(sK2,k2_xboole_0(sK3,k2_xboole_0(sK1,sK0))) = iProver_top ),
% 35.47/5.00      inference(superposition,[status(thm)],[c_814,c_350]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_2127,plain,
% 35.47/5.00      ( k2_xboole_0(sK2,k2_xboole_0(sK3,k2_xboole_0(sK1,sK0))) = k2_xboole_0(sK3,k2_xboole_0(sK1,sK0)) ),
% 35.47/5.00      inference(superposition,[status(thm)],[c_962,c_353]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_6710,plain,
% 35.47/5.00      ( k2_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK1,sK0)) = k2_xboole_0(sK1,sK0) ),
% 35.47/5.00      inference(light_normalisation,[status(thm)],[c_6709,c_2127,c_6300]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_11730,plain,
% 35.47/5.00      ( k2_xboole_0(k2_xboole_0(sK2,sK0),k2_xboole_0(sK1,sK0)) = k2_xboole_0(sK1,sK0) ),
% 35.47/5.00      inference(light_normalisation,[status(thm)],[c_11720,c_6710]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_11731,plain,
% 35.47/5.00      ( k2_xboole_0(sK1,k2_xboole_0(sK0,k2_xboole_0(sK1,sK0))) = k2_xboole_0(sK1,sK0) ),
% 35.47/5.00      inference(demodulation,[status(thm)],[c_11719,c_11730]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_11732,plain,
% 35.47/5.00      ( k2_xboole_0(sK1,k2_xboole_0(sK1,sK0)) = k2_xboole_0(sK1,sK0) ),
% 35.47/5.00      inference(light_normalisation,[status(thm)],[c_11731,c_11348]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_37195,plain,
% 35.47/5.00      ( k2_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(sK1,sK0)) = k2_xboole_0(sK1,sK0) ),
% 35.47/5.00      inference(light_normalisation,[status(thm)],[c_37028,c_11732]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_7180,plain,
% 35.47/5.00      ( k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k2_xboole_0(X0,X2) ),
% 35.47/5.00      inference(superposition,[status(thm)],[c_7057,c_11]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_108926,plain,
% 35.47/5.00      ( k2_xboole_0(sK1,k2_xboole_0(sK1,sK0)) = k2_xboole_0(sK1,sK3) ),
% 35.47/5.00      inference(superposition,[status(thm)],[c_106648,c_7180]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_109100,plain,
% 35.47/5.00      ( k2_xboole_0(sK1,sK3) = k2_xboole_0(sK1,sK0) ),
% 35.47/5.00      inference(light_normalisation,
% 35.47/5.00                [status(thm)],
% 35.47/5.00                [c_109078,c_11348,c_37195,c_108926]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_118669,plain,
% 35.47/5.00      ( k4_xboole_0(k2_xboole_0(sK1,sK3),k4_xboole_0(k2_xboole_0(sK1,sK3),k4_xboole_0(sK2,k4_xboole_0(sK3,sK2)))) = k4_xboole_0(sK2,k4_xboole_0(sK3,sK2)) ),
% 35.47/5.00      inference(light_normalisation,
% 35.47/5.00                [status(thm)],
% 35.47/5.00                [c_118363,c_3993,c_109100]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_1995,plain,
% 35.47/5.00      ( k4_xboole_0(sK3,k2_xboole_0(sK1,X0)) = k4_xboole_0(sK3,X0) ),
% 35.47/5.00      inference(superposition,[status(thm)],[c_742,c_6]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_2784,plain,
% 35.47/5.00      ( k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(X0,sK1),X1)) = k2_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK2,X1))) ),
% 35.47/5.00      inference(superposition,[status(thm)],[c_2586,c_12]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_2797,plain,
% 35.47/5.00      ( k4_xboole_0(sK2,k4_xboole_0(X0,k2_xboole_0(sK1,X1))) = sK2 ),
% 35.47/5.00      inference(demodulation,[status(thm)],[c_2784,c_6,c_1256]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_12519,plain,
% 35.47/5.00      ( k4_xboole_0(sK2,k4_xboole_0(sK3,X0)) = sK2 ),
% 35.47/5.00      inference(superposition,[status(thm)],[c_1995,c_2797]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_1209,plain,
% 35.47/5.00      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,X2))) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
% 35.47/5.00      inference(superposition,[status(thm)],[c_9,c_12]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_110801,plain,
% 35.47/5.00      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(sK1,sK0),X0),k4_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK3,X1))) = k4_xboole_0(k2_xboole_0(sK1,sK0),k4_xboole_0(X0,k4_xboole_0(sK2,X1))) ),
% 35.47/5.00      inference(superposition,[status(thm)],[c_33122,c_1209]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_111415,plain,
% 35.47/5.00      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(sK1,sK3),X0),k4_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK3,X1))) = k4_xboole_0(k2_xboole_0(sK1,sK3),k4_xboole_0(X0,k4_xboole_0(sK2,X1))) ),
% 35.47/5.00      inference(light_normalisation,[status(thm)],[c_110801,c_109100]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_688,plain,
% 35.47/5.00      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 35.47/5.00      inference(superposition,[status(thm)],[c_5,c_6]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_702,plain,
% 35.47/5.00      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 35.47/5.00      inference(demodulation,[status(thm)],[c_688,c_6]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_111416,plain,
% 35.47/5.00      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(sK1,sK3),X0),k4_xboole_0(sK1,k2_xboole_0(sK3,X1))) = k4_xboole_0(k2_xboole_0(sK1,sK3),k4_xboole_0(X0,k4_xboole_0(sK2,X1))) ),
% 35.47/5.00      inference(demodulation,[status(thm)],[c_111415,c_702]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_3181,plain,
% 35.47/5.00      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X0),X2)) = k4_xboole_0(X0,X2) ),
% 35.47/5.00      inference(superposition,[status(thm)],[c_2428,c_6]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_30316,plain,
% 35.47/5.00      ( k4_xboole_0(sK1,k2_xboole_0(sK3,X0)) = k4_xboole_0(sK1,X0) ),
% 35.47/5.00      inference(superposition,[status(thm)],[c_742,c_3181]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_111417,plain,
% 35.47/5.00      ( k4_xboole_0(k2_xboole_0(sK1,sK3),k4_xboole_0(X0,k4_xboole_0(sK2,X1))) = k2_xboole_0(k4_xboole_0(k2_xboole_0(sK1,sK3),X0),k4_xboole_0(sK1,X1)) ),
% 35.47/5.00      inference(demodulation,[status(thm)],[c_111416,c_30316]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_108880,plain,
% 35.47/5.00      ( k2_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(sK3,X0)) = k2_xboole_0(k2_xboole_0(sK1,sK0),X0) ),
% 35.47/5.00      inference(superposition,[status(thm)],[c_106648,c_11]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_108903,plain,
% 35.47/5.00      ( k2_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(sK3,X0)) = k2_xboole_0(X0,k2_xboole_0(sK1,sK0)) ),
% 35.47/5.00      inference(superposition,[status(thm)],[c_106648,c_360]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_109444,plain,
% 35.47/5.00      ( k2_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(sK3,X0)) = k2_xboole_0(k2_xboole_0(sK1,sK3),X0) ),
% 35.47/5.00      inference(light_normalisation,
% 35.47/5.00                [status(thm)],
% 35.47/5.00                [c_108880,c_108903,c_109100]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_4331,plain,
% 35.47/5.00      ( k2_xboole_0(k2_xboole_0(sK2,X0),k2_xboole_0(X1,sK3)) = k2_xboole_0(X1,k2_xboole_0(X0,k2_xboole_0(sK1,sK0))) ),
% 35.47/5.00      inference(superposition,[status(thm)],[c_3007,c_360]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_109579,plain,
% 35.47/5.00      ( k2_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(k4_xboole_0(sK1,sK0),sK3)) = k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK1,sK0)) ),
% 35.47/5.00      inference(superposition,[status(thm)],[c_109444,c_4331]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_109639,plain,
% 35.47/5.00      ( k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK1,sK3)) = k2_xboole_0(sK1,sK0) ),
% 35.47/5.00      inference(light_normalisation,
% 35.47/5.00                [status(thm)],
% 35.47/5.00                [c_109579,c_198,c_6710,c_106648,c_109100]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_109117,plain,
% 35.47/5.00      ( k2_xboole_0(sK1,k2_xboole_0(sK1,sK3)) = k2_xboole_0(sK1,sK3) ),
% 35.47/5.00      inference(light_normalisation,
% 35.47/5.00                [status(thm)],
% 35.47/5.00                [c_108926,c_108926,c_109100]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_109161,plain,
% 35.47/5.00      ( k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK1,X0)) = k2_xboole_0(X0,k2_xboole_0(sK1,sK3)) ),
% 35.47/5.00      inference(superposition,[status(thm)],[c_109117,c_359]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_109640,plain,
% 35.47/5.00      ( k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK1,sK3)) = k2_xboole_0(sK1,sK3) ),
% 35.47/5.00      inference(demodulation,[status(thm)],[c_109639,c_109100,c_109161]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_109927,plain,
% 35.47/5.00      ( k4_xboole_0(k2_xboole_0(k2_xboole_0(sK1,sK3),sK1),sK3) = k4_xboole_0(k2_xboole_0(sK1,sK3),sK3) ),
% 35.47/5.00      inference(superposition,[status(thm)],[c_109640,c_808]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_3167,plain,
% 35.47/5.00      ( k4_xboole_0(sK1,sK3) = sK1 ),
% 35.47/5.00      inference(superposition,[status(thm)],[c_742,c_2428]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_109964,plain,
% 35.47/5.00      ( k4_xboole_0(k2_xboole_0(k2_xboole_0(sK1,sK3),sK1),sK3) = sK1 ),
% 35.47/5.00      inference(demodulation,[status(thm)],[c_109927,c_5,c_3167]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_111743,plain,
% 35.47/5.00      ( k4_xboole_0(k2_xboole_0(sK1,k2_xboole_0(sK1,sK3)),sK3) = sK1 ),
% 35.47/5.00      inference(superposition,[status(thm)],[c_0,c_109964]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_111811,plain,
% 35.47/5.00      ( k4_xboole_0(k2_xboole_0(sK1,sK3),sK3) = sK1 ),
% 35.47/5.00      inference(light_normalisation,[status(thm)],[c_111743,c_109117]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_726,plain,
% 35.47/5.00      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X2)))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 35.47/5.00      inference(superposition,[status(thm)],[c_9,c_6]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_728,plain,
% 35.47/5.00      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X2))))) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 35.47/5.00      inference(light_normalisation,[status(thm)],[c_726,c_6]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_729,plain,
% 35.47/5.00      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2)))))) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 35.47/5.00      inference(demodulation,[status(thm)],[c_728,c_6]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_108898,plain,
% 35.47/5.00      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(X0,k2_xboole_0(sK1,sK0)))))) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(sK1,sK0),sK3)) ),
% 35.47/5.00      inference(superposition,[status(thm)],[c_106648,c_729]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_108943,plain,
% 35.47/5.00      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(X0,k2_xboole_0(sK1,sK0)))))) = k4_xboole_0(X0,k2_xboole_0(sK1,sK0)) ),
% 35.47/5.00      inference(demodulation,[status(thm)],[c_108898,c_106648]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_114825,plain,
% 35.47/5.00      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(X0,k2_xboole_0(sK1,sK3)))))) = k4_xboole_0(X0,k2_xboole_0(sK1,sK3)) ),
% 35.47/5.00      inference(light_normalisation,
% 35.47/5.00                [status(thm)],
% 35.47/5.00                [c_108943,c_108943,c_109100]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_114919,plain,
% 35.47/5.00      ( k4_xboole_0(k2_xboole_0(sK1,sK0),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK1,sK3))))),sK3)) = k2_xboole_0(k4_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK1,sK3)),k4_xboole_0(k2_xboole_0(sK1,sK0),k4_xboole_0(sK2,sK3))) ),
% 35.47/5.00      inference(superposition,[status(thm)],[c_114825,c_1221]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_115099,plain,
% 35.47/5.00      ( k4_xboole_0(k2_xboole_0(sK1,sK3),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK1,sK3))))),sK3)) = k2_xboole_0(k4_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK1,sK3)),k4_xboole_0(k2_xboole_0(sK1,sK3),sK2)) ),
% 35.47/5.00      inference(light_normalisation,
% 35.47/5.00                [status(thm)],
% 35.47/5.00                [c_114919,c_2782,c_109100]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_4731,plain,
% 35.47/5.00      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(k4_xboole_0(X1,X0),X2) ),
% 35.47/5.00      inference(superposition,[status(thm)],[c_602,c_6]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_4750,plain,
% 35.47/5.00      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(X1,k2_xboole_0(X0,X2)) ),
% 35.47/5.00      inference(demodulation,[status(thm)],[c_4731,c_6]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_109022,plain,
% 35.47/5.00      ( k4_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(k4_xboole_0(sK1,sK0),X0)) = k4_xboole_0(sK3,k2_xboole_0(k4_xboole_0(sK1,sK0),X0)) ),
% 35.47/5.00      inference(superposition,[status(thm)],[c_108890,c_702]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_109279,plain,
% 35.47/5.00      ( k4_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(k4_xboole_0(sK1,sK0),X0)) = k4_xboole_0(sK3,k2_xboole_0(k4_xboole_0(sK1,sK0),X0)) ),
% 35.47/5.00      inference(light_normalisation,[status(thm)],[c_109022,c_109100]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_67738,plain,
% 35.47/5.00      ( k4_xboole_0(sK3,k2_xboole_0(k4_xboole_0(sK1,X0),X1)) = k4_xboole_0(sK3,k2_xboole_0(sK1,X1)) ),
% 35.47/5.00      inference(superposition,[status(thm)],[c_7180,c_1995]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_67828,plain,
% 35.47/5.00      ( k4_xboole_0(sK3,k2_xboole_0(k4_xboole_0(sK1,X0),X1)) = k4_xboole_0(sK3,X1) ),
% 35.47/5.00      inference(demodulation,[status(thm)],[c_67738,c_1995]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_109280,plain,
% 35.47/5.00      ( k4_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(k4_xboole_0(sK1,sK0),X0)) = k4_xboole_0(sK3,X0) ),
% 35.47/5.00      inference(demodulation,[status(thm)],[c_109279,c_67828]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_115100,plain,
% 35.47/5.00      ( k4_xboole_0(k2_xboole_0(sK1,sK3),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(sK3,k4_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK1,sK3)))),sK3)) = k2_xboole_0(k4_xboole_0(sK3,k2_xboole_0(sK1,sK3)),k4_xboole_0(k2_xboole_0(sK1,sK3),sK2)) ),
% 35.47/5.00      inference(demodulation,[status(thm)],[c_115099,c_4750,c_109280]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_7435,plain,
% 35.47/5.00      ( k2_xboole_0(k4_xboole_0(sK3,X0),k4_xboole_0(sK3,k4_xboole_0(sK3,X1))) = k4_xboole_0(sK3,k4_xboole_0(k2_xboole_0(sK1,X0),X1)) ),
% 35.47/5.00      inference(superposition,[status(thm)],[c_1995,c_12]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_7448,plain,
% 35.47/5.00      ( k4_xboole_0(sK3,k4_xboole_0(k2_xboole_0(sK1,X0),X1)) = k4_xboole_0(sK3,k4_xboole_0(X0,X1)) ),
% 35.47/5.00      inference(demodulation,[status(thm)],[c_7435,c_12]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_115101,plain,
% 35.47/5.00      ( k4_xboole_0(k2_xboole_0(sK1,sK3),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(sK3,k4_xboole_0(sK3,k2_xboole_0(sK1,sK3)))),sK3)) = k2_xboole_0(k4_xboole_0(sK3,sK3),k4_xboole_0(k2_xboole_0(sK1,sK3),sK2)) ),
% 35.47/5.00      inference(demodulation,[status(thm)],[c_115100,c_1995,c_7448]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_115102,plain,
% 35.47/5.00      ( k4_xboole_0(k2_xboole_0(sK1,sK3),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(sK3,k4_xboole_0(sK3,sK3))),sK3)) = k4_xboole_0(k2_xboole_0(sK1,sK3),sK2) ),
% 35.47/5.00      inference(demodulation,
% 35.47/5.00                [status(thm)],
% 35.47/5.00                [c_115101,c_1328,c_2016,c_2268]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_1219,plain,
% 35.47/5.00      ( k4_xboole_0(sK3,k4_xboole_0(X0,k4_xboole_0(sK3,sK1))) = k2_xboole_0(k4_xboole_0(sK3,X0),k4_xboole_0(sK3,k1_xboole_0)) ),
% 35.47/5.00      inference(superposition,[status(thm)],[c_129,c_12]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_1232,plain,
% 35.47/5.00      ( k2_xboole_0(k4_xboole_0(sK3,X0),k4_xboole_0(sK3,k1_xboole_0)) = k4_xboole_0(sK3,k4_xboole_0(X0,sK3)) ),
% 35.47/5.00      inference(light_normalisation,[status(thm)],[c_1219,c_742]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_1233,plain,
% 35.47/5.00      ( k4_xboole_0(sK3,k4_xboole_0(X0,sK3)) = k2_xboole_0(k4_xboole_0(sK3,X0),sK3) ),
% 35.47/5.00      inference(demodulation,[status(thm)],[c_1232,c_4]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_67607,plain,
% 35.47/5.00      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X2),X0) = k4_xboole_0(k2_xboole_0(X0,X2),X0) ),
% 35.47/5.00      inference(superposition,[status(thm)],[c_7180,c_602]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_67906,plain,
% 35.47/5.00      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X2),X0) = k4_xboole_0(X2,X0) ),
% 35.47/5.00      inference(demodulation,[status(thm)],[c_67607,c_602]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_112319,plain,
% 35.47/5.00      ( k2_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(sK3,X0)) = k2_xboole_0(X0,k2_xboole_0(sK1,sK3)) ),
% 35.47/5.00      inference(light_normalisation,
% 35.47/5.00                [status(thm)],
% 35.47/5.00                [c_108903,c_109100,c_109444]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_112336,plain,
% 35.47/5.00      ( k2_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(X0,sK3)) = k2_xboole_0(X0,k2_xboole_0(sK1,sK3)) ),
% 35.47/5.00      inference(superposition,[status(thm)],[c_0,c_112319]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_115103,plain,
% 35.47/5.00      ( k4_xboole_0(k2_xboole_0(sK1,sK3),k4_xboole_0(k2_xboole_0(sK1,sK3),sK3)) = k4_xboole_0(k2_xboole_0(sK1,sK3),sK2) ),
% 35.47/5.00      inference(demodulation,
% 35.47/5.00                [status(thm)],
% 35.47/5.00                [c_115102,c_1233,c_67906,c_112336]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_109020,plain,
% 35.47/5.00      ( k4_xboole_0(k2_xboole_0(sK1,sK0),k4_xboole_0(k2_xboole_0(sK1,sK0),k4_xboole_0(sK3,k4_xboole_0(sK1,sK0)))) = k4_xboole_0(sK3,k4_xboole_0(sK1,sK0)) ),
% 35.47/5.00      inference(superposition,[status(thm)],[c_108890,c_739]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_109281,plain,
% 35.47/5.00      ( k4_xboole_0(k2_xboole_0(sK1,sK3),k4_xboole_0(k2_xboole_0(sK1,sK3),k4_xboole_0(sK3,k4_xboole_0(sK1,sK0)))) = k4_xboole_0(sK3,k4_xboole_0(sK1,sK0)) ),
% 35.47/5.00      inference(light_normalisation,[status(thm)],[c_109020,c_109100]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_1993,plain,
% 35.47/5.00      ( k2_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK3,X0))) = k4_xboole_0(sK3,k4_xboole_0(sK1,X0)) ),
% 35.47/5.00      inference(superposition,[status(thm)],[c_742,c_12]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_2002,plain,
% 35.47/5.00      ( k4_xboole_0(sK3,k4_xboole_0(sK1,X0)) = sK3 ),
% 35.47/5.00      inference(demodulation,[status(thm)],[c_1993,c_1256]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_109282,plain,
% 35.47/5.00      ( k4_xboole_0(k2_xboole_0(sK1,sK3),k4_xboole_0(sK1,sK3)) = sK3 ),
% 35.47/5.00      inference(demodulation,[status(thm)],[c_109281,c_5,c_2002]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_109283,plain,
% 35.47/5.00      ( k4_xboole_0(k2_xboole_0(sK1,sK3),sK1) = sK3 ),
% 35.47/5.00      inference(light_normalisation,[status(thm)],[c_109282,c_3167]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_115104,plain,
% 35.47/5.00      ( k4_xboole_0(k2_xboole_0(sK1,sK3),sK2) = sK3 ),
% 35.47/5.00      inference(light_normalisation,
% 35.47/5.00                [status(thm)],
% 35.47/5.00                [c_115103,c_109283,c_111811]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_118670,plain,
% 35.47/5.00      ( sK2 = sK1 ),
% 35.47/5.00      inference(demodulation,
% 35.47/5.00                [status(thm)],
% 35.47/5.00                [c_118669,c_12519,c_111417,c_111811,c_115104]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_201,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_362,plain,
% 35.47/5.00      ( sK2 != X0 | sK1 != X0 | sK1 = sK2 ),
% 35.47/5.00      inference(instantiation,[status(thm)],[c_201]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_34916,plain,
% 35.47/5.00      ( sK2 != sK1 | sK1 = sK2 | sK1 != sK1 ),
% 35.47/5.00      inference(instantiation,[status(thm)],[c_362]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_200,plain,( X0 = X0 ),theory(equality) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_490,plain,
% 35.47/5.00      ( sK1 = sK1 ),
% 35.47/5.00      inference(instantiation,[status(thm)],[c_200]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(c_13,negated_conjecture,
% 35.47/5.00      ( sK1 != sK2 ),
% 35.47/5.00      inference(cnf_transformation,[],[f43]) ).
% 35.47/5.00  
% 35.47/5.00  cnf(contradiction,plain,
% 35.47/5.00      ( $false ),
% 35.47/5.00      inference(minisat,[status(thm)],[c_118670,c_34916,c_490,c_13]) ).
% 35.47/5.00  
% 35.47/5.00  
% 35.47/5.00  % SZS output end CNFRefutation for theBenchmark.p
% 35.47/5.00  
% 35.47/5.00  ------                               Statistics
% 35.47/5.00  
% 35.47/5.00  ------ General
% 35.47/5.00  
% 35.47/5.00  abstr_ref_over_cycles:                  0
% 35.47/5.00  abstr_ref_under_cycles:                 0
% 35.47/5.00  gc_basic_clause_elim:                   0
% 35.47/5.00  forced_gc_time:                         0
% 35.47/5.00  parsing_time:                           0.008
% 35.47/5.00  unif_index_cands_time:                  0.
% 35.47/5.00  unif_index_add_time:                    0.
% 35.47/5.00  orderings_time:                         0.
% 35.47/5.00  out_proof_time:                         0.017
% 35.47/5.00  total_time:                             4.102
% 35.47/5.00  num_of_symbols:                         40
% 35.47/5.00  num_of_terms:                           176485
% 35.47/5.00  
% 35.47/5.00  ------ Preprocessing
% 35.47/5.00  
% 35.47/5.00  num_of_splits:                          0
% 35.47/5.00  num_of_split_atoms:                     0
% 35.47/5.00  num_of_reused_defs:                     0
% 35.47/5.00  num_eq_ax_congr_red:                    0
% 35.47/5.00  num_of_sem_filtered_clauses:            1
% 35.47/5.00  num_of_subtypes:                        0
% 35.47/5.00  monotx_restored_types:                  0
% 35.47/5.00  sat_num_of_epr_types:                   0
% 35.47/5.00  sat_num_of_non_cyclic_types:            0
% 35.47/5.00  sat_guarded_non_collapsed_types:        0
% 35.47/5.00  num_pure_diseq_elim:                    0
% 35.47/5.00  simp_replaced_by:                       0
% 35.47/5.00  res_preprocessed:                       76
% 35.47/5.00  prep_upred:                             0
% 35.47/5.00  prep_unflattend:                        4
% 35.47/5.00  smt_new_axioms:                         0
% 35.47/5.00  pred_elim_cands:                        1
% 35.47/5.00  pred_elim:                              1
% 35.47/5.00  pred_elim_cl:                           1
% 35.47/5.00  pred_elim_cycles:                       3
% 35.47/5.00  merged_defs:                            8
% 35.47/5.00  merged_defs_ncl:                        0
% 35.47/5.00  bin_hyper_res:                          8
% 35.47/5.00  prep_cycles:                            4
% 35.47/5.00  pred_elim_time:                         0.001
% 35.47/5.00  splitting_time:                         0.
% 35.47/5.00  sem_filter_time:                        0.
% 35.47/5.00  monotx_time:                            0.
% 35.47/5.00  subtype_inf_time:                       0.
% 35.47/5.00  
% 35.47/5.00  ------ Problem properties
% 35.47/5.00  
% 35.47/5.00  clauses:                                16
% 35.47/5.00  conjectures:                            2
% 35.47/5.00  epr:                                    1
% 35.47/5.00  horn:                                   16
% 35.47/5.00  ground:                                 4
% 35.47/5.00  unary:                                  13
% 35.47/5.00  binary:                                 3
% 35.47/5.00  lits:                                   19
% 35.47/5.00  lits_eq:                                13
% 35.47/5.00  fd_pure:                                0
% 35.47/5.00  fd_pseudo:                              0
% 35.47/5.00  fd_cond:                                0
% 35.47/5.00  fd_pseudo_cond:                         0
% 35.47/5.00  ac_symbols:                             1
% 35.47/5.00  
% 35.47/5.00  ------ Propositional Solver
% 35.47/5.00  
% 35.47/5.00  prop_solver_calls:                      42
% 35.47/5.00  prop_fast_solver_calls:                 861
% 35.47/5.00  smt_solver_calls:                       0
% 35.47/5.00  smt_fast_solver_calls:                  0
% 35.47/5.00  prop_num_of_clauses:                    37449
% 35.47/5.00  prop_preprocess_simplified:             33632
% 35.47/5.00  prop_fo_subsumed:                       11
% 35.47/5.00  prop_solver_time:                       0.
% 35.47/5.00  smt_solver_time:                        0.
% 35.47/5.00  smt_fast_solver_time:                   0.
% 35.47/5.00  prop_fast_solver_time:                  0.
% 35.47/5.00  prop_unsat_core_time:                   0.005
% 35.47/5.00  
% 35.47/5.00  ------ QBF
% 35.47/5.00  
% 35.47/5.00  qbf_q_res:                              0
% 35.47/5.00  qbf_num_tautologies:                    0
% 35.47/5.00  qbf_prep_cycles:                        0
% 35.47/5.00  
% 35.47/5.00  ------ BMC1
% 35.47/5.00  
% 35.47/5.00  bmc1_current_bound:                     -1
% 35.47/5.00  bmc1_last_solved_bound:                 -1
% 35.47/5.00  bmc1_unsat_core_size:                   -1
% 35.47/5.00  bmc1_unsat_core_parents_size:           -1
% 35.47/5.00  bmc1_merge_next_fun:                    0
% 35.47/5.00  bmc1_unsat_core_clauses_time:           0.
% 35.47/5.00  
% 35.47/5.00  ------ Instantiation
% 35.47/5.00  
% 35.47/5.00  inst_num_of_clauses:                    7754
% 35.47/5.00  inst_num_in_passive:                    5906
% 35.47/5.00  inst_num_in_active:                     1716
% 35.47/5.00  inst_num_in_unprocessed:                134
% 35.47/5.00  inst_num_of_loops:                      2350
% 35.47/5.00  inst_num_of_learning_restarts:          0
% 35.47/5.00  inst_num_moves_active_passive:          626
% 35.47/5.00  inst_lit_activity:                      0
% 35.47/5.00  inst_lit_activity_moves:                3
% 35.47/5.00  inst_num_tautologies:                   0
% 35.47/5.00  inst_num_prop_implied:                  0
% 35.47/5.00  inst_num_existing_simplified:           0
% 35.47/5.00  inst_num_eq_res_simplified:             0
% 35.47/5.00  inst_num_child_elim:                    0
% 35.47/5.00  inst_num_of_dismatching_blockings:      6253
% 35.47/5.00  inst_num_of_non_proper_insts:           8042
% 35.47/5.00  inst_num_of_duplicates:                 0
% 35.47/5.00  inst_inst_num_from_inst_to_res:         0
% 35.47/5.00  inst_dismatching_checking_time:         0.
% 35.47/5.00  
% 35.47/5.00  ------ Resolution
% 35.47/5.00  
% 35.47/5.00  res_num_of_clauses:                     0
% 35.47/5.00  res_num_in_passive:                     0
% 35.47/5.00  res_num_in_active:                      0
% 35.47/5.00  res_num_of_loops:                       80
% 35.47/5.00  res_forward_subset_subsumed:            4686
% 35.47/5.00  res_backward_subset_subsumed:           4
% 35.47/5.00  res_forward_subsumed:                   0
% 35.47/5.00  res_backward_subsumed:                  0
% 35.47/5.00  res_forward_subsumption_resolution:     0
% 35.47/5.00  res_backward_subsumption_resolution:    0
% 35.47/5.00  res_clause_to_clause_subsumption:       122946
% 35.47/5.00  res_orphan_elimination:                 0
% 35.47/5.00  res_tautology_del:                      691
% 35.47/5.00  res_num_eq_res_simplified:              0
% 35.47/5.00  res_num_sel_changes:                    0
% 35.47/5.00  res_moves_from_active_to_pass:          0
% 35.47/5.00  
% 35.47/5.00  ------ Superposition
% 35.47/5.00  
% 35.47/5.00  sup_time_total:                         0.
% 35.47/5.00  sup_time_generating:                    0.
% 35.47/5.00  sup_time_sim_full:                      0.
% 35.47/5.00  sup_time_sim_immed:                     0.
% 35.47/5.00  
% 35.47/5.00  sup_num_of_clauses:                     9633
% 35.47/5.00  sup_num_in_active:                      431
% 35.47/5.00  sup_num_in_passive:                     9202
% 35.47/5.00  sup_num_of_loops:                       469
% 35.47/5.00  sup_fw_superposition:                   23695
% 35.47/5.00  sup_bw_superposition:                   14009
% 35.47/5.00  sup_immediate_simplified:               20170
% 35.47/5.00  sup_given_eliminated:                   11
% 35.47/5.00  comparisons_done:                       0
% 35.47/5.00  comparisons_avoided:                    0
% 35.47/5.00  
% 35.47/5.00  ------ Simplifications
% 35.47/5.00  
% 35.47/5.00  
% 35.47/5.00  sim_fw_subset_subsumed:                 283
% 35.47/5.00  sim_bw_subset_subsumed:                 72
% 35.47/5.00  sim_fw_subsumed:                        3207
% 35.47/5.00  sim_bw_subsumed:                        250
% 35.47/5.00  sim_fw_subsumption_res:                 0
% 35.47/5.00  sim_bw_subsumption_res:                 0
% 35.47/5.00  sim_tautology_del:                      123
% 35.47/5.00  sim_eq_tautology_del:                   3994
% 35.47/5.00  sim_eq_res_simp:                        0
% 35.47/5.00  sim_fw_demodulated:                     14851
% 35.47/5.00  sim_bw_demodulated:                     136
% 35.47/5.00  sim_light_normalised:                   9162
% 35.47/5.00  sim_joinable_taut:                      296
% 35.47/5.00  sim_joinable_simp:                      0
% 35.47/5.00  sim_ac_normalised:                      0
% 35.47/5.00  sim_smt_subsumption:                    0
% 35.47/5.00  
%------------------------------------------------------------------------------
