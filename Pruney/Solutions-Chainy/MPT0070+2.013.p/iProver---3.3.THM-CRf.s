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
% DateTime   : Thu Dec  3 11:23:16 EST 2020

% Result     : Theorem 7.89s
% Output     : CNFRefutation 7.89s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 651 expanded)
%              Number of clauses        :   70 ( 224 expanded)
%              Number of leaves         :   14 ( 177 expanded)
%              Depth                    :   33
%              Number of atoms          :  156 ( 867 expanded)
%              Number of equality atoms :  112 ( 610 expanded)
%              Maximal formula depth    :    7 (   2 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f24,f28])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_xboole_0(X1,X2)
          & r1_tarski(X0,X1) )
       => r1_xboole_0(X0,X2) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,X2)
      & r1_xboole_0(X1,X2)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,X2)
      & r1_xboole_0(X1,X2)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f17,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(X0,X2)
        & r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
   => ( ~ r1_xboole_0(sK0,sK2)
      & r1_xboole_0(sK1,sK2)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    & r1_xboole_0(sK1,sK2)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f17])).

fof(f30,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f33,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f20,f28,f28])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f38,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f29,f28])).

fof(f6,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f6])).

fof(f37,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f25,f28])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f4,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f21,f28])).

fof(f31,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f22,f28])).

fof(f32,plain,(
    ~ r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_12,negated_conjecture,
    ( r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_102,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
    | sK1 != X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_12])).

cnf(c_103,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = sK0 ),
    inference(unflattening,[status(thm)],[c_102])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_9,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_533,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0)) = X1 ),
    inference(superposition,[status(thm)],[c_1,c_9])).

cnf(c_5675,plain,
    ( k2_xboole_0(sK0,k4_xboole_0(sK1,sK0)) = sK1 ),
    inference(superposition,[status(thm)],[c_103,c_533])).

cnf(c_6,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_7,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f26])).

cnf(c_151,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_6,c_7])).

cnf(c_8,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_413,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_151,c_8])).

cnf(c_1183,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_9,c_413])).

cnf(c_5731,plain,
    ( k2_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)),X0) = X0 ),
    inference(superposition,[status(thm)],[c_7,c_533])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_6109,plain,
    ( k2_xboole_0(X0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) = X0 ),
    inference(superposition,[status(thm)],[c_5731,c_0])).

cnf(c_411,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),X0)) = k4_xboole_0(sK0,X0) ),
    inference(superposition,[status(thm)],[c_103,c_8])).

cnf(c_780,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),X0),X1)) = k4_xboole_0(k4_xboole_0(sK0,X0),X1) ),
    inference(superposition,[status(thm)],[c_411,c_8])).

cnf(c_782,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),X0),X1)) = k4_xboole_0(sK0,k2_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_780,c_8])).

cnf(c_6310,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1))),X0)) = k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),X0)) ),
    inference(superposition,[status(thm)],[c_6109,c_782])).

cnf(c_6346,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1))),X0)) = k4_xboole_0(sK0,X0) ),
    inference(light_normalisation,[status(thm)],[c_6310,c_411])).

cnf(c_7265,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1))) = k4_xboole_0(sK0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_9,c_6346])).

cnf(c_7325,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1))) = sK0 ),
    inference(demodulation,[status(thm)],[c_7265,c_7])).

cnf(c_7443,plain,
    ( k2_xboole_0(k4_xboole_0(sK0,sK0),k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1)),sK0)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_7325,c_533])).

cnf(c_4,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f23])).

cnf(c_310,plain,
    ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_4,c_0])).

cnf(c_7480,plain,
    ( k4_xboole_0(k1_xboole_0,k2_xboole_0(k4_xboole_0(sK0,sK1),sK0)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1)) ),
    inference(demodulation,[status(thm)],[c_7443,c_8,c_151,c_310])).

cnf(c_552,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
    inference(superposition,[status(thm)],[c_9,c_0])).

cnf(c_6434,plain,
    ( k2_xboole_0(k4_xboole_0(sK0,sK1),sK0) = sK0 ),
    inference(superposition,[status(thm)],[c_103,c_552])).

cnf(c_7481,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1)) = k4_xboole_0(k1_xboole_0,sK0) ),
    inference(light_normalisation,[status(thm)],[c_7480,c_6434])).

cnf(c_7890,plain,
    ( k2_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0)),k4_xboole_0(k1_xboole_0,sK0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7481,c_533])).

cnf(c_7904,plain,
    ( k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0))),k4_xboole_0(k1_xboole_0,sK0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7890,c_8])).

cnf(c_7905,plain,
    ( k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,k4_xboole_0(sK0,k2_xboole_0(sK1,k1_xboole_0)))),k4_xboole_0(k1_xboole_0,sK0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7904,c_8])).

cnf(c_420,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8,c_151])).

cnf(c_7906,plain,
    ( k4_xboole_0(k1_xboole_0,sK0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7905,c_4,c_310,c_420])).

cnf(c_9251,plain,
    ( k4_xboole_0(k1_xboole_0,k2_xboole_0(sK0,X0)) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_7906,c_8])).

cnf(c_9536,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(sK0,X0),k4_xboole_0(k2_xboole_0(sK0,X0),k1_xboole_0)),k4_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_9251,c_533])).

cnf(c_9552,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_9536,c_7,c_151,c_310])).

cnf(c_22315,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1183,c_8,c_9552])).

cnf(c_22320,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1,c_22315])).

cnf(c_22467,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k2_xboole_0(X1,X2)) = k4_xboole_0(k1_xboole_0,X2) ),
    inference(superposition,[status(thm)],[c_22320,c_8])).

cnf(c_22485,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_22467,c_8,c_9552])).

cnf(c_25345,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,sK0)),sK1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5675,c_22485])).

cnf(c_26103,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,sK0),sK1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_25345,c_8])).

cnf(c_3,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_57,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_3])).

cnf(c_11,negated_conjecture,
    ( r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_114,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
    | sK1 != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_57,c_11])).

cnf(c_115,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_114])).

cnf(c_395,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1,c_115])).

cnf(c_686,plain,
    ( k2_xboole_0(k1_xboole_0,k4_xboole_0(sK2,sK1)) = sK2 ),
    inference(superposition,[status(thm)],[c_395,c_9])).

cnf(c_1034,plain,
    ( k4_xboole_0(sK2,sK1) = sK2 ),
    inference(superposition,[status(thm)],[c_310,c_686])).

cnf(c_4626,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(sK1,X0)) = k4_xboole_0(sK2,X0) ),
    inference(superposition,[status(thm)],[c_1034,c_8])).

cnf(c_4766,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(X0,sK1)) = k4_xboole_0(sK2,X0) ),
    inference(superposition,[status(thm)],[c_0,c_4626])).

cnf(c_26741,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_26103,c_4766])).

cnf(c_136,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_192,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) ),
    inference(instantiation,[status(thm)],[c_136])).

cnf(c_193,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) != k1_xboole_0
    | k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0))
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_192])).

cnf(c_182,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_178,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) != X0
    | k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_136])).

cnf(c_181,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) != k4_xboole_0(sK2,k4_xboole_0(sK2,sK0))
    | k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k1_xboole_0
    | k1_xboole_0 != k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) ),
    inference(instantiation,[status(thm)],[c_178])).

cnf(c_135,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_140,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_135])).

cnf(c_2,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_55,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_2])).

cnf(c_10,negated_conjecture,
    ( ~ r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_109,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0
    | sK2 != X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_55,c_10])).

cnf(c_110,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_109])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_26741,c_193,c_182,c_181,c_140,c_110])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:03:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.89/1.51  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.89/1.51  
% 7.89/1.51  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.89/1.51  
% 7.89/1.51  ------  iProver source info
% 7.89/1.51  
% 7.89/1.51  git: date: 2020-06-30 10:37:57 +0100
% 7.89/1.51  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.89/1.51  git: non_committed_changes: false
% 7.89/1.51  git: last_make_outside_of_git: false
% 7.89/1.51  
% 7.89/1.51  ------ 
% 7.89/1.51  ------ Parsing...
% 7.89/1.51  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.89/1.51  
% 7.89/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 7.89/1.51  
% 7.89/1.51  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.89/1.51  
% 7.89/1.51  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.89/1.51  ------ Proving...
% 7.89/1.51  ------ Problem Properties 
% 7.89/1.51  
% 7.89/1.51  
% 7.89/1.51  clauses                                 11
% 7.89/1.51  conjectures                             0
% 7.89/1.51  EPR                                     1
% 7.89/1.51  Horn                                    11
% 7.89/1.51  unary                                   11
% 7.89/1.51  binary                                  0
% 7.89/1.51  lits                                    11
% 7.89/1.51  lits eq                                 11
% 7.89/1.51  fd_pure                                 0
% 7.89/1.51  fd_pseudo                               0
% 7.89/1.51  fd_cond                                 0
% 7.89/1.51  fd_pseudo_cond                          0
% 7.89/1.51  AC symbols                              0
% 7.89/1.51  
% 7.89/1.51  ------ Input Options Time Limit: Unbounded
% 7.89/1.51  
% 7.89/1.51  
% 7.89/1.51  ------ 
% 7.89/1.51  Current options:
% 7.89/1.51  ------ 
% 7.89/1.51  
% 7.89/1.51  
% 7.89/1.51  
% 7.89/1.51  
% 7.89/1.51  ------ Proving...
% 7.89/1.51  
% 7.89/1.51  
% 7.89/1.51  % SZS status Theorem for theBenchmark.p
% 7.89/1.51  
% 7.89/1.51  % SZS output start CNFRefutation for theBenchmark.p
% 7.89/1.51  
% 7.89/1.51  fof(f5,axiom,(
% 7.89/1.51    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 7.89/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.89/1.51  
% 7.89/1.51  fof(f13,plain,(
% 7.89/1.51    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 7.89/1.51    inference(ennf_transformation,[],[f5])).
% 7.89/1.51  
% 7.89/1.51  fof(f24,plain,(
% 7.89/1.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 7.89/1.51    inference(cnf_transformation,[],[f13])).
% 7.89/1.51  
% 7.89/1.51  fof(f9,axiom,(
% 7.89/1.51    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 7.89/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.89/1.51  
% 7.89/1.51  fof(f28,plain,(
% 7.89/1.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 7.89/1.51    inference(cnf_transformation,[],[f9])).
% 7.89/1.51  
% 7.89/1.51  fof(f36,plain,(
% 7.89/1.51    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 7.89/1.51    inference(definition_unfolding,[],[f24,f28])).
% 7.89/1.51  
% 7.89/1.51  fof(f11,conjecture,(
% 7.89/1.51    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 7.89/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.89/1.51  
% 7.89/1.51  fof(f12,negated_conjecture,(
% 7.89/1.51    ~! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 7.89/1.51    inference(negated_conjecture,[],[f11])).
% 7.89/1.51  
% 7.89/1.51  fof(f14,plain,(
% 7.89/1.51    ? [X0,X1,X2] : (~r1_xboole_0(X0,X2) & (r1_xboole_0(X1,X2) & r1_tarski(X0,X1)))),
% 7.89/1.51    inference(ennf_transformation,[],[f12])).
% 7.89/1.51  
% 7.89/1.51  fof(f15,plain,(
% 7.89/1.51    ? [X0,X1,X2] : (~r1_xboole_0(X0,X2) & r1_xboole_0(X1,X2) & r1_tarski(X0,X1))),
% 7.89/1.51    inference(flattening,[],[f14])).
% 7.89/1.51  
% 7.89/1.51  fof(f17,plain,(
% 7.89/1.51    ? [X0,X1,X2] : (~r1_xboole_0(X0,X2) & r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => (~r1_xboole_0(sK0,sK2) & r1_xboole_0(sK1,sK2) & r1_tarski(sK0,sK1))),
% 7.89/1.51    introduced(choice_axiom,[])).
% 7.89/1.51  
% 7.89/1.51  fof(f18,plain,(
% 7.89/1.51    ~r1_xboole_0(sK0,sK2) & r1_xboole_0(sK1,sK2) & r1_tarski(sK0,sK1)),
% 7.89/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f17])).
% 7.89/1.51  
% 7.89/1.51  fof(f30,plain,(
% 7.89/1.51    r1_tarski(sK0,sK1)),
% 7.89/1.51    inference(cnf_transformation,[],[f18])).
% 7.89/1.51  
% 7.89/1.51  fof(f2,axiom,(
% 7.89/1.51    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 7.89/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.89/1.51  
% 7.89/1.51  fof(f20,plain,(
% 7.89/1.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 7.89/1.51    inference(cnf_transformation,[],[f2])).
% 7.89/1.51  
% 7.89/1.51  fof(f33,plain,(
% 7.89/1.51    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 7.89/1.51    inference(definition_unfolding,[],[f20,f28,f28])).
% 7.89/1.51  
% 7.89/1.51  fof(f10,axiom,(
% 7.89/1.51    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 7.89/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.89/1.51  
% 7.89/1.51  fof(f29,plain,(
% 7.89/1.51    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 7.89/1.51    inference(cnf_transformation,[],[f10])).
% 7.89/1.51  
% 7.89/1.51  fof(f38,plain,(
% 7.89/1.51    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 7.89/1.51    inference(definition_unfolding,[],[f29,f28])).
% 7.89/1.51  
% 7.89/1.51  fof(f6,axiom,(
% 7.89/1.51    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 7.89/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.89/1.51  
% 7.89/1.51  fof(f25,plain,(
% 7.89/1.51    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 7.89/1.51    inference(cnf_transformation,[],[f6])).
% 7.89/1.51  
% 7.89/1.51  fof(f37,plain,(
% 7.89/1.51    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 7.89/1.51    inference(definition_unfolding,[],[f25,f28])).
% 7.89/1.51  
% 7.89/1.51  fof(f7,axiom,(
% 7.89/1.51    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 7.89/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.89/1.51  
% 7.89/1.51  fof(f26,plain,(
% 7.89/1.51    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 7.89/1.51    inference(cnf_transformation,[],[f7])).
% 7.89/1.51  
% 7.89/1.51  fof(f8,axiom,(
% 7.89/1.51    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 7.89/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.89/1.51  
% 7.89/1.51  fof(f27,plain,(
% 7.89/1.51    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 7.89/1.51    inference(cnf_transformation,[],[f8])).
% 7.89/1.51  
% 7.89/1.51  fof(f1,axiom,(
% 7.89/1.51    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 7.89/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.89/1.51  
% 7.89/1.51  fof(f19,plain,(
% 7.89/1.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 7.89/1.51    inference(cnf_transformation,[],[f1])).
% 7.89/1.51  
% 7.89/1.51  fof(f4,axiom,(
% 7.89/1.51    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 7.89/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.89/1.51  
% 7.89/1.51  fof(f23,plain,(
% 7.89/1.51    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 7.89/1.51    inference(cnf_transformation,[],[f4])).
% 7.89/1.51  
% 7.89/1.51  fof(f3,axiom,(
% 7.89/1.51    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 7.89/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.89/1.51  
% 7.89/1.51  fof(f16,plain,(
% 7.89/1.51    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 7.89/1.51    inference(nnf_transformation,[],[f3])).
% 7.89/1.51  
% 7.89/1.51  fof(f21,plain,(
% 7.89/1.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 7.89/1.51    inference(cnf_transformation,[],[f16])).
% 7.89/1.51  
% 7.89/1.51  fof(f35,plain,(
% 7.89/1.51    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 7.89/1.51    inference(definition_unfolding,[],[f21,f28])).
% 7.89/1.51  
% 7.89/1.51  fof(f31,plain,(
% 7.89/1.51    r1_xboole_0(sK1,sK2)),
% 7.89/1.51    inference(cnf_transformation,[],[f18])).
% 7.89/1.51  
% 7.89/1.51  fof(f22,plain,(
% 7.89/1.51    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 7.89/1.51    inference(cnf_transformation,[],[f16])).
% 7.89/1.51  
% 7.89/1.51  fof(f34,plain,(
% 7.89/1.51    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 7.89/1.51    inference(definition_unfolding,[],[f22,f28])).
% 7.89/1.51  
% 7.89/1.51  fof(f32,plain,(
% 7.89/1.51    ~r1_xboole_0(sK0,sK2)),
% 7.89/1.51    inference(cnf_transformation,[],[f18])).
% 7.89/1.51  
% 7.89/1.51  cnf(c_5,plain,
% 7.89/1.51      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 7.89/1.51      inference(cnf_transformation,[],[f36]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_12,negated_conjecture,
% 7.89/1.51      ( r1_tarski(sK0,sK1) ),
% 7.89/1.51      inference(cnf_transformation,[],[f30]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_102,plain,
% 7.89/1.51      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | sK1 != X1 | sK0 != X0 ),
% 7.89/1.51      inference(resolution_lifted,[status(thm)],[c_5,c_12]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_103,plain,
% 7.89/1.51      ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = sK0 ),
% 7.89/1.51      inference(unflattening,[status(thm)],[c_102]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_1,plain,
% 7.89/1.51      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 7.89/1.51      inference(cnf_transformation,[],[f33]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_9,plain,
% 7.89/1.51      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
% 7.89/1.51      inference(cnf_transformation,[],[f38]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_533,plain,
% 7.89/1.51      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0)) = X1 ),
% 7.89/1.51      inference(superposition,[status(thm)],[c_1,c_9]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_5675,plain,
% 7.89/1.51      ( k2_xboole_0(sK0,k4_xboole_0(sK1,sK0)) = sK1 ),
% 7.89/1.51      inference(superposition,[status(thm)],[c_103,c_533]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_6,plain,
% 7.89/1.51      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 7.89/1.51      inference(cnf_transformation,[],[f37]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_7,plain,
% 7.89/1.51      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.89/1.51      inference(cnf_transformation,[],[f26]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_151,plain,
% 7.89/1.51      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 7.89/1.51      inference(light_normalisation,[status(thm)],[c_6,c_7]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_8,plain,
% 7.89/1.51      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 7.89/1.51      inference(cnf_transformation,[],[f27]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_413,plain,
% 7.89/1.51      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(k1_xboole_0,X1) ),
% 7.89/1.51      inference(superposition,[status(thm)],[c_151,c_8]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_1183,plain,
% 7.89/1.51      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1)) ),
% 7.89/1.51      inference(superposition,[status(thm)],[c_9,c_413]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_5731,plain,
% 7.89/1.51      ( k2_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)),X0) = X0 ),
% 7.89/1.51      inference(superposition,[status(thm)],[c_7,c_533]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_0,plain,
% 7.89/1.51      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 7.89/1.51      inference(cnf_transformation,[],[f19]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_6109,plain,
% 7.89/1.51      ( k2_xboole_0(X0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) = X0 ),
% 7.89/1.51      inference(superposition,[status(thm)],[c_5731,c_0]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_411,plain,
% 7.89/1.51      ( k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),X0)) = k4_xboole_0(sK0,X0) ),
% 7.89/1.51      inference(superposition,[status(thm)],[c_103,c_8]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_780,plain,
% 7.89/1.51      ( k4_xboole_0(sK0,k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),X0),X1)) = k4_xboole_0(k4_xboole_0(sK0,X0),X1) ),
% 7.89/1.51      inference(superposition,[status(thm)],[c_411,c_8]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_782,plain,
% 7.89/1.51      ( k4_xboole_0(sK0,k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),X0),X1)) = k4_xboole_0(sK0,k2_xboole_0(X0,X1)) ),
% 7.89/1.51      inference(demodulation,[status(thm)],[c_780,c_8]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_6310,plain,
% 7.89/1.51      ( k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1))),X0)) = k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),X0)) ),
% 7.89/1.51      inference(superposition,[status(thm)],[c_6109,c_782]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_6346,plain,
% 7.89/1.51      ( k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1))),X0)) = k4_xboole_0(sK0,X0) ),
% 7.89/1.51      inference(light_normalisation,[status(thm)],[c_6310,c_411]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_7265,plain,
% 7.89/1.51      ( k4_xboole_0(sK0,k4_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1))) = k4_xboole_0(sK0,k1_xboole_0) ),
% 7.89/1.51      inference(superposition,[status(thm)],[c_9,c_6346]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_7325,plain,
% 7.89/1.51      ( k4_xboole_0(sK0,k4_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1))) = sK0 ),
% 7.89/1.51      inference(demodulation,[status(thm)],[c_7265,c_7]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_7443,plain,
% 7.89/1.51      ( k2_xboole_0(k4_xboole_0(sK0,sK0),k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1)),sK0)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1)) ),
% 7.89/1.51      inference(superposition,[status(thm)],[c_7325,c_533]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_4,plain,
% 7.89/1.51      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.89/1.51      inference(cnf_transformation,[],[f23]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_310,plain,
% 7.89/1.51      ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
% 7.89/1.51      inference(superposition,[status(thm)],[c_4,c_0]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_7480,plain,
% 7.89/1.51      ( k4_xboole_0(k1_xboole_0,k2_xboole_0(k4_xboole_0(sK0,sK1),sK0)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1)) ),
% 7.89/1.51      inference(demodulation,[status(thm)],[c_7443,c_8,c_151,c_310]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_552,plain,
% 7.89/1.51      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
% 7.89/1.51      inference(superposition,[status(thm)],[c_9,c_0]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_6434,plain,
% 7.89/1.51      ( k2_xboole_0(k4_xboole_0(sK0,sK1),sK0) = sK0 ),
% 7.89/1.51      inference(superposition,[status(thm)],[c_103,c_552]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_7481,plain,
% 7.89/1.51      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1)) = k4_xboole_0(k1_xboole_0,sK0) ),
% 7.89/1.51      inference(light_normalisation,[status(thm)],[c_7480,c_6434]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_7890,plain,
% 7.89/1.51      ( k2_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0)),k4_xboole_0(k1_xboole_0,sK0)) = k1_xboole_0 ),
% 7.89/1.51      inference(superposition,[status(thm)],[c_7481,c_533]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_7904,plain,
% 7.89/1.51      ( k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0))),k4_xboole_0(k1_xboole_0,sK0)) = k1_xboole_0 ),
% 7.89/1.51      inference(demodulation,[status(thm)],[c_7890,c_8]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_7905,plain,
% 7.89/1.51      ( k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,k4_xboole_0(sK0,k2_xboole_0(sK1,k1_xboole_0)))),k4_xboole_0(k1_xboole_0,sK0)) = k1_xboole_0 ),
% 7.89/1.51      inference(demodulation,[status(thm)],[c_7904,c_8]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_420,plain,
% 7.89/1.51      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
% 7.89/1.51      inference(superposition,[status(thm)],[c_8,c_151]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_7906,plain,
% 7.89/1.51      ( k4_xboole_0(k1_xboole_0,sK0) = k1_xboole_0 ),
% 7.89/1.51      inference(demodulation,[status(thm)],[c_7905,c_4,c_310,c_420]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_9251,plain,
% 7.89/1.51      ( k4_xboole_0(k1_xboole_0,k2_xboole_0(sK0,X0)) = k4_xboole_0(k1_xboole_0,X0) ),
% 7.89/1.51      inference(superposition,[status(thm)],[c_7906,c_8]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_9536,plain,
% 7.89/1.51      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(sK0,X0),k4_xboole_0(k2_xboole_0(sK0,X0),k1_xboole_0)),k4_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
% 7.89/1.51      inference(superposition,[status(thm)],[c_9251,c_533]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_9552,plain,
% 7.89/1.51      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 7.89/1.51      inference(demodulation,[status(thm)],[c_9536,c_7,c_151,c_310]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_22315,plain,
% 7.89/1.51      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = k1_xboole_0 ),
% 7.89/1.51      inference(demodulation,[status(thm)],[c_1183,c_8,c_9552]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_22320,plain,
% 7.89/1.51      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = k1_xboole_0 ),
% 7.89/1.51      inference(superposition,[status(thm)],[c_1,c_22315]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_22467,plain,
% 7.89/1.51      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k2_xboole_0(X1,X2)) = k4_xboole_0(k1_xboole_0,X2) ),
% 7.89/1.51      inference(superposition,[status(thm)],[c_22320,c_8]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_22485,plain,
% 7.89/1.51      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k2_xboole_0(X1,X2)) = k1_xboole_0 ),
% 7.89/1.51      inference(demodulation,[status(thm)],[c_22467,c_8,c_9552]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_25345,plain,
% 7.89/1.51      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,sK0)),sK1) = k1_xboole_0 ),
% 7.89/1.51      inference(superposition,[status(thm)],[c_5675,c_22485]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_26103,plain,
% 7.89/1.51      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,sK0),sK1)) = k1_xboole_0 ),
% 7.89/1.51      inference(superposition,[status(thm)],[c_25345,c_8]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_3,plain,
% 7.89/1.51      ( ~ r1_xboole_0(X0,X1)
% 7.89/1.51      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 7.89/1.51      inference(cnf_transformation,[],[f35]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_57,plain,
% 7.89/1.51      ( ~ r1_xboole_0(X0,X1)
% 7.89/1.51      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 7.89/1.51      inference(prop_impl,[status(thm)],[c_3]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_11,negated_conjecture,
% 7.89/1.51      ( r1_xboole_0(sK1,sK2) ),
% 7.89/1.51      inference(cnf_transformation,[],[f31]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_114,plain,
% 7.89/1.51      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
% 7.89/1.51      | sK1 != X0
% 7.89/1.51      | sK2 != X1 ),
% 7.89/1.51      inference(resolution_lifted,[status(thm)],[c_57,c_11]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_115,plain,
% 7.89/1.51      ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = k1_xboole_0 ),
% 7.89/1.51      inference(unflattening,[status(thm)],[c_114]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_395,plain,
% 7.89/1.51      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) = k1_xboole_0 ),
% 7.89/1.51      inference(superposition,[status(thm)],[c_1,c_115]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_686,plain,
% 7.89/1.51      ( k2_xboole_0(k1_xboole_0,k4_xboole_0(sK2,sK1)) = sK2 ),
% 7.89/1.51      inference(superposition,[status(thm)],[c_395,c_9]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_1034,plain,
% 7.89/1.51      ( k4_xboole_0(sK2,sK1) = sK2 ),
% 7.89/1.51      inference(superposition,[status(thm)],[c_310,c_686]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_4626,plain,
% 7.89/1.51      ( k4_xboole_0(sK2,k2_xboole_0(sK1,X0)) = k4_xboole_0(sK2,X0) ),
% 7.89/1.51      inference(superposition,[status(thm)],[c_1034,c_8]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_4766,plain,
% 7.89/1.51      ( k4_xboole_0(sK2,k2_xboole_0(X0,sK1)) = k4_xboole_0(sK2,X0) ),
% 7.89/1.51      inference(superposition,[status(thm)],[c_0,c_4626]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_26741,plain,
% 7.89/1.51      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) = k1_xboole_0 ),
% 7.89/1.51      inference(superposition,[status(thm)],[c_26103,c_4766]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_136,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_192,plain,
% 7.89/1.51      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) != X0
% 7.89/1.51      | k1_xboole_0 != X0
% 7.89/1.51      | k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) ),
% 7.89/1.51      inference(instantiation,[status(thm)],[c_136]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_193,plain,
% 7.89/1.51      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) != k1_xboole_0
% 7.89/1.51      | k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0))
% 7.89/1.51      | k1_xboole_0 != k1_xboole_0 ),
% 7.89/1.51      inference(instantiation,[status(thm)],[c_192]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_182,plain,
% 7.89/1.51      ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) ),
% 7.89/1.51      inference(instantiation,[status(thm)],[c_1]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_178,plain,
% 7.89/1.51      ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) != X0
% 7.89/1.51      | k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k1_xboole_0
% 7.89/1.51      | k1_xboole_0 != X0 ),
% 7.89/1.51      inference(instantiation,[status(thm)],[c_136]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_181,plain,
% 7.89/1.51      ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) != k4_xboole_0(sK2,k4_xboole_0(sK2,sK0))
% 7.89/1.51      | k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k1_xboole_0
% 7.89/1.51      | k1_xboole_0 != k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) ),
% 7.89/1.51      inference(instantiation,[status(thm)],[c_178]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_135,plain,( X0 = X0 ),theory(equality) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_140,plain,
% 7.89/1.51      ( k1_xboole_0 = k1_xboole_0 ),
% 7.89/1.51      inference(instantiation,[status(thm)],[c_135]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_2,plain,
% 7.89/1.51      ( r1_xboole_0(X0,X1)
% 7.89/1.51      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
% 7.89/1.51      inference(cnf_transformation,[],[f34]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_55,plain,
% 7.89/1.51      ( r1_xboole_0(X0,X1)
% 7.89/1.51      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
% 7.89/1.51      inference(prop_impl,[status(thm)],[c_2]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_10,negated_conjecture,
% 7.89/1.51      ( ~ r1_xboole_0(sK0,sK2) ),
% 7.89/1.51      inference(cnf_transformation,[],[f32]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_109,plain,
% 7.89/1.51      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0
% 7.89/1.51      | sK2 != X1
% 7.89/1.51      | sK0 != X0 ),
% 7.89/1.51      inference(resolution_lifted,[status(thm)],[c_55,c_10]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_110,plain,
% 7.89/1.51      ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) != k1_xboole_0 ),
% 7.89/1.51      inference(unflattening,[status(thm)],[c_109]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(contradiction,plain,
% 7.89/1.51      ( $false ),
% 7.89/1.51      inference(minisat,
% 7.89/1.51                [status(thm)],
% 7.89/1.51                [c_26741,c_193,c_182,c_181,c_140,c_110]) ).
% 7.89/1.51  
% 7.89/1.51  
% 7.89/1.51  % SZS output end CNFRefutation for theBenchmark.p
% 7.89/1.51  
% 7.89/1.51  ------                               Statistics
% 7.89/1.51  
% 7.89/1.51  ------ Selected
% 7.89/1.51  
% 7.89/1.51  total_time:                             0.963
% 7.89/1.51  
%------------------------------------------------------------------------------
