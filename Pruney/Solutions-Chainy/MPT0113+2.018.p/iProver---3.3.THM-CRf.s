%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:25:45 EST 2020

% Result     : Theorem 7.88s
% Output     : CNFRefutation 7.88s
% Verified   : 
% Statistics : Number of formulae       :  159 (5742 expanded)
%              Number of clauses        :  119 (2021 expanded)
%              Number of leaves         :   17 (1606 expanded)
%              Depth                    :   26
%              Number of atoms          :  202 (6104 expanded)
%              Number of equality atoms :  157 (5621 expanded)
%              Maximal formula depth    :    8 (   2 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f12,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f15,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f15])).

fof(f7,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f49,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f46,f38])).

fof(f52,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
    inference(definition_unfolding,[],[f40,f49])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f53,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) ),
    inference(definition_unfolding,[],[f42,f38,f38])).

fof(f14,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f14])).

fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,k4_xboole_0(X1,X2))
       => ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,X2)
        | ~ r1_tarski(X0,X1) )
      & r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f28,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r1_xboole_0(X0,X2)
          | ~ r1_tarski(X0,X1) )
        & r1_tarski(X0,k4_xboole_0(X1,X2)) )
   => ( ( ~ r1_xboole_0(sK2,sK4)
        | ~ r1_tarski(sK2,sK3) )
      & r1_tarski(sK2,k4_xboole_0(sK3,sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ( ~ r1_xboole_0(sK2,sK4)
      | ~ r1_tarski(sK2,sK3) )
    & r1_tarski(sK2,k4_xboole_0(sK3,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f22,f28])).

fof(f47,plain,(
    r1_tarski(sK2,k4_xboole_0(sK3,sK4)) ),
    inference(cnf_transformation,[],[f29])).

fof(f54,plain,(
    r1_tarski(sK2,k5_xboole_0(sK3,k3_xboole_0(sK3,sK4))) ),
    inference(definition_unfolding,[],[f47,f38])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f6,axiom,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0 ) ),
    inference(definition_unfolding,[],[f35,f38])).

fof(f48,plain,
    ( ~ r1_xboole_0(sK2,sK4)
    | ~ r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_12,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_13,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_627,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_13,c_1])).

cnf(c_4688,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)) = k5_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_12,c_627])).

cnf(c_9,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_4758,plain,
    ( k3_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(X0,k1_xboole_0),X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4688,c_9])).

cnf(c_4823,plain,
    ( k3_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,X0),X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_4758])).

cnf(c_11,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_826,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) = k3_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X2))) ),
    inference(superposition,[status(thm)],[c_0,c_11])).

cnf(c_14178,plain,
    ( k3_xboole_0(k5_xboole_0(k3_xboole_0(k1_xboole_0,X0),X0),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1))) = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1)) ),
    inference(superposition,[status(thm)],[c_4823,c_826])).

cnf(c_755,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_12,c_1])).

cnf(c_772,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0))) = X0 ),
    inference(superposition,[status(thm)],[c_755,c_9])).

cnf(c_1366,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0))) = X0 ),
    inference(superposition,[status(thm)],[c_0,c_772])).

cnf(c_771,plain,
    ( k3_xboole_0(k1_xboole_0,k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_755,c_9])).

cnf(c_1342,plain,
    ( k3_xboole_0(k1_xboole_0,k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_11,c_771])).

cnf(c_8771,plain,
    ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1366,c_1342])).

cnf(c_14243,plain,
    ( k3_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1))) = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_14178,c_755,c_8771])).

cnf(c_14244,plain,
    ( k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,X1)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_14243,c_755,c_8771])).

cnf(c_14245,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_14244,c_8771])).

cnf(c_14218,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)))) = k3_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_826,c_1366])).

cnf(c_14246,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,k5_xboole_0(X0,k1_xboole_0))) = k3_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_14245,c_14218])).

cnf(c_14247,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X0)) = k3_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_14246,c_12])).

cnf(c_14,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_784,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_14,c_13])).

cnf(c_791,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_784,c_755])).

cnf(c_900,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_11,c_791])).

cnf(c_27385,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(k3_xboole_0(X1,X0),X2)))) = k3_xboole_0(k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X0)),X2) ),
    inference(superposition,[status(thm)],[c_14247,c_900])).

cnf(c_22277,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X0)) = k3_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_14247,c_0])).

cnf(c_27605,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(k3_xboole_0(X1,X0),X2)))) = k3_xboole_0(k3_xboole_0(X1,X0),X2) ),
    inference(light_normalisation,[status(thm)],[c_27385,c_22277])).

cnf(c_823,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,k3_xboole_0(X0,X1))) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(superposition,[status(thm)],[c_0,c_11])).

cnf(c_11438,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k3_xboole_0(X2,k3_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_823,c_791])).

cnf(c_22254,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(k3_xboole_0(X1,X0),X2))) = k5_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(k3_xboole_0(X1,X0),X2)) ),
    inference(superposition,[status(thm)],[c_14247,c_826])).

cnf(c_22315,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(demodulation,[status(thm)],[c_22254,c_826])).

cnf(c_27606,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X2,k3_xboole_0(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_27605,c_826,c_11438,c_22315])).

cnf(c_14149,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(k3_xboole_0(X1,X0),k1_xboole_0))))) = k5_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_1366,c_826])).

cnf(c_14277,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0)))))) = k5_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_14149,c_826])).

cnf(c_14278,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X0,k5_xboole_0(X1,k1_xboole_0))))) = k5_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_14277,c_14245])).

cnf(c_14279,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X0,X1)))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_14278,c_12,c_14])).

cnf(c_16,negated_conjecture,
    ( r1_tarski(sK2,k5_xboole_0(sK3,k3_xboole_0(sK3,sK4))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_606,plain,
    ( r1_tarski(sK2,k5_xboole_0(sK3,k3_xboole_0(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_731,plain,
    ( r1_tarski(sK2,k5_xboole_0(sK3,k3_xboole_0(sK4,sK3))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_0,c_606])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_608,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1249,plain,
    ( k3_xboole_0(sK2,k5_xboole_0(sK3,k3_xboole_0(sK4,sK3))) = sK2 ),
    inference(superposition,[status(thm)],[c_731,c_608])).

cnf(c_1424,plain,
    ( k3_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK3,k3_xboole_0(sK4,sK3)),k3_xboole_0(k5_xboole_0(sK3,k3_xboole_0(sK4,sK3)),X0))) = k5_xboole_0(sK2,k3_xboole_0(sK2,X0)) ),
    inference(superposition,[status(thm)],[c_1249,c_11])).

cnf(c_1452,plain,
    ( k3_xboole_0(sK2,k5_xboole_0(sK3,k5_xboole_0(k3_xboole_0(sK4,sK3),k3_xboole_0(k5_xboole_0(sK3,k3_xboole_0(sK4,sK3)),X0)))) = k5_xboole_0(sK2,k3_xboole_0(sK2,X0)) ),
    inference(superposition,[status(thm)],[c_13,c_1424])).

cnf(c_22915,plain,
    ( k5_xboole_0(sK2,k3_xboole_0(sK2,k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(k5_xboole_0(sK3,k3_xboole_0(sK4,sK3)),X0))))) = k3_xboole_0(sK2,k5_xboole_0(sK3,k5_xboole_0(k3_xboole_0(sK4,sK3),k1_xboole_0))) ),
    inference(superposition,[status(thm)],[c_14279,c_1452])).

cnf(c_22916,plain,
    ( k5_xboole_0(sK2,k3_xboole_0(sK2,k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(k5_xboole_0(sK3,k3_xboole_0(sK4,sK3)),X0))))) = k3_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK3,k3_xboole_0(sK4,sK3)),k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_14279,c_1424])).

cnf(c_906,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_791,c_9])).

cnf(c_829,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(k3_xboole_0(k3_xboole_0(X0,X1),X2),X3)) = k5_xboole_0(k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))),X3) ),
    inference(superposition,[status(thm)],[c_11,c_13])).

cnf(c_18541,plain,
    ( k5_xboole_0(k3_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X0),k3_xboole_0(k3_xboole_0(X0,X0),X1))),X2) = k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X1),X2)) ),
    inference(superposition,[status(thm)],[c_906,c_829])).

cnf(c_8,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_609,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_840,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_9,c_609])).

cnf(c_1251,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_840,c_608])).

cnf(c_11410,plain,
    ( k3_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X0),k3_xboole_0(k3_xboole_0(X0,X0),X1))) = k5_xboole_0(X0,k3_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_906,c_823])).

cnf(c_11524,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))) = k5_xboole_0(X0,k3_xboole_0(X1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_11410,c_1251])).

cnf(c_18692,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X2) = k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X1),X2)) ),
    inference(light_normalisation,[status(thm)],[c_18541,c_1251,c_11524])).

cnf(c_22929,plain,
    ( k5_xboole_0(sK2,k3_xboole_0(sK2,k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(k5_xboole_0(sK3,k3_xboole_0(sK4,sK3)),X0))))) = k3_xboole_0(sK2,k5_xboole_0(sK3,k5_xboole_0(k3_xboole_0(sK3,sK4),k1_xboole_0))) ),
    inference(demodulation,[status(thm)],[c_22916,c_18692])).

cnf(c_22930,plain,
    ( k5_xboole_0(sK2,k3_xboole_0(sK2,k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(k5_xboole_0(sK3,k3_xboole_0(sK4,sK3)),X0))))) = k3_xboole_0(sK2,k5_xboole_0(sK3,k3_xboole_0(sK3,sK4))) ),
    inference(demodulation,[status(thm)],[c_22929,c_12])).

cnf(c_22933,plain,
    ( k3_xboole_0(sK2,k5_xboole_0(sK3,k5_xboole_0(k3_xboole_0(sK4,sK3),k1_xboole_0))) = k3_xboole_0(sK2,k5_xboole_0(sK3,k3_xboole_0(sK3,sK4))) ),
    inference(demodulation,[status(thm)],[c_22915,c_22930])).

cnf(c_22934,plain,
    ( k3_xboole_0(sK2,k5_xboole_0(sK3,k3_xboole_0(sK3,sK4))) = sK2 ),
    inference(demodulation,[status(thm)],[c_22933,c_12,c_1249])).

cnf(c_27395,plain,
    ( k5_xboole_0(k3_xboole_0(sK2,sK3),sK2) = k3_xboole_0(k3_xboole_0(sK2,sK3),sK4) ),
    inference(superposition,[status(thm)],[c_22934,c_900])).

cnf(c_27607,plain,
    ( k5_xboole_0(k3_xboole_0(sK2,sK3),sK2) = k3_xboole_0(sK4,k3_xboole_0(sK3,sK2)) ),
    inference(demodulation,[status(thm)],[c_27606,c_27395])).

cnf(c_22798,plain,
    ( k3_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X0,X1))),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X0,X1))),k1_xboole_0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_14279,c_14279])).

cnf(c_14164,plain,
    ( k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)),k5_xboole_0(X0,k3_xboole_0(X0,X1))) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_1366,c_826])).

cnf(c_14270,plain,
    ( k3_xboole_0(k5_xboole_0(X0,k1_xboole_0),k5_xboole_0(X0,k3_xboole_0(X0,X1))) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_14164,c_14245])).

cnf(c_14271,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X1,X0)) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_14270,c_12,c_11524])).

cnf(c_22502,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2) = k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X1,X0),X2)) ),
    inference(superposition,[status(thm)],[c_14271,c_13])).

cnf(c_23085,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(k3_xboole_0(X0,X1),X1),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X0,X1))),k1_xboole_0)))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_22798,c_22502])).

cnf(c_838,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_609])).

cnf(c_1250,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X1) = k3_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_838,c_608])).

cnf(c_23086,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X0,X1))),k1_xboole_0)))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_23085,c_1250])).

cnf(c_23087,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_23086,c_12,c_14245])).

cnf(c_1453,plain,
    ( k3_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK3,k3_xboole_0(sK4,sK3)),k3_xboole_0(X0,k5_xboole_0(sK3,k3_xboole_0(sK4,sK3))))) = k5_xboole_0(sK2,k3_xboole_0(sK2,X0)) ),
    inference(superposition,[status(thm)],[c_0,c_1424])).

cnf(c_24561,plain,
    ( k3_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK3,k3_xboole_0(sK4,sK3)),k1_xboole_0)) = k5_xboole_0(sK2,k3_xboole_0(sK2,sK4)) ),
    inference(superposition,[status(thm)],[c_23087,c_1453])).

cnf(c_24570,plain,
    ( k3_xboole_0(sK2,k5_xboole_0(sK3,k5_xboole_0(k3_xboole_0(sK3,sK4),k1_xboole_0))) = k5_xboole_0(sK2,k3_xboole_0(sK2,sK4)) ),
    inference(demodulation,[status(thm)],[c_24561,c_18692])).

cnf(c_24571,plain,
    ( k5_xboole_0(sK2,k3_xboole_0(sK2,sK4)) = sK2 ),
    inference(demodulation,[status(thm)],[c_24570,c_12,c_22934])).

cnf(c_24866,plain,
    ( k5_xboole_0(sK2,sK2) = k3_xboole_0(sK2,sK4) ),
    inference(superposition,[status(thm)],[c_24571,c_791])).

cnf(c_25503,plain,
    ( k3_xboole_0(sK2,sK4) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_24866,c_14])).

cnf(c_27418,plain,
    ( k5_xboole_0(k3_xboole_0(X0,sK2),k3_xboole_0(X0,k5_xboole_0(sK2,k1_xboole_0))) = k3_xboole_0(k3_xboole_0(X0,sK2),sK4) ),
    inference(superposition,[status(thm)],[c_25503,c_900])).

cnf(c_27572,plain,
    ( k3_xboole_0(k3_xboole_0(X0,sK2),sK4) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_27418,c_12,c_14])).

cnf(c_28281,plain,
    ( k3_xboole_0(sK4,k3_xboole_0(X0,sK2)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_27572,c_0])).

cnf(c_28934,plain,
    ( k5_xboole_0(k3_xboole_0(sK2,sK3),sK2) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_27607,c_28281])).

cnf(c_11411,plain,
    ( k3_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK3,k3_xboole_0(sK4,sK3)),k3_xboole_0(k5_xboole_0(sK3,k3_xboole_0(sK4,sK3)),X0))) = k5_xboole_0(sK2,k3_xboole_0(X0,sK2)) ),
    inference(superposition,[status(thm)],[c_1249,c_823])).

cnf(c_626,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_13,c_1])).

cnf(c_898,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
    inference(superposition,[status(thm)],[c_1,c_791])).

cnf(c_987,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X0) = X1 ),
    inference(superposition,[status(thm)],[c_898,c_898])).

cnf(c_1139,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X2)) = k5_xboole_0(X1,X2) ),
    inference(superposition,[status(thm)],[c_987,c_13])).

cnf(c_8635,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X1,X3)) = k5_xboole_0(k5_xboole_0(X0,X2),X3) ),
    inference(superposition,[status(thm)],[c_626,c_1139])).

cnf(c_983,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X1) = X0 ),
    inference(superposition,[status(thm)],[c_791,c_898])).

cnf(c_1047,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X1,X2)) = k5_xboole_0(X0,X2) ),
    inference(superposition,[status(thm)],[c_983,c_13])).

cnf(c_8355,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X1,X3)) = k5_xboole_0(X0,k5_xboole_0(X2,X3)) ),
    inference(superposition,[status(thm)],[c_1047,c_1047])).

cnf(c_8760,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(light_normalisation,[status(thm)],[c_8635,c_8355])).

cnf(c_11523,plain,
    ( k5_xboole_0(sK2,k3_xboole_0(X0,sK2)) = k5_xboole_0(sK2,k3_xboole_0(sK2,X0)) ),
    inference(demodulation,[status(thm)],[c_11411,c_1424,c_1452,c_8760])).

cnf(c_3683,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X1,X0)))) = X0 ),
    inference(superposition,[status(thm)],[c_626,c_9])).

cnf(c_12517,plain,
    ( k3_xboole_0(sK2,k5_xboole_0(X0,k5_xboole_0(sK2,k3_xboole_0(sK2,X0)))) = sK2 ),
    inference(superposition,[status(thm)],[c_11523,c_3683])).

cnf(c_24906,plain,
    ( k3_xboole_0(sK2,k5_xboole_0(sK4,sK2)) = sK2 ),
    inference(superposition,[status(thm)],[c_24571,c_12517])).

cnf(c_7,plain,
    ( r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_610,plain,
    ( r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_25930,plain,
    ( r1_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(sK4,sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_24906,c_610])).

cnf(c_26084,plain,
    ( r1_xboole_0(sK2,sK4) = iProver_top ),
    inference(demodulation,[status(thm)],[c_25930,c_898])).

cnf(c_711,plain,
    ( k5_xboole_0(sK2,k3_xboole_0(sK2,sK3)) = k5_xboole_0(k3_xboole_0(sK2,sK3),sK2) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_326,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_669,plain,
    ( k5_xboole_0(k3_xboole_0(sK2,sK3),sK2) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k5_xboole_0(k3_xboole_0(sK2,sK3),sK2) ),
    inference(instantiation,[status(thm)],[c_326])).

cnf(c_670,plain,
    ( k5_xboole_0(k3_xboole_0(sK2,sK3),sK2) != k1_xboole_0
    | k1_xboole_0 = k5_xboole_0(k3_xboole_0(sK2,sK3),sK2)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_669])).

cnf(c_643,plain,
    ( k5_xboole_0(sK2,k3_xboole_0(sK2,sK3)) != X0
    | k5_xboole_0(sK2,k3_xboole_0(sK2,sK3)) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_326])).

cnf(c_653,plain,
    ( k5_xboole_0(sK2,k3_xboole_0(sK2,sK3)) != k5_xboole_0(k3_xboole_0(sK2,sK3),sK2)
    | k5_xboole_0(sK2,k3_xboole_0(sK2,sK3)) = k1_xboole_0
    | k1_xboole_0 != k5_xboole_0(k3_xboole_0(sK2,sK3),sK2) ),
    inference(instantiation,[status(thm)],[c_643])).

cnf(c_325,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_336,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_325])).

cnf(c_6,plain,
    ( r1_tarski(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_96,plain,
    ( r1_tarski(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_6])).

cnf(c_15,negated_conjecture,
    ( ~ r1_tarski(sK2,sK3)
    | ~ r1_xboole_0(sK2,sK4) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_267,plain,
    ( ~ r1_xboole_0(sK2,sK4)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_96,c_15])).

cnf(c_268,plain,
    ( ~ r1_xboole_0(sK2,sK4)
    | k5_xboole_0(sK2,k3_xboole_0(sK2,sK3)) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_267])).

cnf(c_269,plain,
    ( k5_xboole_0(sK2,k3_xboole_0(sK2,sK3)) != k1_xboole_0
    | r1_xboole_0(sK2,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_268])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_28934,c_26084,c_711,c_670,c_653,c_336,c_269])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:45:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 7.88/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.88/1.49  
% 7.88/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.88/1.49  
% 7.88/1.49  ------  iProver source info
% 7.88/1.49  
% 7.88/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.88/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.88/1.49  git: non_committed_changes: false
% 7.88/1.49  git: last_make_outside_of_git: false
% 7.88/1.49  
% 7.88/1.49  ------ 
% 7.88/1.49  
% 7.88/1.49  ------ Input Options
% 7.88/1.49  
% 7.88/1.49  --out_options                           all
% 7.88/1.49  --tptp_safe_out                         true
% 7.88/1.49  --problem_path                          ""
% 7.88/1.49  --include_path                          ""
% 7.88/1.49  --clausifier                            res/vclausify_rel
% 7.88/1.49  --clausifier_options                    ""
% 7.88/1.49  --stdin                                 false
% 7.88/1.49  --stats_out                             all
% 7.88/1.49  
% 7.88/1.49  ------ General Options
% 7.88/1.49  
% 7.88/1.49  --fof                                   false
% 7.88/1.49  --time_out_real                         305.
% 7.88/1.49  --time_out_virtual                      -1.
% 7.88/1.49  --symbol_type_check                     false
% 7.88/1.49  --clausify_out                          false
% 7.88/1.49  --sig_cnt_out                           false
% 7.88/1.49  --trig_cnt_out                          false
% 7.88/1.49  --trig_cnt_out_tolerance                1.
% 7.88/1.49  --trig_cnt_out_sk_spl                   false
% 7.88/1.49  --abstr_cl_out                          false
% 7.88/1.49  
% 7.88/1.49  ------ Global Options
% 7.88/1.49  
% 7.88/1.49  --schedule                              default
% 7.88/1.49  --add_important_lit                     false
% 7.88/1.49  --prop_solver_per_cl                    1000
% 7.88/1.49  --min_unsat_core                        false
% 7.88/1.49  --soft_assumptions                      false
% 7.88/1.49  --soft_lemma_size                       3
% 7.88/1.49  --prop_impl_unit_size                   0
% 7.88/1.49  --prop_impl_unit                        []
% 7.88/1.49  --share_sel_clauses                     true
% 7.88/1.49  --reset_solvers                         false
% 7.88/1.49  --bc_imp_inh                            [conj_cone]
% 7.88/1.49  --conj_cone_tolerance                   3.
% 7.88/1.49  --extra_neg_conj                        none
% 7.88/1.49  --large_theory_mode                     true
% 7.88/1.49  --prolific_symb_bound                   200
% 7.88/1.49  --lt_threshold                          2000
% 7.88/1.49  --clause_weak_htbl                      true
% 7.88/1.49  --gc_record_bc_elim                     false
% 7.88/1.49  
% 7.88/1.49  ------ Preprocessing Options
% 7.88/1.49  
% 7.88/1.49  --preprocessing_flag                    true
% 7.88/1.49  --time_out_prep_mult                    0.1
% 7.88/1.49  --splitting_mode                        input
% 7.88/1.49  --splitting_grd                         true
% 7.88/1.49  --splitting_cvd                         false
% 7.88/1.49  --splitting_cvd_svl                     false
% 7.88/1.49  --splitting_nvd                         32
% 7.88/1.49  --sub_typing                            true
% 7.88/1.49  --prep_gs_sim                           true
% 7.88/1.49  --prep_unflatten                        true
% 7.88/1.49  --prep_res_sim                          true
% 7.88/1.49  --prep_upred                            true
% 7.88/1.49  --prep_sem_filter                       exhaustive
% 7.88/1.49  --prep_sem_filter_out                   false
% 7.88/1.49  --pred_elim                             true
% 7.88/1.49  --res_sim_input                         true
% 7.88/1.49  --eq_ax_congr_red                       true
% 7.88/1.49  --pure_diseq_elim                       true
% 7.88/1.49  --brand_transform                       false
% 7.88/1.49  --non_eq_to_eq                          false
% 7.88/1.49  --prep_def_merge                        true
% 7.88/1.49  --prep_def_merge_prop_impl              false
% 7.88/1.49  --prep_def_merge_mbd                    true
% 7.88/1.49  --prep_def_merge_tr_red                 false
% 7.88/1.49  --prep_def_merge_tr_cl                  false
% 7.88/1.49  --smt_preprocessing                     true
% 7.88/1.49  --smt_ac_axioms                         fast
% 7.88/1.49  --preprocessed_out                      false
% 7.88/1.49  --preprocessed_stats                    false
% 7.88/1.49  
% 7.88/1.49  ------ Abstraction refinement Options
% 7.88/1.49  
% 7.88/1.49  --abstr_ref                             []
% 7.88/1.49  --abstr_ref_prep                        false
% 7.88/1.49  --abstr_ref_until_sat                   false
% 7.88/1.49  --abstr_ref_sig_restrict                funpre
% 7.88/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.88/1.49  --abstr_ref_under                       []
% 7.88/1.49  
% 7.88/1.49  ------ SAT Options
% 7.88/1.49  
% 7.88/1.49  --sat_mode                              false
% 7.88/1.49  --sat_fm_restart_options                ""
% 7.88/1.49  --sat_gr_def                            false
% 7.88/1.49  --sat_epr_types                         true
% 7.88/1.49  --sat_non_cyclic_types                  false
% 7.88/1.49  --sat_finite_models                     false
% 7.88/1.49  --sat_fm_lemmas                         false
% 7.88/1.49  --sat_fm_prep                           false
% 7.88/1.49  --sat_fm_uc_incr                        true
% 7.88/1.49  --sat_out_model                         small
% 7.88/1.49  --sat_out_clauses                       false
% 7.88/1.49  
% 7.88/1.49  ------ QBF Options
% 7.88/1.49  
% 7.88/1.49  --qbf_mode                              false
% 7.88/1.49  --qbf_elim_univ                         false
% 7.88/1.49  --qbf_dom_inst                          none
% 7.88/1.49  --qbf_dom_pre_inst                      false
% 7.88/1.49  --qbf_sk_in                             false
% 7.88/1.49  --qbf_pred_elim                         true
% 7.88/1.49  --qbf_split                             512
% 7.88/1.49  
% 7.88/1.49  ------ BMC1 Options
% 7.88/1.49  
% 7.88/1.49  --bmc1_incremental                      false
% 7.88/1.49  --bmc1_axioms                           reachable_all
% 7.88/1.49  --bmc1_min_bound                        0
% 7.88/1.49  --bmc1_max_bound                        -1
% 7.88/1.49  --bmc1_max_bound_default                -1
% 7.88/1.49  --bmc1_symbol_reachability              true
% 7.88/1.49  --bmc1_property_lemmas                  false
% 7.88/1.49  --bmc1_k_induction                      false
% 7.88/1.49  --bmc1_non_equiv_states                 false
% 7.88/1.49  --bmc1_deadlock                         false
% 7.88/1.49  --bmc1_ucm                              false
% 7.88/1.49  --bmc1_add_unsat_core                   none
% 7.88/1.49  --bmc1_unsat_core_children              false
% 7.88/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.88/1.49  --bmc1_out_stat                         full
% 7.88/1.49  --bmc1_ground_init                      false
% 7.88/1.49  --bmc1_pre_inst_next_state              false
% 7.88/1.49  --bmc1_pre_inst_state                   false
% 7.88/1.49  --bmc1_pre_inst_reach_state             false
% 7.88/1.49  --bmc1_out_unsat_core                   false
% 7.88/1.49  --bmc1_aig_witness_out                  false
% 7.88/1.49  --bmc1_verbose                          false
% 7.88/1.49  --bmc1_dump_clauses_tptp                false
% 7.88/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.88/1.49  --bmc1_dump_file                        -
% 7.88/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.88/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.88/1.49  --bmc1_ucm_extend_mode                  1
% 7.88/1.49  --bmc1_ucm_init_mode                    2
% 7.88/1.49  --bmc1_ucm_cone_mode                    none
% 7.88/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.88/1.49  --bmc1_ucm_relax_model                  4
% 7.88/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.88/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.88/1.49  --bmc1_ucm_layered_model                none
% 7.88/1.49  --bmc1_ucm_max_lemma_size               10
% 7.88/1.49  
% 7.88/1.49  ------ AIG Options
% 7.88/1.49  
% 7.88/1.49  --aig_mode                              false
% 7.88/1.49  
% 7.88/1.49  ------ Instantiation Options
% 7.88/1.49  
% 7.88/1.49  --instantiation_flag                    true
% 7.88/1.49  --inst_sos_flag                         true
% 7.88/1.49  --inst_sos_phase                        true
% 7.88/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.88/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.88/1.49  --inst_lit_sel_side                     num_symb
% 7.88/1.49  --inst_solver_per_active                1400
% 7.88/1.49  --inst_solver_calls_frac                1.
% 7.88/1.49  --inst_passive_queue_type               priority_queues
% 7.88/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.88/1.49  --inst_passive_queues_freq              [25;2]
% 7.88/1.49  --inst_dismatching                      true
% 7.88/1.49  --inst_eager_unprocessed_to_passive     true
% 7.88/1.49  --inst_prop_sim_given                   true
% 7.88/1.49  --inst_prop_sim_new                     false
% 7.88/1.49  --inst_subs_new                         false
% 7.88/1.49  --inst_eq_res_simp                      false
% 7.88/1.49  --inst_subs_given                       false
% 7.88/1.49  --inst_orphan_elimination               true
% 7.88/1.49  --inst_learning_loop_flag               true
% 7.88/1.49  --inst_learning_start                   3000
% 7.88/1.49  --inst_learning_factor                  2
% 7.88/1.49  --inst_start_prop_sim_after_learn       3
% 7.88/1.49  --inst_sel_renew                        solver
% 7.88/1.49  --inst_lit_activity_flag                true
% 7.88/1.49  --inst_restr_to_given                   false
% 7.88/1.49  --inst_activity_threshold               500
% 7.88/1.49  --inst_out_proof                        true
% 7.88/1.49  
% 7.88/1.49  ------ Resolution Options
% 7.88/1.49  
% 7.88/1.49  --resolution_flag                       true
% 7.88/1.49  --res_lit_sel                           adaptive
% 7.88/1.49  --res_lit_sel_side                      none
% 7.88/1.49  --res_ordering                          kbo
% 7.88/1.49  --res_to_prop_solver                    active
% 7.88/1.49  --res_prop_simpl_new                    false
% 7.88/1.49  --res_prop_simpl_given                  true
% 7.88/1.49  --res_passive_queue_type                priority_queues
% 7.88/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.88/1.49  --res_passive_queues_freq               [15;5]
% 7.88/1.49  --res_forward_subs                      full
% 7.88/1.49  --res_backward_subs                     full
% 7.88/1.49  --res_forward_subs_resolution           true
% 7.88/1.49  --res_backward_subs_resolution          true
% 7.88/1.49  --res_orphan_elimination                true
% 7.88/1.49  --res_time_limit                        2.
% 7.88/1.49  --res_out_proof                         true
% 7.88/1.49  
% 7.88/1.49  ------ Superposition Options
% 7.88/1.49  
% 7.88/1.49  --superposition_flag                    true
% 7.88/1.49  --sup_passive_queue_type                priority_queues
% 7.88/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.88/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.88/1.49  --demod_completeness_check              fast
% 7.88/1.49  --demod_use_ground                      true
% 7.88/1.49  --sup_to_prop_solver                    passive
% 7.88/1.49  --sup_prop_simpl_new                    true
% 7.88/1.49  --sup_prop_simpl_given                  true
% 7.88/1.49  --sup_fun_splitting                     true
% 7.88/1.49  --sup_smt_interval                      50000
% 7.88/1.49  
% 7.88/1.49  ------ Superposition Simplification Setup
% 7.88/1.49  
% 7.88/1.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.88/1.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.88/1.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.88/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.88/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.88/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.88/1.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.88/1.49  --sup_immed_triv                        [TrivRules]
% 7.88/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.88/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.88/1.49  --sup_immed_bw_main                     []
% 7.88/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.88/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.88/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.88/1.49  --sup_input_bw                          []
% 7.88/1.49  
% 7.88/1.49  ------ Combination Options
% 7.88/1.49  
% 7.88/1.49  --comb_res_mult                         3
% 7.88/1.49  --comb_sup_mult                         2
% 7.88/1.49  --comb_inst_mult                        10
% 7.88/1.49  
% 7.88/1.49  ------ Debug Options
% 7.88/1.49  
% 7.88/1.49  --dbg_backtrace                         false
% 7.88/1.49  --dbg_dump_prop_clauses                 false
% 7.88/1.49  --dbg_dump_prop_clauses_file            -
% 7.88/1.49  --dbg_out_stat                          false
% 7.88/1.49  ------ Parsing...
% 7.88/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.88/1.49  
% 7.88/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.88/1.49  
% 7.88/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.88/1.49  
% 7.88/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.88/1.49  ------ Proving...
% 7.88/1.49  ------ Problem Properties 
% 7.88/1.49  
% 7.88/1.49  
% 7.88/1.49  clauses                                 17
% 7.88/1.49  conjectures                             2
% 7.88/1.49  EPR                                     1
% 7.88/1.49  Horn                                    15
% 7.88/1.49  unary                                   10
% 7.88/1.49  binary                                  7
% 7.88/1.49  lits                                    24
% 7.88/1.49  lits eq                                 11
% 7.88/1.49  fd_pure                                 0
% 7.88/1.49  fd_pseudo                               0
% 7.88/1.49  fd_cond                                 1
% 7.88/1.49  fd_pseudo_cond                          0
% 7.88/1.49  AC symbols                              1
% 7.88/1.49  
% 7.88/1.49  ------ Schedule dynamic 5 is on 
% 7.88/1.49  
% 7.88/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.88/1.49  
% 7.88/1.49  
% 7.88/1.49  ------ 
% 7.88/1.49  Current options:
% 7.88/1.49  ------ 
% 7.88/1.49  
% 7.88/1.49  ------ Input Options
% 7.88/1.49  
% 7.88/1.49  --out_options                           all
% 7.88/1.49  --tptp_safe_out                         true
% 7.88/1.49  --problem_path                          ""
% 7.88/1.49  --include_path                          ""
% 7.88/1.49  --clausifier                            res/vclausify_rel
% 7.88/1.49  --clausifier_options                    ""
% 7.88/1.49  --stdin                                 false
% 7.88/1.49  --stats_out                             all
% 7.88/1.49  
% 7.88/1.49  ------ General Options
% 7.88/1.49  
% 7.88/1.49  --fof                                   false
% 7.88/1.49  --time_out_real                         305.
% 7.88/1.49  --time_out_virtual                      -1.
% 7.88/1.49  --symbol_type_check                     false
% 7.88/1.49  --clausify_out                          false
% 7.88/1.49  --sig_cnt_out                           false
% 7.88/1.49  --trig_cnt_out                          false
% 7.88/1.49  --trig_cnt_out_tolerance                1.
% 7.88/1.49  --trig_cnt_out_sk_spl                   false
% 7.88/1.49  --abstr_cl_out                          false
% 7.88/1.49  
% 7.88/1.49  ------ Global Options
% 7.88/1.49  
% 7.88/1.49  --schedule                              default
% 7.88/1.49  --add_important_lit                     false
% 7.88/1.49  --prop_solver_per_cl                    1000
% 7.88/1.49  --min_unsat_core                        false
% 7.88/1.49  --soft_assumptions                      false
% 7.88/1.49  --soft_lemma_size                       3
% 7.88/1.49  --prop_impl_unit_size                   0
% 7.88/1.49  --prop_impl_unit                        []
% 7.88/1.49  --share_sel_clauses                     true
% 7.88/1.49  --reset_solvers                         false
% 7.88/1.49  --bc_imp_inh                            [conj_cone]
% 7.88/1.49  --conj_cone_tolerance                   3.
% 7.88/1.49  --extra_neg_conj                        none
% 7.88/1.49  --large_theory_mode                     true
% 7.88/1.49  --prolific_symb_bound                   200
% 7.88/1.49  --lt_threshold                          2000
% 7.88/1.49  --clause_weak_htbl                      true
% 7.88/1.49  --gc_record_bc_elim                     false
% 7.88/1.49  
% 7.88/1.49  ------ Preprocessing Options
% 7.88/1.49  
% 7.88/1.49  --preprocessing_flag                    true
% 7.88/1.49  --time_out_prep_mult                    0.1
% 7.88/1.49  --splitting_mode                        input
% 7.88/1.49  --splitting_grd                         true
% 7.88/1.49  --splitting_cvd                         false
% 7.88/1.49  --splitting_cvd_svl                     false
% 7.88/1.49  --splitting_nvd                         32
% 7.88/1.49  --sub_typing                            true
% 7.88/1.49  --prep_gs_sim                           true
% 7.88/1.49  --prep_unflatten                        true
% 7.88/1.49  --prep_res_sim                          true
% 7.88/1.49  --prep_upred                            true
% 7.88/1.49  --prep_sem_filter                       exhaustive
% 7.88/1.49  --prep_sem_filter_out                   false
% 7.88/1.49  --pred_elim                             true
% 7.88/1.49  --res_sim_input                         true
% 7.88/1.49  --eq_ax_congr_red                       true
% 7.88/1.49  --pure_diseq_elim                       true
% 7.88/1.49  --brand_transform                       false
% 7.88/1.49  --non_eq_to_eq                          false
% 7.88/1.49  --prep_def_merge                        true
% 7.88/1.49  --prep_def_merge_prop_impl              false
% 7.88/1.49  --prep_def_merge_mbd                    true
% 7.88/1.49  --prep_def_merge_tr_red                 false
% 7.88/1.49  --prep_def_merge_tr_cl                  false
% 7.88/1.49  --smt_preprocessing                     true
% 7.88/1.49  --smt_ac_axioms                         fast
% 7.88/1.49  --preprocessed_out                      false
% 7.88/1.49  --preprocessed_stats                    false
% 7.88/1.49  
% 7.88/1.49  ------ Abstraction refinement Options
% 7.88/1.49  
% 7.88/1.49  --abstr_ref                             []
% 7.88/1.49  --abstr_ref_prep                        false
% 7.88/1.49  --abstr_ref_until_sat                   false
% 7.88/1.49  --abstr_ref_sig_restrict                funpre
% 7.88/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.88/1.49  --abstr_ref_under                       []
% 7.88/1.49  
% 7.88/1.49  ------ SAT Options
% 7.88/1.49  
% 7.88/1.49  --sat_mode                              false
% 7.88/1.49  --sat_fm_restart_options                ""
% 7.88/1.49  --sat_gr_def                            false
% 7.88/1.49  --sat_epr_types                         true
% 7.88/1.49  --sat_non_cyclic_types                  false
% 7.88/1.49  --sat_finite_models                     false
% 7.88/1.49  --sat_fm_lemmas                         false
% 7.88/1.49  --sat_fm_prep                           false
% 7.88/1.49  --sat_fm_uc_incr                        true
% 7.88/1.49  --sat_out_model                         small
% 7.88/1.49  --sat_out_clauses                       false
% 7.88/1.49  
% 7.88/1.49  ------ QBF Options
% 7.88/1.49  
% 7.88/1.49  --qbf_mode                              false
% 7.88/1.49  --qbf_elim_univ                         false
% 7.88/1.49  --qbf_dom_inst                          none
% 7.88/1.49  --qbf_dom_pre_inst                      false
% 7.88/1.49  --qbf_sk_in                             false
% 7.88/1.49  --qbf_pred_elim                         true
% 7.88/1.49  --qbf_split                             512
% 7.88/1.49  
% 7.88/1.49  ------ BMC1 Options
% 7.88/1.49  
% 7.88/1.49  --bmc1_incremental                      false
% 7.88/1.49  --bmc1_axioms                           reachable_all
% 7.88/1.49  --bmc1_min_bound                        0
% 7.88/1.49  --bmc1_max_bound                        -1
% 7.88/1.49  --bmc1_max_bound_default                -1
% 7.88/1.49  --bmc1_symbol_reachability              true
% 7.88/1.49  --bmc1_property_lemmas                  false
% 7.88/1.49  --bmc1_k_induction                      false
% 7.88/1.49  --bmc1_non_equiv_states                 false
% 7.88/1.49  --bmc1_deadlock                         false
% 7.88/1.49  --bmc1_ucm                              false
% 7.88/1.49  --bmc1_add_unsat_core                   none
% 7.88/1.49  --bmc1_unsat_core_children              false
% 7.88/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.88/1.49  --bmc1_out_stat                         full
% 7.88/1.49  --bmc1_ground_init                      false
% 7.88/1.49  --bmc1_pre_inst_next_state              false
% 7.88/1.49  --bmc1_pre_inst_state                   false
% 7.88/1.49  --bmc1_pre_inst_reach_state             false
% 7.88/1.49  --bmc1_out_unsat_core                   false
% 7.88/1.49  --bmc1_aig_witness_out                  false
% 7.88/1.49  --bmc1_verbose                          false
% 7.88/1.49  --bmc1_dump_clauses_tptp                false
% 7.88/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.88/1.49  --bmc1_dump_file                        -
% 7.88/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.88/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.88/1.49  --bmc1_ucm_extend_mode                  1
% 7.88/1.49  --bmc1_ucm_init_mode                    2
% 7.88/1.49  --bmc1_ucm_cone_mode                    none
% 7.88/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.88/1.49  --bmc1_ucm_relax_model                  4
% 7.88/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.88/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.88/1.49  --bmc1_ucm_layered_model                none
% 7.88/1.49  --bmc1_ucm_max_lemma_size               10
% 7.88/1.49  
% 7.88/1.49  ------ AIG Options
% 7.88/1.49  
% 7.88/1.49  --aig_mode                              false
% 7.88/1.49  
% 7.88/1.49  ------ Instantiation Options
% 7.88/1.49  
% 7.88/1.49  --instantiation_flag                    true
% 7.88/1.49  --inst_sos_flag                         true
% 7.88/1.49  --inst_sos_phase                        true
% 7.88/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.88/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.88/1.49  --inst_lit_sel_side                     none
% 7.88/1.49  --inst_solver_per_active                1400
% 7.88/1.49  --inst_solver_calls_frac                1.
% 7.88/1.49  --inst_passive_queue_type               priority_queues
% 7.88/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.88/1.49  --inst_passive_queues_freq              [25;2]
% 7.88/1.49  --inst_dismatching                      true
% 7.88/1.49  --inst_eager_unprocessed_to_passive     true
% 7.88/1.49  --inst_prop_sim_given                   true
% 7.88/1.49  --inst_prop_sim_new                     false
% 7.88/1.49  --inst_subs_new                         false
% 7.88/1.49  --inst_eq_res_simp                      false
% 7.88/1.49  --inst_subs_given                       false
% 7.88/1.49  --inst_orphan_elimination               true
% 7.88/1.49  --inst_learning_loop_flag               true
% 7.88/1.49  --inst_learning_start                   3000
% 7.88/1.49  --inst_learning_factor                  2
% 7.88/1.49  --inst_start_prop_sim_after_learn       3
% 7.88/1.49  --inst_sel_renew                        solver
% 7.88/1.49  --inst_lit_activity_flag                true
% 7.88/1.49  --inst_restr_to_given                   false
% 7.88/1.49  --inst_activity_threshold               500
% 7.88/1.49  --inst_out_proof                        true
% 7.88/1.49  
% 7.88/1.49  ------ Resolution Options
% 7.88/1.49  
% 7.88/1.49  --resolution_flag                       false
% 7.88/1.49  --res_lit_sel                           adaptive
% 7.88/1.49  --res_lit_sel_side                      none
% 7.88/1.49  --res_ordering                          kbo
% 7.88/1.49  --res_to_prop_solver                    active
% 7.88/1.49  --res_prop_simpl_new                    false
% 7.88/1.49  --res_prop_simpl_given                  true
% 7.88/1.49  --res_passive_queue_type                priority_queues
% 7.88/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.88/1.49  --res_passive_queues_freq               [15;5]
% 7.88/1.49  --res_forward_subs                      full
% 7.88/1.49  --res_backward_subs                     full
% 7.88/1.49  --res_forward_subs_resolution           true
% 7.88/1.49  --res_backward_subs_resolution          true
% 7.88/1.49  --res_orphan_elimination                true
% 7.88/1.49  --res_time_limit                        2.
% 7.88/1.49  --res_out_proof                         true
% 7.88/1.49  
% 7.88/1.49  ------ Superposition Options
% 7.88/1.49  
% 7.88/1.49  --superposition_flag                    true
% 7.88/1.49  --sup_passive_queue_type                priority_queues
% 7.88/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.88/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.88/1.49  --demod_completeness_check              fast
% 7.88/1.49  --demod_use_ground                      true
% 7.88/1.49  --sup_to_prop_solver                    passive
% 7.88/1.49  --sup_prop_simpl_new                    true
% 7.88/1.49  --sup_prop_simpl_given                  true
% 7.88/1.49  --sup_fun_splitting                     true
% 7.88/1.49  --sup_smt_interval                      50000
% 7.88/1.49  
% 7.88/1.49  ------ Superposition Simplification Setup
% 7.88/1.49  
% 7.88/1.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.88/1.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.88/1.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.88/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.88/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.88/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.88/1.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.88/1.49  --sup_immed_triv                        [TrivRules]
% 7.88/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.88/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.88/1.49  --sup_immed_bw_main                     []
% 7.88/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.88/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.88/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.88/1.49  --sup_input_bw                          []
% 7.88/1.49  
% 7.88/1.49  ------ Combination Options
% 7.88/1.49  
% 7.88/1.49  --comb_res_mult                         3
% 7.88/1.49  --comb_sup_mult                         2
% 7.88/1.49  --comb_inst_mult                        10
% 7.88/1.49  
% 7.88/1.49  ------ Debug Options
% 7.88/1.49  
% 7.88/1.49  --dbg_backtrace                         false
% 7.88/1.49  --dbg_dump_prop_clauses                 false
% 7.88/1.49  --dbg_dump_prop_clauses_file            -
% 7.88/1.49  --dbg_out_stat                          false
% 7.88/1.49  
% 7.88/1.49  
% 7.88/1.49  
% 7.88/1.49  
% 7.88/1.49  ------ Proving...
% 7.88/1.49  
% 7.88/1.49  
% 7.88/1.49  % SZS status Theorem for theBenchmark.p
% 7.88/1.49  
% 7.88/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.88/1.49  
% 7.88/1.49  fof(f1,axiom,(
% 7.88/1.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 7.88/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.88/1.49  
% 7.88/1.49  fof(f30,plain,(
% 7.88/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 7.88/1.49    inference(cnf_transformation,[],[f1])).
% 7.88/1.49  
% 7.88/1.49  fof(f12,axiom,(
% 7.88/1.49    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 7.88/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.88/1.49  
% 7.88/1.49  fof(f43,plain,(
% 7.88/1.49    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 7.88/1.49    inference(cnf_transformation,[],[f12])).
% 7.88/1.49  
% 7.88/1.49  fof(f13,axiom,(
% 7.88/1.49    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 7.88/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.88/1.49  
% 7.88/1.49  fof(f44,plain,(
% 7.88/1.49    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 7.88/1.49    inference(cnf_transformation,[],[f13])).
% 7.88/1.49  
% 7.88/1.49  fof(f2,axiom,(
% 7.88/1.49    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 7.88/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.88/1.49  
% 7.88/1.49  fof(f31,plain,(
% 7.88/1.49    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 7.88/1.49    inference(cnf_transformation,[],[f2])).
% 7.88/1.49  
% 7.88/1.49  fof(f9,axiom,(
% 7.88/1.49    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 7.88/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.88/1.49  
% 7.88/1.49  fof(f40,plain,(
% 7.88/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 7.88/1.49    inference(cnf_transformation,[],[f9])).
% 7.88/1.49  
% 7.88/1.49  fof(f15,axiom,(
% 7.88/1.49    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 7.88/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.88/1.49  
% 7.88/1.49  fof(f46,plain,(
% 7.88/1.49    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 7.88/1.49    inference(cnf_transformation,[],[f15])).
% 7.88/1.49  
% 7.88/1.49  fof(f7,axiom,(
% 7.88/1.49    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 7.88/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.88/1.49  
% 7.88/1.49  fof(f38,plain,(
% 7.88/1.49    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 7.88/1.49    inference(cnf_transformation,[],[f7])).
% 7.88/1.49  
% 7.88/1.49  fof(f49,plain,(
% 7.88/1.49    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 7.88/1.49    inference(definition_unfolding,[],[f46,f38])).
% 7.88/1.49  
% 7.88/1.49  fof(f52,plain,(
% 7.88/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0) )),
% 7.88/1.49    inference(definition_unfolding,[],[f40,f49])).
% 7.88/1.49  
% 7.88/1.49  fof(f11,axiom,(
% 7.88/1.49    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 7.88/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.88/1.49  
% 7.88/1.49  fof(f42,plain,(
% 7.88/1.49    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 7.88/1.49    inference(cnf_transformation,[],[f11])).
% 7.88/1.49  
% 7.88/1.49  fof(f53,plain,(
% 7.88/1.49    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2))) )),
% 7.88/1.49    inference(definition_unfolding,[],[f42,f38,f38])).
% 7.88/1.49  
% 7.88/1.49  fof(f14,axiom,(
% 7.88/1.49    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 7.88/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.88/1.49  
% 7.88/1.49  fof(f45,plain,(
% 7.88/1.49    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 7.88/1.49    inference(cnf_transformation,[],[f14])).
% 7.88/1.49  
% 7.88/1.49  fof(f16,conjecture,(
% 7.88/1.49    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 7.88/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.88/1.49  
% 7.88/1.49  fof(f17,negated_conjecture,(
% 7.88/1.49    ~! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 7.88/1.49    inference(negated_conjecture,[],[f16])).
% 7.88/1.49  
% 7.88/1.49  fof(f22,plain,(
% 7.88/1.49    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 7.88/1.49    inference(ennf_transformation,[],[f17])).
% 7.88/1.49  
% 7.88/1.49  fof(f28,plain,(
% 7.88/1.49    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2))) => ((~r1_xboole_0(sK2,sK4) | ~r1_tarski(sK2,sK3)) & r1_tarski(sK2,k4_xboole_0(sK3,sK4)))),
% 7.88/1.49    introduced(choice_axiom,[])).
% 7.88/1.49  
% 7.88/1.49  fof(f29,plain,(
% 7.88/1.49    (~r1_xboole_0(sK2,sK4) | ~r1_tarski(sK2,sK3)) & r1_tarski(sK2,k4_xboole_0(sK3,sK4))),
% 7.88/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f22,f28])).
% 7.88/1.49  
% 7.88/1.49  fof(f47,plain,(
% 7.88/1.49    r1_tarski(sK2,k4_xboole_0(sK3,sK4))),
% 7.88/1.49    inference(cnf_transformation,[],[f29])).
% 7.88/1.49  
% 7.88/1.49  fof(f54,plain,(
% 7.88/1.49    r1_tarski(sK2,k5_xboole_0(sK3,k3_xboole_0(sK3,sK4)))),
% 7.88/1.49    inference(definition_unfolding,[],[f47,f38])).
% 7.88/1.49  
% 7.88/1.49  fof(f10,axiom,(
% 7.88/1.49    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 7.88/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.88/1.49  
% 7.88/1.49  fof(f21,plain,(
% 7.88/1.49    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 7.88/1.49    inference(ennf_transformation,[],[f10])).
% 7.88/1.49  
% 7.88/1.49  fof(f41,plain,(
% 7.88/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 7.88/1.49    inference(cnf_transformation,[],[f21])).
% 7.88/1.49  
% 7.88/1.49  fof(f8,axiom,(
% 7.88/1.49    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 7.88/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.88/1.49  
% 7.88/1.49  fof(f39,plain,(
% 7.88/1.49    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 7.88/1.49    inference(cnf_transformation,[],[f8])).
% 7.88/1.49  
% 7.88/1.49  fof(f6,axiom,(
% 7.88/1.49    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 7.88/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.88/1.49  
% 7.88/1.49  fof(f37,plain,(
% 7.88/1.49    ( ! [X0,X1] : (r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))) )),
% 7.88/1.49    inference(cnf_transformation,[],[f6])).
% 7.88/1.49  
% 7.88/1.49  fof(f5,axiom,(
% 7.88/1.49    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 7.88/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.88/1.49  
% 7.88/1.49  fof(f27,plain,(
% 7.88/1.49    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 7.88/1.49    inference(nnf_transformation,[],[f5])).
% 7.88/1.49  
% 7.88/1.49  fof(f35,plain,(
% 7.88/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)) )),
% 7.88/1.49    inference(cnf_transformation,[],[f27])).
% 7.88/1.49  
% 7.88/1.49  fof(f51,plain,(
% 7.88/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0) )),
% 7.88/1.49    inference(definition_unfolding,[],[f35,f38])).
% 7.88/1.49  
% 7.88/1.49  fof(f48,plain,(
% 7.88/1.49    ~r1_xboole_0(sK2,sK4) | ~r1_tarski(sK2,sK3)),
% 7.88/1.49    inference(cnf_transformation,[],[f29])).
% 7.88/1.49  
% 7.88/1.49  cnf(c_0,plain,
% 7.88/1.49      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 7.88/1.49      inference(cnf_transformation,[],[f30]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_12,plain,
% 7.88/1.49      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.88/1.49      inference(cnf_transformation,[],[f43]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_13,plain,
% 7.88/1.49      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 7.88/1.49      inference(cnf_transformation,[],[f44]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_1,plain,
% 7.88/1.49      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 7.88/1.49      inference(cnf_transformation,[],[f31]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_627,plain,
% 7.88/1.49      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
% 7.88/1.49      inference(superposition,[status(thm)],[c_13,c_1]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_4688,plain,
% 7.88/1.49      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)) = k5_xboole_0(X1,X0) ),
% 7.88/1.49      inference(superposition,[status(thm)],[c_12,c_627]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_9,plain,
% 7.88/1.49      ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
% 7.88/1.49      inference(cnf_transformation,[],[f52]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_4758,plain,
% 7.88/1.49      ( k3_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(X0,k1_xboole_0),X0)) = k1_xboole_0 ),
% 7.88/1.49      inference(superposition,[status(thm)],[c_4688,c_9]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_4823,plain,
% 7.88/1.49      ( k3_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,X0),X0)) = k1_xboole_0 ),
% 7.88/1.49      inference(superposition,[status(thm)],[c_0,c_4758]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_11,plain,
% 7.88/1.49      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 7.88/1.49      inference(cnf_transformation,[],[f53]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_826,plain,
% 7.88/1.49      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) = k3_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X2))) ),
% 7.88/1.49      inference(superposition,[status(thm)],[c_0,c_11]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_14178,plain,
% 7.88/1.49      ( k3_xboole_0(k5_xboole_0(k3_xboole_0(k1_xboole_0,X0),X0),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1))) = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1)) ),
% 7.88/1.49      inference(superposition,[status(thm)],[c_4823,c_826]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_755,plain,
% 7.88/1.49      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 7.88/1.49      inference(superposition,[status(thm)],[c_12,c_1]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_772,plain,
% 7.88/1.49      ( k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0))) = X0 ),
% 7.88/1.49      inference(superposition,[status(thm)],[c_755,c_9]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_1366,plain,
% 7.88/1.49      ( k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0))) = X0 ),
% 7.88/1.49      inference(superposition,[status(thm)],[c_0,c_772]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_771,plain,
% 7.88/1.49      ( k3_xboole_0(k1_xboole_0,k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0))) = k1_xboole_0 ),
% 7.88/1.49      inference(superposition,[status(thm)],[c_755,c_9]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_1342,plain,
% 7.88/1.49      ( k3_xboole_0(k1_xboole_0,k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0)))) = k1_xboole_0 ),
% 7.88/1.49      inference(superposition,[status(thm)],[c_11,c_771]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_8771,plain,
% 7.88/1.49      ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 7.88/1.49      inference(superposition,[status(thm)],[c_1366,c_1342]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_14243,plain,
% 7.88/1.49      ( k3_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1))) = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1)) ),
% 7.88/1.49      inference(light_normalisation,[status(thm)],[c_14178,c_755,c_8771]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_14244,plain,
% 7.88/1.49      ( k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,X1)) = k1_xboole_0 ),
% 7.88/1.49      inference(demodulation,[status(thm)],[c_14243,c_755,c_8771]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_14245,plain,
% 7.88/1.49      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 7.88/1.49      inference(demodulation,[status(thm)],[c_14244,c_8771]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_14218,plain,
% 7.88/1.49      ( k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)))) = k3_xboole_0(X0,X1) ),
% 7.88/1.49      inference(superposition,[status(thm)],[c_826,c_1366]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_14246,plain,
% 7.88/1.49      ( k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,k5_xboole_0(X0,k1_xboole_0))) = k3_xboole_0(X0,X1) ),
% 7.88/1.49      inference(demodulation,[status(thm)],[c_14245,c_14218]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_14247,plain,
% 7.88/1.49      ( k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X0)) = k3_xboole_0(X0,X1) ),
% 7.88/1.49      inference(light_normalisation,[status(thm)],[c_14246,c_12]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_14,plain,
% 7.88/1.49      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 7.88/1.49      inference(cnf_transformation,[],[f45]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_784,plain,
% 7.88/1.49      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
% 7.88/1.49      inference(superposition,[status(thm)],[c_14,c_13]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_791,plain,
% 7.88/1.49      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
% 7.88/1.49      inference(demodulation,[status(thm)],[c_784,c_755]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_900,plain,
% 7.88/1.49      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
% 7.88/1.49      inference(superposition,[status(thm)],[c_11,c_791]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_27385,plain,
% 7.88/1.49      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(k3_xboole_0(X1,X0),X2)))) = k3_xboole_0(k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X0)),X2) ),
% 7.88/1.49      inference(superposition,[status(thm)],[c_14247,c_900]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_22277,plain,
% 7.88/1.49      ( k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X0)) = k3_xboole_0(X1,X0) ),
% 7.88/1.49      inference(superposition,[status(thm)],[c_14247,c_0]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_27605,plain,
% 7.88/1.49      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(k3_xboole_0(X1,X0),X2)))) = k3_xboole_0(k3_xboole_0(X1,X0),X2) ),
% 7.88/1.49      inference(light_normalisation,[status(thm)],[c_27385,c_22277]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_823,plain,
% 7.88/1.49      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,k3_xboole_0(X0,X1))) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 7.88/1.49      inference(superposition,[status(thm)],[c_0,c_11]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_11438,plain,
% 7.88/1.49      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k3_xboole_0(X2,k3_xboole_0(X0,X1)) ),
% 7.88/1.49      inference(superposition,[status(thm)],[c_823,c_791]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_22254,plain,
% 7.88/1.49      ( k3_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(k3_xboole_0(X1,X0),X2))) = k5_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(k3_xboole_0(X1,X0),X2)) ),
% 7.88/1.49      inference(superposition,[status(thm)],[c_14247,c_826]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_22315,plain,
% 7.88/1.49      ( k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 7.88/1.49      inference(demodulation,[status(thm)],[c_22254,c_826]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_27606,plain,
% 7.88/1.49      ( k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X2,k3_xboole_0(X1,X0)) ),
% 7.88/1.49      inference(demodulation,
% 7.88/1.49                [status(thm)],
% 7.88/1.49                [c_27605,c_826,c_11438,c_22315]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_14149,plain,
% 7.88/1.49      ( k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(k3_xboole_0(X1,X0),k1_xboole_0))))) = k5_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(X1,X0)) ),
% 7.88/1.49      inference(superposition,[status(thm)],[c_1366,c_826]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_14277,plain,
% 7.88/1.49      ( k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0)))))) = k5_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(X1,X0)) ),
% 7.88/1.49      inference(demodulation,[status(thm)],[c_14149,c_826]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_14278,plain,
% 7.88/1.49      ( k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X0,k5_xboole_0(X1,k1_xboole_0))))) = k5_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(X1,X0)) ),
% 7.88/1.49      inference(demodulation,[status(thm)],[c_14277,c_14245]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_14279,plain,
% 7.88/1.49      ( k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X0,X1)))) = k1_xboole_0 ),
% 7.88/1.49      inference(demodulation,[status(thm)],[c_14278,c_12,c_14]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_16,negated_conjecture,
% 7.88/1.49      ( r1_tarski(sK2,k5_xboole_0(sK3,k3_xboole_0(sK3,sK4))) ),
% 7.88/1.49      inference(cnf_transformation,[],[f54]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_606,plain,
% 7.88/1.49      ( r1_tarski(sK2,k5_xboole_0(sK3,k3_xboole_0(sK3,sK4))) = iProver_top ),
% 7.88/1.49      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_731,plain,
% 7.88/1.49      ( r1_tarski(sK2,k5_xboole_0(sK3,k3_xboole_0(sK4,sK3))) = iProver_top ),
% 7.88/1.49      inference(demodulation,[status(thm)],[c_0,c_606]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_10,plain,
% 7.88/1.49      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 7.88/1.49      inference(cnf_transformation,[],[f41]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_608,plain,
% 7.88/1.49      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 7.88/1.49      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_1249,plain,
% 7.88/1.49      ( k3_xboole_0(sK2,k5_xboole_0(sK3,k3_xboole_0(sK4,sK3))) = sK2 ),
% 7.88/1.49      inference(superposition,[status(thm)],[c_731,c_608]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_1424,plain,
% 7.88/1.49      ( k3_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK3,k3_xboole_0(sK4,sK3)),k3_xboole_0(k5_xboole_0(sK3,k3_xboole_0(sK4,sK3)),X0))) = k5_xboole_0(sK2,k3_xboole_0(sK2,X0)) ),
% 7.88/1.49      inference(superposition,[status(thm)],[c_1249,c_11]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_1452,plain,
% 7.88/1.49      ( k3_xboole_0(sK2,k5_xboole_0(sK3,k5_xboole_0(k3_xboole_0(sK4,sK3),k3_xboole_0(k5_xboole_0(sK3,k3_xboole_0(sK4,sK3)),X0)))) = k5_xboole_0(sK2,k3_xboole_0(sK2,X0)) ),
% 7.88/1.49      inference(superposition,[status(thm)],[c_13,c_1424]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_22915,plain,
% 7.88/1.49      ( k5_xboole_0(sK2,k3_xboole_0(sK2,k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(k5_xboole_0(sK3,k3_xboole_0(sK4,sK3)),X0))))) = k3_xboole_0(sK2,k5_xboole_0(sK3,k5_xboole_0(k3_xboole_0(sK4,sK3),k1_xboole_0))) ),
% 7.88/1.49      inference(superposition,[status(thm)],[c_14279,c_1452]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_22916,plain,
% 7.88/1.49      ( k5_xboole_0(sK2,k3_xboole_0(sK2,k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(k5_xboole_0(sK3,k3_xboole_0(sK4,sK3)),X0))))) = k3_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK3,k3_xboole_0(sK4,sK3)),k1_xboole_0)) ),
% 7.88/1.49      inference(superposition,[status(thm)],[c_14279,c_1424]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_906,plain,
% 7.88/1.49      ( k3_xboole_0(X0,k3_xboole_0(X0,X0)) = X0 ),
% 7.88/1.49      inference(superposition,[status(thm)],[c_791,c_9]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_829,plain,
% 7.88/1.49      ( k5_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(k3_xboole_0(k3_xboole_0(X0,X1),X2),X3)) = k5_xboole_0(k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))),X3) ),
% 7.88/1.49      inference(superposition,[status(thm)],[c_11,c_13]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_18541,plain,
% 7.88/1.49      ( k5_xboole_0(k3_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X0),k3_xboole_0(k3_xboole_0(X0,X0),X1))),X2) = k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X1),X2)) ),
% 7.88/1.49      inference(superposition,[status(thm)],[c_906,c_829]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_8,plain,
% 7.88/1.49      ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
% 7.88/1.49      inference(cnf_transformation,[],[f39]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_609,plain,
% 7.88/1.49      ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
% 7.88/1.49      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_840,plain,
% 7.88/1.49      ( r1_tarski(X0,X0) = iProver_top ),
% 7.88/1.49      inference(superposition,[status(thm)],[c_9,c_609]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_1251,plain,
% 7.88/1.49      ( k3_xboole_0(X0,X0) = X0 ),
% 7.88/1.49      inference(superposition,[status(thm)],[c_840,c_608]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_11410,plain,
% 7.88/1.49      ( k3_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X0),k3_xboole_0(k3_xboole_0(X0,X0),X1))) = k5_xboole_0(X0,k3_xboole_0(X1,X0)) ),
% 7.88/1.49      inference(superposition,[status(thm)],[c_906,c_823]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_11524,plain,
% 7.88/1.49      ( k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))) = k5_xboole_0(X0,k3_xboole_0(X1,X0)) ),
% 7.88/1.49      inference(light_normalisation,[status(thm)],[c_11410,c_1251]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_18692,plain,
% 7.88/1.49      ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X2) = k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X1),X2)) ),
% 7.88/1.49      inference(light_normalisation,
% 7.88/1.49                [status(thm)],
% 7.88/1.49                [c_18541,c_1251,c_11524]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_22929,plain,
% 7.88/1.49      ( k5_xboole_0(sK2,k3_xboole_0(sK2,k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(k5_xboole_0(sK3,k3_xboole_0(sK4,sK3)),X0))))) = k3_xboole_0(sK2,k5_xboole_0(sK3,k5_xboole_0(k3_xboole_0(sK3,sK4),k1_xboole_0))) ),
% 7.88/1.49      inference(demodulation,[status(thm)],[c_22916,c_18692]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_22930,plain,
% 7.88/1.49      ( k5_xboole_0(sK2,k3_xboole_0(sK2,k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(k5_xboole_0(sK3,k3_xboole_0(sK4,sK3)),X0))))) = k3_xboole_0(sK2,k5_xboole_0(sK3,k3_xboole_0(sK3,sK4))) ),
% 7.88/1.49      inference(demodulation,[status(thm)],[c_22929,c_12]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_22933,plain,
% 7.88/1.49      ( k3_xboole_0(sK2,k5_xboole_0(sK3,k5_xboole_0(k3_xboole_0(sK4,sK3),k1_xboole_0))) = k3_xboole_0(sK2,k5_xboole_0(sK3,k3_xboole_0(sK3,sK4))) ),
% 7.88/1.49      inference(demodulation,[status(thm)],[c_22915,c_22930]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_22934,plain,
% 7.88/1.49      ( k3_xboole_0(sK2,k5_xboole_0(sK3,k3_xboole_0(sK3,sK4))) = sK2 ),
% 7.88/1.49      inference(demodulation,[status(thm)],[c_22933,c_12,c_1249]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_27395,plain,
% 7.88/1.49      ( k5_xboole_0(k3_xboole_0(sK2,sK3),sK2) = k3_xboole_0(k3_xboole_0(sK2,sK3),sK4) ),
% 7.88/1.49      inference(superposition,[status(thm)],[c_22934,c_900]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_27607,plain,
% 7.88/1.49      ( k5_xboole_0(k3_xboole_0(sK2,sK3),sK2) = k3_xboole_0(sK4,k3_xboole_0(sK3,sK2)) ),
% 7.88/1.49      inference(demodulation,[status(thm)],[c_27606,c_27395]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_22798,plain,
% 7.88/1.49      ( k3_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X0,X1))),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X0,X1))),k1_xboole_0))) = k1_xboole_0 ),
% 7.88/1.49      inference(superposition,[status(thm)],[c_14279,c_14279]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_14164,plain,
% 7.88/1.49      ( k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)),k5_xboole_0(X0,k3_xboole_0(X0,X1))) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
% 7.88/1.49      inference(superposition,[status(thm)],[c_1366,c_826]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_14270,plain,
% 7.88/1.49      ( k3_xboole_0(k5_xboole_0(X0,k1_xboole_0),k5_xboole_0(X0,k3_xboole_0(X0,X1))) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
% 7.88/1.49      inference(demodulation,[status(thm)],[c_14164,c_14245]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_14271,plain,
% 7.88/1.49      ( k5_xboole_0(X0,k3_xboole_0(X1,X0)) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
% 7.88/1.49      inference(light_normalisation,[status(thm)],[c_14270,c_12,c_11524]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_22502,plain,
% 7.88/1.49      ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2) = k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X1,X0),X2)) ),
% 7.88/1.49      inference(superposition,[status(thm)],[c_14271,c_13]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_23085,plain,
% 7.88/1.49      ( k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(k3_xboole_0(X0,X1),X1),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X0,X1))),k1_xboole_0)))) = k1_xboole_0 ),
% 7.88/1.49      inference(demodulation,[status(thm)],[c_22798,c_22502]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_838,plain,
% 7.88/1.49      ( r1_tarski(k3_xboole_0(X0,X1),X1) = iProver_top ),
% 7.88/1.49      inference(superposition,[status(thm)],[c_0,c_609]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_1250,plain,
% 7.88/1.49      ( k3_xboole_0(k3_xboole_0(X0,X1),X1) = k3_xboole_0(X0,X1) ),
% 7.88/1.49      inference(superposition,[status(thm)],[c_838,c_608]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_23086,plain,
% 7.88/1.49      ( k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X0,X1))),k1_xboole_0)))) = k1_xboole_0 ),
% 7.88/1.49      inference(light_normalisation,[status(thm)],[c_23085,c_1250]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_23087,plain,
% 7.88/1.49      ( k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))) = k1_xboole_0 ),
% 7.88/1.49      inference(demodulation,[status(thm)],[c_23086,c_12,c_14245]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_1453,plain,
% 7.88/1.49      ( k3_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK3,k3_xboole_0(sK4,sK3)),k3_xboole_0(X0,k5_xboole_0(sK3,k3_xboole_0(sK4,sK3))))) = k5_xboole_0(sK2,k3_xboole_0(sK2,X0)) ),
% 7.88/1.49      inference(superposition,[status(thm)],[c_0,c_1424]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_24561,plain,
% 7.88/1.49      ( k3_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK3,k3_xboole_0(sK4,sK3)),k1_xboole_0)) = k5_xboole_0(sK2,k3_xboole_0(sK2,sK4)) ),
% 7.88/1.49      inference(superposition,[status(thm)],[c_23087,c_1453]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_24570,plain,
% 7.88/1.49      ( k3_xboole_0(sK2,k5_xboole_0(sK3,k5_xboole_0(k3_xboole_0(sK3,sK4),k1_xboole_0))) = k5_xboole_0(sK2,k3_xboole_0(sK2,sK4)) ),
% 7.88/1.49      inference(demodulation,[status(thm)],[c_24561,c_18692]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_24571,plain,
% 7.88/1.49      ( k5_xboole_0(sK2,k3_xboole_0(sK2,sK4)) = sK2 ),
% 7.88/1.49      inference(demodulation,[status(thm)],[c_24570,c_12,c_22934]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_24866,plain,
% 7.88/1.49      ( k5_xboole_0(sK2,sK2) = k3_xboole_0(sK2,sK4) ),
% 7.88/1.49      inference(superposition,[status(thm)],[c_24571,c_791]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_25503,plain,
% 7.88/1.49      ( k3_xboole_0(sK2,sK4) = k1_xboole_0 ),
% 7.88/1.49      inference(demodulation,[status(thm)],[c_24866,c_14]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_27418,plain,
% 7.88/1.49      ( k5_xboole_0(k3_xboole_0(X0,sK2),k3_xboole_0(X0,k5_xboole_0(sK2,k1_xboole_0))) = k3_xboole_0(k3_xboole_0(X0,sK2),sK4) ),
% 7.88/1.49      inference(superposition,[status(thm)],[c_25503,c_900]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_27572,plain,
% 7.88/1.49      ( k3_xboole_0(k3_xboole_0(X0,sK2),sK4) = k1_xboole_0 ),
% 7.88/1.49      inference(demodulation,[status(thm)],[c_27418,c_12,c_14]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_28281,plain,
% 7.88/1.49      ( k3_xboole_0(sK4,k3_xboole_0(X0,sK2)) = k1_xboole_0 ),
% 7.88/1.49      inference(superposition,[status(thm)],[c_27572,c_0]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_28934,plain,
% 7.88/1.49      ( k5_xboole_0(k3_xboole_0(sK2,sK3),sK2) = k1_xboole_0 ),
% 7.88/1.49      inference(demodulation,[status(thm)],[c_27607,c_28281]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_11411,plain,
% 7.88/1.49      ( k3_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK3,k3_xboole_0(sK4,sK3)),k3_xboole_0(k5_xboole_0(sK3,k3_xboole_0(sK4,sK3)),X0))) = k5_xboole_0(sK2,k3_xboole_0(X0,sK2)) ),
% 7.88/1.49      inference(superposition,[status(thm)],[c_1249,c_823]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_626,plain,
% 7.88/1.49      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
% 7.88/1.49      inference(superposition,[status(thm)],[c_13,c_1]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_898,plain,
% 7.88/1.49      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
% 7.88/1.49      inference(superposition,[status(thm)],[c_1,c_791]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_987,plain,
% 7.88/1.49      ( k5_xboole_0(k5_xboole_0(X0,X1),X0) = X1 ),
% 7.88/1.49      inference(superposition,[status(thm)],[c_898,c_898]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_1139,plain,
% 7.88/1.49      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X2)) = k5_xboole_0(X1,X2) ),
% 7.88/1.49      inference(superposition,[status(thm)],[c_987,c_13]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_8635,plain,
% 7.88/1.49      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X1,X3)) = k5_xboole_0(k5_xboole_0(X0,X2),X3) ),
% 7.88/1.49      inference(superposition,[status(thm)],[c_626,c_1139]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_983,plain,
% 7.88/1.49      ( k5_xboole_0(k5_xboole_0(X0,X1),X1) = X0 ),
% 7.88/1.49      inference(superposition,[status(thm)],[c_791,c_898]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_1047,plain,
% 7.88/1.49      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X1,X2)) = k5_xboole_0(X0,X2) ),
% 7.88/1.49      inference(superposition,[status(thm)],[c_983,c_13]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_8355,plain,
% 7.88/1.49      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X1,X3)) = k5_xboole_0(X0,k5_xboole_0(X2,X3)) ),
% 7.88/1.49      inference(superposition,[status(thm)],[c_1047,c_1047]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_8760,plain,
% 7.88/1.49      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
% 7.88/1.49      inference(light_normalisation,[status(thm)],[c_8635,c_8355]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_11523,plain,
% 7.88/1.49      ( k5_xboole_0(sK2,k3_xboole_0(X0,sK2)) = k5_xboole_0(sK2,k3_xboole_0(sK2,X0)) ),
% 7.88/1.49      inference(demodulation,
% 7.88/1.49                [status(thm)],
% 7.88/1.49                [c_11411,c_1424,c_1452,c_8760]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_3683,plain,
% 7.88/1.49      ( k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X1,X0)))) = X0 ),
% 7.88/1.49      inference(superposition,[status(thm)],[c_626,c_9]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_12517,plain,
% 7.88/1.49      ( k3_xboole_0(sK2,k5_xboole_0(X0,k5_xboole_0(sK2,k3_xboole_0(sK2,X0)))) = sK2 ),
% 7.88/1.49      inference(superposition,[status(thm)],[c_11523,c_3683]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_24906,plain,
% 7.88/1.49      ( k3_xboole_0(sK2,k5_xboole_0(sK4,sK2)) = sK2 ),
% 7.88/1.49      inference(superposition,[status(thm)],[c_24571,c_12517]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_7,plain,
% 7.88/1.49      ( r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
% 7.88/1.49      inference(cnf_transformation,[],[f37]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_610,plain,
% 7.88/1.49      ( r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) = iProver_top ),
% 7.88/1.49      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_25930,plain,
% 7.88/1.49      ( r1_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(sK4,sK2))) = iProver_top ),
% 7.88/1.49      inference(superposition,[status(thm)],[c_24906,c_610]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_26084,plain,
% 7.88/1.49      ( r1_xboole_0(sK2,sK4) = iProver_top ),
% 7.88/1.49      inference(demodulation,[status(thm)],[c_25930,c_898]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_711,plain,
% 7.88/1.49      ( k5_xboole_0(sK2,k3_xboole_0(sK2,sK3)) = k5_xboole_0(k3_xboole_0(sK2,sK3),sK2) ),
% 7.88/1.49      inference(instantiation,[status(thm)],[c_1]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_326,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_669,plain,
% 7.88/1.49      ( k5_xboole_0(k3_xboole_0(sK2,sK3),sK2) != X0
% 7.88/1.49      | k1_xboole_0 != X0
% 7.88/1.49      | k1_xboole_0 = k5_xboole_0(k3_xboole_0(sK2,sK3),sK2) ),
% 7.88/1.49      inference(instantiation,[status(thm)],[c_326]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_670,plain,
% 7.88/1.49      ( k5_xboole_0(k3_xboole_0(sK2,sK3),sK2) != k1_xboole_0
% 7.88/1.49      | k1_xboole_0 = k5_xboole_0(k3_xboole_0(sK2,sK3),sK2)
% 7.88/1.49      | k1_xboole_0 != k1_xboole_0 ),
% 7.88/1.49      inference(instantiation,[status(thm)],[c_669]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_643,plain,
% 7.88/1.49      ( k5_xboole_0(sK2,k3_xboole_0(sK2,sK3)) != X0
% 7.88/1.49      | k5_xboole_0(sK2,k3_xboole_0(sK2,sK3)) = k1_xboole_0
% 7.88/1.49      | k1_xboole_0 != X0 ),
% 7.88/1.49      inference(instantiation,[status(thm)],[c_326]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_653,plain,
% 7.88/1.49      ( k5_xboole_0(sK2,k3_xboole_0(sK2,sK3)) != k5_xboole_0(k3_xboole_0(sK2,sK3),sK2)
% 7.88/1.49      | k5_xboole_0(sK2,k3_xboole_0(sK2,sK3)) = k1_xboole_0
% 7.88/1.49      | k1_xboole_0 != k5_xboole_0(k3_xboole_0(sK2,sK3),sK2) ),
% 7.88/1.49      inference(instantiation,[status(thm)],[c_643]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_325,plain,( X0 = X0 ),theory(equality) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_336,plain,
% 7.88/1.49      ( k1_xboole_0 = k1_xboole_0 ),
% 7.88/1.49      inference(instantiation,[status(thm)],[c_325]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_6,plain,
% 7.88/1.49      ( r1_tarski(X0,X1)
% 7.88/1.49      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0 ),
% 7.88/1.49      inference(cnf_transformation,[],[f51]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_96,plain,
% 7.88/1.49      ( r1_tarski(X0,X1)
% 7.88/1.49      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0 ),
% 7.88/1.49      inference(prop_impl,[status(thm)],[c_6]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_15,negated_conjecture,
% 7.88/1.49      ( ~ r1_tarski(sK2,sK3) | ~ r1_xboole_0(sK2,sK4) ),
% 7.88/1.49      inference(cnf_transformation,[],[f48]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_267,plain,
% 7.88/1.49      ( ~ r1_xboole_0(sK2,sK4)
% 7.88/1.49      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0
% 7.88/1.49      | sK3 != X1
% 7.88/1.49      | sK2 != X0 ),
% 7.88/1.49      inference(resolution_lifted,[status(thm)],[c_96,c_15]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_268,plain,
% 7.88/1.49      ( ~ r1_xboole_0(sK2,sK4)
% 7.88/1.49      | k5_xboole_0(sK2,k3_xboole_0(sK2,sK3)) != k1_xboole_0 ),
% 7.88/1.49      inference(unflattening,[status(thm)],[c_267]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_269,plain,
% 7.88/1.49      ( k5_xboole_0(sK2,k3_xboole_0(sK2,sK3)) != k1_xboole_0
% 7.88/1.49      | r1_xboole_0(sK2,sK4) != iProver_top ),
% 7.88/1.49      inference(predicate_to_equality,[status(thm)],[c_268]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(contradiction,plain,
% 7.88/1.49      ( $false ),
% 7.88/1.49      inference(minisat,
% 7.88/1.49                [status(thm)],
% 7.88/1.49                [c_28934,c_26084,c_711,c_670,c_653,c_336,c_269]) ).
% 7.88/1.49  
% 7.88/1.49  
% 7.88/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.88/1.49  
% 7.88/1.49  ------                               Statistics
% 7.88/1.49  
% 7.88/1.49  ------ General
% 7.88/1.49  
% 7.88/1.49  abstr_ref_over_cycles:                  0
% 7.88/1.49  abstr_ref_under_cycles:                 0
% 7.88/1.49  gc_basic_clause_elim:                   0
% 7.88/1.49  forced_gc_time:                         0
% 7.88/1.49  parsing_time:                           0.007
% 7.88/1.49  unif_index_cands_time:                  0.
% 7.88/1.49  unif_index_add_time:                    0.
% 7.88/1.49  orderings_time:                         0.
% 7.88/1.49  out_proof_time:                         0.01
% 7.88/1.49  total_time:                             0.886
% 7.88/1.49  num_of_symbols:                         42
% 7.88/1.49  num_of_terms:                           50791
% 7.88/1.49  
% 7.88/1.49  ------ Preprocessing
% 7.88/1.49  
% 7.88/1.49  num_of_splits:                          0
% 7.88/1.49  num_of_split_atoms:                     0
% 7.88/1.49  num_of_reused_defs:                     0
% 7.88/1.49  num_eq_ax_congr_red:                    6
% 7.88/1.49  num_of_sem_filtered_clauses:            1
% 7.88/1.49  num_of_subtypes:                        0
% 7.88/1.49  monotx_restored_types:                  0
% 7.88/1.49  sat_num_of_epr_types:                   0
% 7.88/1.49  sat_num_of_non_cyclic_types:            0
% 7.88/1.49  sat_guarded_non_collapsed_types:        0
% 7.88/1.49  num_pure_diseq_elim:                    0
% 7.88/1.49  simp_replaced_by:                       0
% 7.88/1.49  res_preprocessed:                       66
% 7.88/1.49  prep_upred:                             0
% 7.88/1.49  prep_unflattend:                        20
% 7.88/1.49  smt_new_axioms:                         0
% 7.88/1.49  pred_elim_cands:                        3
% 7.88/1.49  pred_elim:                              0
% 7.88/1.49  pred_elim_cl:                           0
% 7.88/1.49  pred_elim_cycles:                       3
% 7.88/1.49  merged_defs:                            6
% 7.88/1.49  merged_defs_ncl:                        0
% 7.88/1.49  bin_hyper_res:                          6
% 7.88/1.49  prep_cycles:                            3
% 7.88/1.49  pred_elim_time:                         0.001
% 7.88/1.49  splitting_time:                         0.
% 7.88/1.49  sem_filter_time:                        0.
% 7.88/1.49  monotx_time:                            0.
% 7.88/1.49  subtype_inf_time:                       0.
% 7.88/1.49  
% 7.88/1.49  ------ Problem properties
% 7.88/1.49  
% 7.88/1.49  clauses:                                17
% 7.88/1.49  conjectures:                            2
% 7.88/1.49  epr:                                    1
% 7.88/1.49  horn:                                   15
% 7.88/1.49  ground:                                 2
% 7.88/1.49  unary:                                  10
% 7.88/1.49  binary:                                 7
% 7.88/1.49  lits:                                   24
% 7.88/1.49  lits_eq:                                11
% 7.88/1.49  fd_pure:                                0
% 7.88/1.49  fd_pseudo:                              0
% 7.88/1.49  fd_cond:                                1
% 7.88/1.49  fd_pseudo_cond:                         0
% 7.88/1.49  ac_symbols:                             1
% 7.88/1.49  
% 7.88/1.49  ------ Propositional Solver
% 7.88/1.49  
% 7.88/1.49  prop_solver_calls:                      30
% 7.88/1.49  prop_fast_solver_calls:                 521
% 7.88/1.49  smt_solver_calls:                       0
% 7.88/1.49  smt_fast_solver_calls:                  0
% 7.88/1.49  prop_num_of_clauses:                    9932
% 7.88/1.49  prop_preprocess_simplified:             8632
% 7.88/1.49  prop_fo_subsumed:                       1
% 7.88/1.49  prop_solver_time:                       0.
% 7.88/1.49  smt_solver_time:                        0.
% 7.88/1.49  smt_fast_solver_time:                   0.
% 7.88/1.49  prop_fast_solver_time:                  0.
% 7.88/1.49  prop_unsat_core_time:                   0.
% 7.88/1.49  
% 7.88/1.49  ------ QBF
% 7.88/1.49  
% 7.88/1.49  qbf_q_res:                              0
% 7.88/1.49  qbf_num_tautologies:                    0
% 7.88/1.49  qbf_prep_cycles:                        0
% 7.88/1.49  
% 7.88/1.49  ------ BMC1
% 7.88/1.49  
% 7.88/1.49  bmc1_current_bound:                     -1
% 7.88/1.49  bmc1_last_solved_bound:                 -1
% 7.88/1.49  bmc1_unsat_core_size:                   -1
% 7.88/1.49  bmc1_unsat_core_parents_size:           -1
% 7.88/1.49  bmc1_merge_next_fun:                    0
% 7.88/1.49  bmc1_unsat_core_clauses_time:           0.
% 7.88/1.49  
% 7.88/1.49  ------ Instantiation
% 7.88/1.49  
% 7.88/1.49  inst_num_of_clauses:                    1528
% 7.88/1.49  inst_num_in_passive:                    259
% 7.88/1.49  inst_num_in_active:                     814
% 7.88/1.49  inst_num_in_unprocessed:                457
% 7.88/1.49  inst_num_of_loops:                      1010
% 7.88/1.49  inst_num_of_learning_restarts:          0
% 7.88/1.49  inst_num_moves_active_passive:          189
% 7.88/1.49  inst_lit_activity:                      0
% 7.88/1.49  inst_lit_activity_moves:                0
% 7.88/1.49  inst_num_tautologies:                   0
% 7.88/1.49  inst_num_prop_implied:                  0
% 7.88/1.49  inst_num_existing_simplified:           0
% 7.88/1.49  inst_num_eq_res_simplified:             0
% 7.88/1.49  inst_num_child_elim:                    0
% 7.88/1.49  inst_num_of_dismatching_blockings:      531
% 7.88/1.49  inst_num_of_non_proper_insts:           2028
% 7.88/1.49  inst_num_of_duplicates:                 0
% 7.88/1.49  inst_inst_num_from_inst_to_res:         0
% 7.88/1.49  inst_dismatching_checking_time:         0.
% 7.88/1.49  
% 7.88/1.49  ------ Resolution
% 7.88/1.49  
% 7.88/1.49  res_num_of_clauses:                     0
% 7.88/1.49  res_num_in_passive:                     0
% 7.88/1.49  res_num_in_active:                      0
% 7.88/1.49  res_num_of_loops:                       69
% 7.88/1.49  res_forward_subset_subsumed:            244
% 7.88/1.49  res_backward_subset_subsumed:           4
% 7.88/1.49  res_forward_subsumed:                   0
% 7.88/1.49  res_backward_subsumed:                  0
% 7.88/1.49  res_forward_subsumption_resolution:     0
% 7.88/1.49  res_backward_subsumption_resolution:    0
% 7.88/1.49  res_clause_to_clause_subsumption:       28371
% 7.88/1.49  res_orphan_elimination:                 0
% 7.88/1.49  res_tautology_del:                      210
% 7.88/1.49  res_num_eq_res_simplified:              0
% 7.88/1.49  res_num_sel_changes:                    0
% 7.88/1.49  res_moves_from_active_to_pass:          0
% 7.88/1.49  
% 7.88/1.49  ------ Superposition
% 7.88/1.49  
% 7.88/1.49  sup_time_total:                         0.
% 7.88/1.49  sup_time_generating:                    0.
% 7.88/1.49  sup_time_sim_full:                      0.
% 7.88/1.49  sup_time_sim_immed:                     0.
% 7.88/1.49  
% 7.88/1.49  sup_num_of_clauses:                     2657
% 7.88/1.49  sup_num_in_active:                      186
% 7.88/1.49  sup_num_in_passive:                     2471
% 7.88/1.49  sup_num_of_loops:                       200
% 7.88/1.49  sup_fw_superposition:                   4800
% 7.88/1.49  sup_bw_superposition:                   5114
% 7.88/1.49  sup_immediate_simplified:               5563
% 7.88/1.49  sup_given_eliminated:                   6
% 7.88/1.49  comparisons_done:                       0
% 7.88/1.49  comparisons_avoided:                    0
% 7.88/1.49  
% 7.88/1.49  ------ Simplifications
% 7.88/1.49  
% 7.88/1.49  
% 7.88/1.49  sim_fw_subset_subsumed:                 67
% 7.88/1.49  sim_bw_subset_subsumed:                 8
% 7.88/1.49  sim_fw_subsumed:                        587
% 7.88/1.49  sim_bw_subsumed:                        25
% 7.88/1.49  sim_fw_subsumption_res:                 0
% 7.88/1.49  sim_bw_subsumption_res:                 0
% 7.88/1.49  sim_tautology_del:                      1
% 7.88/1.49  sim_eq_tautology_del:                   1288
% 7.88/1.49  sim_eq_res_simp:                        23
% 7.88/1.49  sim_fw_demodulated:                     5239
% 7.88/1.49  sim_bw_demodulated:                     121
% 7.88/1.49  sim_light_normalised:                   1945
% 7.88/1.49  sim_joinable_taut:                      96
% 7.88/1.49  sim_joinable_simp:                      0
% 7.88/1.49  sim_ac_normalised:                      0
% 7.88/1.49  sim_smt_subsumption:                    0
% 7.88/1.49  
%------------------------------------------------------------------------------
