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
% DateTime   : Thu Dec  3 11:24:34 EST 2020

% Result     : Timeout 59.37s
% Output     : None 
% Verified   : 
% Statistics : Number of formulae       :  161 (7115 expanded)
%              Number of clauses        :  129 (2869 expanded)
%              Number of leaves         :   13 (1956 expanded)
%              Depth                    :   36
%              Number of atoms          :  197 (7193 expanded)
%              Number of equality atoms :  169 (7118 expanded)
%              Maximal formula depth    :    7 (   2 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    7 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
     => r1_xboole_0(X1,k4_xboole_0(X0,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
       => r1_xboole_0(X1,k4_xboole_0(X0,X2)) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(X1,k4_xboole_0(X0,X2))
      & r1_xboole_0(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f14,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(X1,k4_xboole_0(X0,X2))
        & r1_xboole_0(X0,k4_xboole_0(X1,X2)) )
   => ( ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
      & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
    & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f14])).

fof(f26,plain,(
    r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f15])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f17,f24])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f32,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f23,f24])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f28,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f16,f24,f24])).

fof(f3,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f3])).

fof(f31,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f19,f24])).

fof(f9,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f18,f24])).

fof(f27,plain,(
    ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_4,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_10,negated_conjecture,
    ( r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_208,plain,
    ( r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_210,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_961,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_208,c_210])).

cnf(c_7,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_408,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(superposition,[status(thm)],[c_7,c_4])).

cnf(c_20186,plain,
    ( k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),sK0) = k2_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_961,c_408])).

cnf(c_5,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f21])).

cnf(c_20638,plain,
    ( k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)),sK0) = k2_xboole_0(sK0,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_20186,c_5,c_7])).

cnf(c_6,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_367,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = k2_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_6,c_4])).

cnf(c_21963,plain,
    ( k2_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)))) = k2_xboole_0(sK0,k4_xboole_0(X0,k2_xboole_0(sK0,k1_xboole_0))) ),
    inference(superposition,[status(thm)],[c_20638,c_367])).

cnf(c_370,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k1_xboole_0)) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_6,c_5])).

cnf(c_22014,plain,
    ( k2_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)))) = k2_xboole_0(sK0,X0) ),
    inference(demodulation,[status(thm)],[c_21963,c_4,c_370])).

cnf(c_0,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_3,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_218,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3,c_5])).

cnf(c_524,plain,
    ( k2_xboole_0(X0,X0) = k2_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_218,c_4])).

cnf(c_369,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_6,c_0])).

cnf(c_373,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2)))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
    inference(light_normalisation,[status(thm)],[c_369,c_6])).

cnf(c_6110,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,k1_xboole_0)))) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_524,c_373])).

cnf(c_6431,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))) = k4_xboole_0(X1,k2_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(light_normalisation,[status(thm)],[c_6110,c_370])).

cnf(c_525,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_218,c_6])).

cnf(c_527,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_525,c_4])).

cnf(c_6432,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6431,c_4,c_527])).

cnf(c_6716,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_6432,c_7])).

cnf(c_6751,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_6716,c_5])).

cnf(c_6763,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_0,c_6751])).

cnf(c_31350,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_6763,c_6])).

cnf(c_46077,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,sK2),k2_xboole_0(sK0,sK0)) = k4_xboole_0(k4_xboole_0(sK1,sK2),sK0) ),
    inference(superposition,[status(thm)],[c_22014,c_31350])).

cnf(c_398,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_0,c_7])).

cnf(c_20215,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0) = k4_xboole_0(k4_xboole_0(sK1,sK2),sK0) ),
    inference(superposition,[status(thm)],[c_961,c_398])).

cnf(c_20572,plain,
    ( k4_xboole_0(sK1,k2_xboole_0(sK2,sK0)) = k4_xboole_0(sK1,sK2) ),
    inference(demodulation,[status(thm)],[c_20215,c_6,c_370])).

cnf(c_46642,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,sK2),k2_xboole_0(sK0,sK0)) = k4_xboole_0(sK1,sK2) ),
    inference(demodulation,[status(thm)],[c_46077,c_6,c_20572])).

cnf(c_6813,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X0),X2)) = k4_xboole_0(X0,X2) ),
    inference(superposition,[status(thm)],[c_6751,c_6])).

cnf(c_523,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_218,c_6])).

cnf(c_8,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_532,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_523,c_8])).

cnf(c_817,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_532,c_4])).

cnf(c_368,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X2))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_6,c_0])).

cnf(c_4945,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),k1_xboole_0))) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2)))) ),
    inference(superposition,[status(thm)],[c_817,c_368])).

cnf(c_5208,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X0,k2_xboole_0(X1,X2)))) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2)))) ),
    inference(demodulation,[status(thm)],[c_4945,c_6,c_370])).

cnf(c_5209,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X0,X2)))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5208,c_4,c_527])).

cnf(c_7949,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X1) = k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_5209,c_398])).

cnf(c_364,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X3)) = k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X3) ),
    inference(superposition,[status(thm)],[c_6,c_6])).

cnf(c_380,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3))) ),
    inference(demodulation,[status(thm)],[c_364,c_6])).

cnf(c_7960,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X1) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,k1_xboole_0))) ),
    inference(demodulation,[status(thm)],[c_7949,c_6,c_380])).

cnf(c_1095,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_370,c_218])).

cnf(c_297,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_0,c_4])).

cnf(c_24337,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),X0),k2_xboole_0(X0,k1_xboole_0)) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,k1_xboole_0)))) ),
    inference(superposition,[status(thm)],[c_1095,c_297])).

cnf(c_24432,plain,
    ( k2_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,k1_xboole_0)))) = k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,k1_xboole_0)) ),
    inference(light_normalisation,[status(thm)],[c_24337,c_1095])).

cnf(c_818,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(k4_xboole_0(X0,X1),X2))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_532,c_6])).

cnf(c_2603,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5,c_818])).

cnf(c_6699,plain,
    ( k4_xboole_0(k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,X1)),k4_xboole_0(k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,X1)),k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2603,c_6432])).

cnf(c_361,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,X1)) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_5,c_6])).

cnf(c_6964,plain,
    ( k4_xboole_0(k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,X1)),k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6699,c_5,c_361])).

cnf(c_9403,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,X1)))) = k4_xboole_0(k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,X1)),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_6964,c_0])).

cnf(c_6766,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = X0 ),
    inference(superposition,[status(thm)],[c_6,c_6751])).

cnf(c_9429,plain,
    ( k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_9403,c_5,c_6766])).

cnf(c_933,plain,
    ( k4_xboole_0(k2_xboole_0(k1_xboole_0,X0),X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_361,c_218])).

cnf(c_930,plain,
    ( k4_xboole_0(k2_xboole_0(k1_xboole_0,X0),k4_xboole_0(k2_xboole_0(k1_xboole_0,X0),X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_361,c_0])).

cnf(c_19439,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = k4_xboole_0(k2_xboole_0(k1_xboole_0,X0),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_933,c_930])).

cnf(c_19451,plain,
    ( k4_xboole_0(k2_xboole_0(k1_xboole_0,X0),k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_19439,c_5,c_218])).

cnf(c_19831,plain,
    ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_19451,c_5])).

cnf(c_24434,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(demodulation,[status(thm)],[c_24432,c_5,c_532,c_9429,c_19831])).

cnf(c_146538,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X1) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_7960,c_6,c_24434])).

cnf(c_146620,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X0)) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X2,X0),X1)) ),
    inference(superposition,[status(thm)],[c_6813,c_146538])).

cnf(c_147400,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X0)) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_146620,c_6,c_6813])).

cnf(c_147899,plain,
    ( k4_xboole_0(k4_xboole_0(k2_xboole_0(sK0,sK0),X0),k4_xboole_0(sK1,sK2)) = k4_xboole_0(k2_xboole_0(sK0,sK0),X0) ),
    inference(superposition,[status(thm)],[c_46642,c_147400])).

cnf(c_4939,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X1))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_524,c_368])).

cnf(c_5228,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X1))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4939,c_6,c_8])).

cnf(c_9411,plain,
    ( k4_xboole_0(k4_xboole_0(k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,X0)),X0),k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6964,c_5228])).

cnf(c_9681,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X0),k2_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_9411,c_6,c_9429])).

cnf(c_407,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_7,c_6])).

cnf(c_418,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_407,c_6])).

cnf(c_11319,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X0),k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X0),k1_xboole_0),X1)) = k4_xboole_0(k2_xboole_0(X0,X0),k2_xboole_0(k2_xboole_0(X0,k1_xboole_0),X1)) ),
    inference(superposition,[status(thm)],[c_9681,c_418])).

cnf(c_9892,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X0),k2_xboole_0(k2_xboole_0(X0,k1_xboole_0),X1)) = k4_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_9681,c_6])).

cnf(c_9945,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X0),k2_xboole_0(k2_xboole_0(X0,k1_xboole_0),X1)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_9892,c_8,c_380])).

cnf(c_11455,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X0),k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X0),k1_xboole_0),X1)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_11319,c_9945])).

cnf(c_11456,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X0),k2_xboole_0(X0,k2_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_11455,c_5,c_380])).

cnf(c_11660,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X0),k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(X0,X1)),X2)) = k4_xboole_0(k1_xboole_0,X2) ),
    inference(superposition,[status(thm)],[c_11456,c_6])).

cnf(c_11695,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X0),k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(X0,X1)),X2)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_11660,c_8,c_380])).

cnf(c_36482,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X0),k4_xboole_0(k2_xboole_0(X0,X0),k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(X0,X1)),X2))),k2_xboole_0(X0,X0)) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X0),k1_xboole_0),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_11695,c_408])).

cnf(c_36582,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X0),k1_xboole_0),k2_xboole_0(X0,X0)) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X0),k1_xboole_0),k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_36482,c_11695])).

cnf(c_36584,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X0),k2_xboole_0(X0,X0)) = k2_xboole_0(X0,X0) ),
    inference(demodulation,[status(thm)],[c_36582,c_5,c_24434])).

cnf(c_7213,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,k2_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_4,c_6766])).

cnf(c_36667,plain,
    ( k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X0),k2_xboole_0(X0,X0)),k4_xboole_0(X1,k2_xboole_0(X0,X0))) = k4_xboole_0(k2_xboole_0(X0,X0),k2_xboole_0(X0,X0)) ),
    inference(superposition,[status(thm)],[c_36584,c_7213])).

cnf(c_1087,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,X1)) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_524,c_370])).

cnf(c_36791,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X0),k2_xboole_0(X0,k4_xboole_0(X1,X0))) = k4_xboole_0(k2_xboole_0(X0,X0),X0) ),
    inference(demodulation,[status(thm)],[c_36667,c_6,c_1087])).

cnf(c_36792,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X0),k2_xboole_0(X0,X1)) = k4_xboole_0(k2_xboole_0(X0,X0),X0) ),
    inference(light_normalisation,[status(thm)],[c_36791,c_4])).

cnf(c_359,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
    inference(superposition,[status(thm)],[c_0,c_6])).

cnf(c_53351,plain,
    ( k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X0))),X2) = k4_xboole_0(k2_xboole_0(X0,X0),k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X0),X0),X2)) ),
    inference(superposition,[status(thm)],[c_36792,c_359])).

cnf(c_53368,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X0)),X2)) = k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X0),k4_xboole_0(k2_xboole_0(X0,X0),X0)),X2) ),
    inference(superposition,[status(thm)],[c_36792,c_359])).

cnf(c_7184,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X3,X0)))) = X0 ),
    inference(superposition,[status(thm)],[c_6,c_6766])).

cnf(c_53403,plain,
    ( k4_xboole_0(X0,k4_xboole_0(k2_xboole_0(X1,X1),X1)) = X0 ),
    inference(superposition,[status(thm)],[c_36792,c_7184])).

cnf(c_53464,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X0)),X2)) = k4_xboole_0(k2_xboole_0(X0,X0),X2) ),
    inference(demodulation,[status(thm)],[c_53368,c_53403])).

cnf(c_53466,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X0),X2)) = k4_xboole_0(k2_xboole_0(X0,X0),X2) ),
    inference(demodulation,[status(thm)],[c_53464,c_1087])).

cnf(c_53502,plain,
    ( k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X0))),X2) = k4_xboole_0(k2_xboole_0(X0,X0),X2) ),
    inference(demodulation,[status(thm)],[c_53351,c_53466])).

cnf(c_784,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4,c_527])).

cnf(c_1118,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k2_xboole_0(k4_xboole_0(X1,X0),X1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_784])).

cnf(c_14596,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k1_xboole_0),k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X0),k2_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_532,c_1118])).

cnf(c_15026,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X0),k2_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_14596,c_5])).

cnf(c_41963,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(k2_xboole_0(X0,X1),X0)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(k2_xboole_0(X0,X1),X0)),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_15026,c_368])).

cnf(c_41989,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),X0)) = X0 ),
    inference(demodulation,[status(thm)],[c_41963,c_6,c_6751,c_24434])).

cnf(c_53504,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X0),X1) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_53502,c_6,c_1087,c_41989])).

cnf(c_148404,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(X0,k4_xboole_0(sK1,sK2))) = k4_xboole_0(sK0,X0) ),
    inference(demodulation,[status(thm)],[c_147899,c_6,c_53504])).

cnf(c_149308,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(sK2,sK1)) = k4_xboole_0(sK0,sK2) ),
    inference(superposition,[status(thm)],[c_4,c_148404])).

cnf(c_1,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_211,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1433,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X2))) != k1_xboole_0
    | r1_xboole_0(k4_xboole_0(X0,X1),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_211])).

cnf(c_1493,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2)))) != k1_xboole_0
    | r1_xboole_0(k4_xboole_0(X0,X1),X2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1433,c_6])).

cnf(c_150003,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(sK2,k4_xboole_0(sK0,sK2))) != k1_xboole_0
    | r1_xboole_0(k4_xboole_0(sK0,sK2),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_149308,c_1493])).

cnf(c_150070,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(k4_xboole_0(sK0,sK2),sK1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_150003,c_4,c_527])).

cnf(c_150071,plain,
    ( r1_xboole_0(k4_xboole_0(sK0,sK2),sK1) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_150070])).

cnf(c_497,plain,
    ( ~ r1_xboole_0(k4_xboole_0(sK0,sK2),sK1)
    | k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(k4_xboole_0(sK0,sK2),sK1)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_498,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(k4_xboole_0(sK0,sK2),sK1)) = k1_xboole_0
    | r1_xboole_0(k4_xboole_0(sK0,sK2),sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_497])).

cnf(c_72,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_343,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(k4_xboole_0(sK0,sK2),sK1)) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(k4_xboole_0(sK0,sK2),sK1)) ),
    inference(instantiation,[status(thm)],[c_72])).

cnf(c_344,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(k4_xboole_0(sK0,sK2),sK1)) != k1_xboole_0
    | k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(k4_xboole_0(sK0,sK2),sK1))
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_343])).

cnf(c_320,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK2))) = k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(k4_xboole_0(sK0,sK2),sK1)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_278,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK2))) != X0
    | k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK2))) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_72])).

cnf(c_319,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK2))) != k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(k4_xboole_0(sK0,sK2),sK1))
    | k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK2))) = k1_xboole_0
    | k1_xboole_0 != k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(k4_xboole_0(sK0,sK2),sK1)) ),
    inference(instantiation,[status(thm)],[c_278])).

cnf(c_258,plain,
    ( r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
    | k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK2))) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_71,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_80,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_71])).

cnf(c_9,negated_conjecture,
    ( ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
    inference(cnf_transformation,[],[f27])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_150071,c_498,c_344,c_320,c_319,c_258,c_80,c_9])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:14:14 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 59.37/8.03  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 59.37/8.03  
% 59.37/8.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 59.37/8.03  
% 59.37/8.03  ------  iProver source info
% 59.37/8.03  
% 59.37/8.03  git: date: 2020-06-30 10:37:57 +0100
% 59.37/8.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 59.37/8.03  git: non_committed_changes: false
% 59.37/8.03  git: last_make_outside_of_git: false
% 59.37/8.03  
% 59.37/8.03  ------ 
% 59.37/8.03  
% 59.37/8.03  ------ Input Options
% 59.37/8.03  
% 59.37/8.03  --out_options                           all
% 59.37/8.03  --tptp_safe_out                         true
% 59.37/8.03  --problem_path                          ""
% 59.37/8.03  --include_path                          ""
% 59.37/8.03  --clausifier                            res/vclausify_rel
% 59.37/8.03  --clausifier_options                    --mode clausify
% 59.37/8.03  --stdin                                 false
% 59.37/8.03  --stats_out                             sel
% 59.37/8.03  
% 59.37/8.03  ------ General Options
% 59.37/8.03  
% 59.37/8.03  --fof                                   false
% 59.37/8.03  --time_out_real                         604.99
% 59.37/8.03  --time_out_virtual                      -1.
% 59.37/8.03  --symbol_type_check                     false
% 59.37/8.03  --clausify_out                          false
% 59.37/8.03  --sig_cnt_out                           false
% 59.37/8.03  --trig_cnt_out                          false
% 59.37/8.03  --trig_cnt_out_tolerance                1.
% 59.37/8.03  --trig_cnt_out_sk_spl                   false
% 59.37/8.03  --abstr_cl_out                          false
% 59.37/8.03  
% 59.37/8.03  ------ Global Options
% 59.37/8.03  
% 59.37/8.03  --schedule                              none
% 59.37/8.03  --add_important_lit                     false
% 59.37/8.03  --prop_solver_per_cl                    1000
% 59.37/8.03  --min_unsat_core                        false
% 59.37/8.03  --soft_assumptions                      false
% 59.37/8.03  --soft_lemma_size                       3
% 59.37/8.03  --prop_impl_unit_size                   0
% 59.37/8.03  --prop_impl_unit                        []
% 59.37/8.03  --share_sel_clauses                     true
% 59.37/8.03  --reset_solvers                         false
% 59.37/8.03  --bc_imp_inh                            [conj_cone]
% 59.37/8.03  --conj_cone_tolerance                   3.
% 59.37/8.03  --extra_neg_conj                        none
% 59.37/8.03  --large_theory_mode                     true
% 59.37/8.03  --prolific_symb_bound                   200
% 59.37/8.03  --lt_threshold                          2000
% 59.37/8.03  --clause_weak_htbl                      true
% 59.37/8.03  --gc_record_bc_elim                     false
% 59.37/8.03  
% 59.37/8.03  ------ Preprocessing Options
% 59.37/8.03  
% 59.37/8.03  --preprocessing_flag                    true
% 59.37/8.03  --time_out_prep_mult                    0.1
% 59.37/8.03  --splitting_mode                        input
% 59.37/8.03  --splitting_grd                         true
% 59.37/8.03  --splitting_cvd                         false
% 59.37/8.03  --splitting_cvd_svl                     false
% 59.37/8.03  --splitting_nvd                         32
% 59.37/8.03  --sub_typing                            true
% 59.37/8.03  --prep_gs_sim                           false
% 59.37/8.03  --prep_unflatten                        true
% 59.37/8.03  --prep_res_sim                          true
% 59.37/8.03  --prep_upred                            true
% 59.37/8.03  --prep_sem_filter                       exhaustive
% 59.37/8.03  --prep_sem_filter_out                   false
% 59.37/8.03  --pred_elim                             false
% 59.37/8.03  --res_sim_input                         true
% 59.37/8.03  --eq_ax_congr_red                       true
% 59.37/8.03  --pure_diseq_elim                       true
% 59.37/8.03  --brand_transform                       false
% 59.37/8.03  --non_eq_to_eq                          false
% 59.37/8.03  --prep_def_merge                        true
% 59.37/8.03  --prep_def_merge_prop_impl              false
% 59.37/8.03  --prep_def_merge_mbd                    true
% 59.37/8.03  --prep_def_merge_tr_red                 false
% 59.37/8.03  --prep_def_merge_tr_cl                  false
% 59.37/8.03  --smt_preprocessing                     true
% 59.37/8.03  --smt_ac_axioms                         fast
% 59.37/8.03  --preprocessed_out                      false
% 59.37/8.03  --preprocessed_stats                    false
% 59.37/8.03  
% 59.37/8.03  ------ Abstraction refinement Options
% 59.37/8.03  
% 59.37/8.03  --abstr_ref                             []
% 59.37/8.03  --abstr_ref_prep                        false
% 59.37/8.03  --abstr_ref_until_sat                   false
% 59.37/8.03  --abstr_ref_sig_restrict                funpre
% 59.37/8.03  --abstr_ref_af_restrict_to_split_sk     false
% 59.37/8.03  --abstr_ref_under                       []
% 59.37/8.03  
% 59.37/8.03  ------ SAT Options
% 59.37/8.03  
% 59.37/8.03  --sat_mode                              false
% 59.37/8.03  --sat_fm_restart_options                ""
% 59.37/8.03  --sat_gr_def                            false
% 59.37/8.03  --sat_epr_types                         true
% 59.37/8.03  --sat_non_cyclic_types                  false
% 59.37/8.03  --sat_finite_models                     false
% 59.37/8.03  --sat_fm_lemmas                         false
% 59.37/8.03  --sat_fm_prep                           false
% 59.37/8.03  --sat_fm_uc_incr                        true
% 59.37/8.03  --sat_out_model                         small
% 59.37/8.03  --sat_out_clauses                       false
% 59.37/8.03  
% 59.37/8.03  ------ QBF Options
% 59.37/8.03  
% 59.37/8.03  --qbf_mode                              false
% 59.37/8.03  --qbf_elim_univ                         false
% 59.37/8.03  --qbf_dom_inst                          none
% 59.37/8.03  --qbf_dom_pre_inst                      false
% 59.37/8.03  --qbf_sk_in                             false
% 59.37/8.03  --qbf_pred_elim                         true
% 59.37/8.03  --qbf_split                             512
% 59.37/8.03  
% 59.37/8.03  ------ BMC1 Options
% 59.37/8.03  
% 59.37/8.03  --bmc1_incremental                      false
% 59.37/8.03  --bmc1_axioms                           reachable_all
% 59.37/8.03  --bmc1_min_bound                        0
% 59.37/8.03  --bmc1_max_bound                        -1
% 59.37/8.03  --bmc1_max_bound_default                -1
% 59.37/8.03  --bmc1_symbol_reachability              true
% 59.37/8.03  --bmc1_property_lemmas                  false
% 59.37/8.03  --bmc1_k_induction                      false
% 59.37/8.03  --bmc1_non_equiv_states                 false
% 59.37/8.03  --bmc1_deadlock                         false
% 59.37/8.03  --bmc1_ucm                              false
% 59.37/8.03  --bmc1_add_unsat_core                   none
% 59.37/8.03  --bmc1_unsat_core_children              false
% 59.37/8.03  --bmc1_unsat_core_extrapolate_axioms    false
% 59.37/8.03  --bmc1_out_stat                         full
% 59.37/8.03  --bmc1_ground_init                      false
% 59.37/8.03  --bmc1_pre_inst_next_state              false
% 59.37/8.03  --bmc1_pre_inst_state                   false
% 59.37/8.03  --bmc1_pre_inst_reach_state             false
% 59.37/8.03  --bmc1_out_unsat_core                   false
% 59.37/8.03  --bmc1_aig_witness_out                  false
% 59.37/8.03  --bmc1_verbose                          false
% 59.37/8.03  --bmc1_dump_clauses_tptp                false
% 59.37/8.03  --bmc1_dump_unsat_core_tptp             false
% 59.37/8.03  --bmc1_dump_file                        -
% 59.37/8.03  --bmc1_ucm_expand_uc_limit              128
% 59.37/8.03  --bmc1_ucm_n_expand_iterations          6
% 59.37/8.03  --bmc1_ucm_extend_mode                  1
% 59.37/8.03  --bmc1_ucm_init_mode                    2
% 59.37/8.03  --bmc1_ucm_cone_mode                    none
% 59.37/8.03  --bmc1_ucm_reduced_relation_type        0
% 59.37/8.03  --bmc1_ucm_relax_model                  4
% 59.37/8.03  --bmc1_ucm_full_tr_after_sat            true
% 59.37/8.03  --bmc1_ucm_expand_neg_assumptions       false
% 59.37/8.03  --bmc1_ucm_layered_model                none
% 59.37/8.03  --bmc1_ucm_max_lemma_size               10
% 59.37/8.03  
% 59.37/8.03  ------ AIG Options
% 59.37/8.03  
% 59.37/8.03  --aig_mode                              false
% 59.37/8.03  
% 59.37/8.03  ------ Instantiation Options
% 59.37/8.03  
% 59.37/8.03  --instantiation_flag                    true
% 59.37/8.03  --inst_sos_flag                         false
% 59.37/8.03  --inst_sos_phase                        true
% 59.37/8.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 59.37/8.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 59.37/8.03  --inst_lit_sel_side                     num_symb
% 59.37/8.03  --inst_solver_per_active                1400
% 59.37/8.03  --inst_solver_calls_frac                1.
% 59.37/8.03  --inst_passive_queue_type               priority_queues
% 59.37/8.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 59.37/8.03  --inst_passive_queues_freq              [25;2]
% 59.37/8.03  --inst_dismatching                      true
% 59.37/8.03  --inst_eager_unprocessed_to_passive     true
% 59.37/8.03  --inst_prop_sim_given                   true
% 59.37/8.03  --inst_prop_sim_new                     false
% 59.37/8.03  --inst_subs_new                         false
% 59.37/8.03  --inst_eq_res_simp                      false
% 59.37/8.03  --inst_subs_given                       false
% 59.37/8.03  --inst_orphan_elimination               true
% 59.37/8.03  --inst_learning_loop_flag               true
% 59.37/8.03  --inst_learning_start                   3000
% 59.37/8.03  --inst_learning_factor                  2
% 59.37/8.03  --inst_start_prop_sim_after_learn       3
% 59.37/8.03  --inst_sel_renew                        solver
% 59.37/8.03  --inst_lit_activity_flag                true
% 59.37/8.03  --inst_restr_to_given                   false
% 59.37/8.03  --inst_activity_threshold               500
% 59.37/8.03  --inst_out_proof                        true
% 59.37/8.03  
% 59.37/8.03  ------ Resolution Options
% 59.37/8.03  
% 59.37/8.03  --resolution_flag                       true
% 59.37/8.03  --res_lit_sel                           adaptive
% 59.37/8.03  --res_lit_sel_side                      none
% 59.37/8.03  --res_ordering                          kbo
% 59.37/8.03  --res_to_prop_solver                    active
% 59.37/8.03  --res_prop_simpl_new                    false
% 59.37/8.03  --res_prop_simpl_given                  true
% 59.37/8.03  --res_passive_queue_type                priority_queues
% 59.37/8.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 59.37/8.03  --res_passive_queues_freq               [15;5]
% 59.37/8.03  --res_forward_subs                      full
% 59.37/8.03  --res_backward_subs                     full
% 59.37/8.03  --res_forward_subs_resolution           true
% 59.37/8.03  --res_backward_subs_resolution          true
% 59.37/8.03  --res_orphan_elimination                true
% 59.37/8.03  --res_time_limit                        2.
% 59.37/8.03  --res_out_proof                         true
% 59.37/8.03  
% 59.37/8.03  ------ Superposition Options
% 59.37/8.03  
% 59.37/8.03  --superposition_flag                    true
% 59.37/8.03  --sup_passive_queue_type                priority_queues
% 59.37/8.03  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 59.37/8.03  --sup_passive_queues_freq               [1;4]
% 59.37/8.03  --demod_completeness_check              fast
% 59.37/8.03  --demod_use_ground                      true
% 59.37/8.03  --sup_to_prop_solver                    passive
% 59.37/8.03  --sup_prop_simpl_new                    true
% 59.37/8.03  --sup_prop_simpl_given                  true
% 59.37/8.03  --sup_fun_splitting                     false
% 59.37/8.03  --sup_smt_interval                      50000
% 59.37/8.03  
% 59.37/8.03  ------ Superposition Simplification Setup
% 59.37/8.03  
% 59.37/8.03  --sup_indices_passive                   []
% 59.37/8.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 59.37/8.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 59.37/8.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 59.37/8.03  --sup_full_triv                         [TrivRules;PropSubs]
% 59.37/8.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 59.37/8.03  --sup_full_bw                           [BwDemod]
% 59.37/8.03  --sup_immed_triv                        [TrivRules]
% 59.37/8.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 59.37/8.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 59.37/8.03  --sup_immed_bw_main                     []
% 59.37/8.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 59.37/8.03  --sup_input_triv                        [Unflattening;TrivRules]
% 59.37/8.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 59.37/8.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 59.37/8.03  
% 59.37/8.03  ------ Combination Options
% 59.37/8.03  
% 59.37/8.03  --comb_res_mult                         3
% 59.37/8.03  --comb_sup_mult                         2
% 59.37/8.03  --comb_inst_mult                        10
% 59.37/8.03  
% 59.37/8.03  ------ Debug Options
% 59.37/8.03  
% 59.37/8.03  --dbg_backtrace                         false
% 59.37/8.03  --dbg_dump_prop_clauses                 false
% 59.37/8.03  --dbg_dump_prop_clauses_file            -
% 59.37/8.03  --dbg_out_stat                          false
% 59.37/8.03  ------ Parsing...
% 59.37/8.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 59.37/8.03  
% 59.37/8.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 59.37/8.03  
% 59.37/8.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 59.37/8.03  
% 59.37/8.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 59.37/8.03  ------ Proving...
% 59.37/8.03  ------ Problem Properties 
% 59.37/8.03  
% 59.37/8.03  
% 59.37/8.03  clauses                                 11
% 59.37/8.03  conjectures                             2
% 59.37/8.03  EPR                                     0
% 59.37/8.03  Horn                                    11
% 59.37/8.03  unary                                   9
% 59.37/8.03  binary                                  2
% 59.37/8.03  lits                                    13
% 59.37/8.03  lits eq                                 9
% 59.37/8.03  fd_pure                                 0
% 59.37/8.03  fd_pseudo                               0
% 59.37/8.03  fd_cond                                 0
% 59.37/8.03  fd_pseudo_cond                          0
% 59.37/8.03  AC symbols                              0
% 59.37/8.03  
% 59.37/8.03  ------ Input Options Time Limit: Unbounded
% 59.37/8.03  
% 59.37/8.03  
% 59.37/8.03  ------ 
% 59.37/8.03  Current options:
% 59.37/8.03  ------ 
% 59.37/8.03  
% 59.37/8.03  ------ Input Options
% 59.37/8.03  
% 59.37/8.03  --out_options                           all
% 59.37/8.03  --tptp_safe_out                         true
% 59.37/8.03  --problem_path                          ""
% 59.37/8.03  --include_path                          ""
% 59.37/8.03  --clausifier                            res/vclausify_rel
% 59.37/8.03  --clausifier_options                    --mode clausify
% 59.37/8.03  --stdin                                 false
% 59.37/8.03  --stats_out                             sel
% 59.37/8.03  
% 59.37/8.03  ------ General Options
% 59.37/8.03  
% 59.37/8.03  --fof                                   false
% 59.37/8.03  --time_out_real                         604.99
% 59.37/8.03  --time_out_virtual                      -1.
% 59.37/8.03  --symbol_type_check                     false
% 59.37/8.03  --clausify_out                          false
% 59.37/8.03  --sig_cnt_out                           false
% 59.37/8.03  --trig_cnt_out                          false
% 59.37/8.03  --trig_cnt_out_tolerance                1.
% 59.37/8.03  --trig_cnt_out_sk_spl                   false
% 59.37/8.03  --abstr_cl_out                          false
% 59.37/8.03  
% 59.37/8.03  ------ Global Options
% 59.37/8.03  
% 59.37/8.03  --schedule                              none
% 59.37/8.03  --add_important_lit                     false
% 59.37/8.03  --prop_solver_per_cl                    1000
% 59.37/8.03  --min_unsat_core                        false
% 59.37/8.03  --soft_assumptions                      false
% 59.37/8.03  --soft_lemma_size                       3
% 59.37/8.03  --prop_impl_unit_size                   0
% 59.37/8.03  --prop_impl_unit                        []
% 59.37/8.03  --share_sel_clauses                     true
% 59.37/8.03  --reset_solvers                         false
% 59.37/8.03  --bc_imp_inh                            [conj_cone]
% 59.37/8.03  --conj_cone_tolerance                   3.
% 59.37/8.03  --extra_neg_conj                        none
% 59.37/8.03  --large_theory_mode                     true
% 59.37/8.03  --prolific_symb_bound                   200
% 59.37/8.03  --lt_threshold                          2000
% 59.37/8.03  --clause_weak_htbl                      true
% 59.37/8.03  --gc_record_bc_elim                     false
% 59.37/8.03  
% 59.37/8.03  ------ Preprocessing Options
% 59.37/8.03  
% 59.37/8.03  --preprocessing_flag                    true
% 59.37/8.03  --time_out_prep_mult                    0.1
% 59.37/8.03  --splitting_mode                        input
% 59.37/8.03  --splitting_grd                         true
% 59.37/8.03  --splitting_cvd                         false
% 59.37/8.03  --splitting_cvd_svl                     false
% 59.37/8.03  --splitting_nvd                         32
% 59.37/8.03  --sub_typing                            true
% 59.37/8.03  --prep_gs_sim                           false
% 59.37/8.03  --prep_unflatten                        true
% 59.37/8.03  --prep_res_sim                          true
% 59.37/8.03  --prep_upred                            true
% 59.37/8.03  --prep_sem_filter                       exhaustive
% 59.37/8.03  --prep_sem_filter_out                   false
% 59.37/8.03  --pred_elim                             false
% 59.37/8.03  --res_sim_input                         true
% 59.37/8.03  --eq_ax_congr_red                       true
% 59.37/8.03  --pure_diseq_elim                       true
% 59.37/8.03  --brand_transform                       false
% 59.37/8.03  --non_eq_to_eq                          false
% 59.37/8.03  --prep_def_merge                        true
% 59.37/8.03  --prep_def_merge_prop_impl              false
% 59.37/8.03  --prep_def_merge_mbd                    true
% 59.37/8.03  --prep_def_merge_tr_red                 false
% 59.37/8.03  --prep_def_merge_tr_cl                  false
% 59.37/8.03  --smt_preprocessing                     true
% 59.37/8.03  --smt_ac_axioms                         fast
% 59.37/8.03  --preprocessed_out                      false
% 59.37/8.03  --preprocessed_stats                    false
% 59.37/8.03  
% 59.37/8.03  ------ Abstraction refinement Options
% 59.37/8.03  
% 59.37/8.03  --abstr_ref                             []
% 59.37/8.03  --abstr_ref_prep                        false
% 59.37/8.03  --abstr_ref_until_sat                   false
% 59.37/8.03  --abstr_ref_sig_restrict                funpre
% 59.37/8.03  --abstr_ref_af_restrict_to_split_sk     false
% 59.37/8.03  --abstr_ref_under                       []
% 59.37/8.03  
% 59.37/8.03  ------ SAT Options
% 59.37/8.03  
% 59.37/8.03  --sat_mode                              false
% 59.37/8.03  --sat_fm_restart_options                ""
% 59.37/8.03  --sat_gr_def                            false
% 59.37/8.03  --sat_epr_types                         true
% 59.37/8.03  --sat_non_cyclic_types                  false
% 59.37/8.03  --sat_finite_models                     false
% 59.37/8.03  --sat_fm_lemmas                         false
% 59.37/8.03  --sat_fm_prep                           false
% 59.37/8.03  --sat_fm_uc_incr                        true
% 59.37/8.03  --sat_out_model                         small
% 59.37/8.03  --sat_out_clauses                       false
% 59.37/8.03  
% 59.37/8.03  ------ QBF Options
% 59.37/8.03  
% 59.37/8.03  --qbf_mode                              false
% 59.37/8.03  --qbf_elim_univ                         false
% 59.37/8.03  --qbf_dom_inst                          none
% 59.37/8.03  --qbf_dom_pre_inst                      false
% 59.37/8.03  --qbf_sk_in                             false
% 59.37/8.03  --qbf_pred_elim                         true
% 59.37/8.03  --qbf_split                             512
% 59.37/8.03  
% 59.37/8.03  ------ BMC1 Options
% 59.37/8.03  
% 59.37/8.03  --bmc1_incremental                      false
% 59.37/8.03  --bmc1_axioms                           reachable_all
% 59.37/8.03  --bmc1_min_bound                        0
% 59.37/8.03  --bmc1_max_bound                        -1
% 59.37/8.03  --bmc1_max_bound_default                -1
% 59.37/8.03  --bmc1_symbol_reachability              true
% 59.37/8.03  --bmc1_property_lemmas                  false
% 59.37/8.03  --bmc1_k_induction                      false
% 59.37/8.03  --bmc1_non_equiv_states                 false
% 59.37/8.03  --bmc1_deadlock                         false
% 59.37/8.03  --bmc1_ucm                              false
% 59.37/8.03  --bmc1_add_unsat_core                   none
% 59.37/8.03  --bmc1_unsat_core_children              false
% 59.37/8.03  --bmc1_unsat_core_extrapolate_axioms    false
% 59.37/8.03  --bmc1_out_stat                         full
% 59.37/8.03  --bmc1_ground_init                      false
% 59.37/8.03  --bmc1_pre_inst_next_state              false
% 59.37/8.03  --bmc1_pre_inst_state                   false
% 59.37/8.03  --bmc1_pre_inst_reach_state             false
% 59.37/8.03  --bmc1_out_unsat_core                   false
% 59.37/8.03  --bmc1_aig_witness_out                  false
% 59.37/8.03  --bmc1_verbose                          false
% 59.37/8.03  --bmc1_dump_clauses_tptp                false
% 59.37/8.03  --bmc1_dump_unsat_core_tptp             false
% 59.37/8.03  --bmc1_dump_file                        -
% 59.37/8.03  --bmc1_ucm_expand_uc_limit              128
% 59.37/8.03  --bmc1_ucm_n_expand_iterations          6
% 59.37/8.03  --bmc1_ucm_extend_mode                  1
% 59.37/8.03  --bmc1_ucm_init_mode                    2
% 59.37/8.03  --bmc1_ucm_cone_mode                    none
% 59.37/8.03  --bmc1_ucm_reduced_relation_type        0
% 59.37/8.03  --bmc1_ucm_relax_model                  4
% 59.37/8.03  --bmc1_ucm_full_tr_after_sat            true
% 59.37/8.03  --bmc1_ucm_expand_neg_assumptions       false
% 59.37/8.03  --bmc1_ucm_layered_model                none
% 59.37/8.03  --bmc1_ucm_max_lemma_size               10
% 59.37/8.03  
% 59.37/8.03  ------ AIG Options
% 59.37/8.03  
% 59.37/8.03  --aig_mode                              false
% 59.37/8.03  
% 59.37/8.03  ------ Instantiation Options
% 59.37/8.03  
% 59.37/8.03  --instantiation_flag                    true
% 59.37/8.03  --inst_sos_flag                         false
% 59.37/8.03  --inst_sos_phase                        true
% 59.37/8.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 59.37/8.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 59.37/8.03  --inst_lit_sel_side                     num_symb
% 59.37/8.03  --inst_solver_per_active                1400
% 59.37/8.03  --inst_solver_calls_frac                1.
% 59.37/8.03  --inst_passive_queue_type               priority_queues
% 59.37/8.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 59.37/8.03  --inst_passive_queues_freq              [25;2]
% 59.37/8.03  --inst_dismatching                      true
% 59.37/8.03  --inst_eager_unprocessed_to_passive     true
% 59.37/8.03  --inst_prop_sim_given                   true
% 59.37/8.03  --inst_prop_sim_new                     false
% 59.37/8.03  --inst_subs_new                         false
% 59.37/8.03  --inst_eq_res_simp                      false
% 59.37/8.03  --inst_subs_given                       false
% 59.37/8.03  --inst_orphan_elimination               true
% 59.37/8.03  --inst_learning_loop_flag               true
% 59.37/8.03  --inst_learning_start                   3000
% 59.37/8.03  --inst_learning_factor                  2
% 59.37/8.03  --inst_start_prop_sim_after_learn       3
% 59.37/8.03  --inst_sel_renew                        solver
% 59.37/8.03  --inst_lit_activity_flag                true
% 59.37/8.03  --inst_restr_to_given                   false
% 59.37/8.03  --inst_activity_threshold               500
% 59.37/8.03  --inst_out_proof                        true
% 59.37/8.03  
% 59.37/8.03  ------ Resolution Options
% 59.37/8.03  
% 59.37/8.03  --resolution_flag                       true
% 59.37/8.03  --res_lit_sel                           adaptive
% 59.37/8.03  --res_lit_sel_side                      none
% 59.37/8.03  --res_ordering                          kbo
% 59.37/8.03  --res_to_prop_solver                    active
% 59.37/8.03  --res_prop_simpl_new                    false
% 59.37/8.03  --res_prop_simpl_given                  true
% 59.37/8.03  --res_passive_queue_type                priority_queues
% 59.37/8.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 59.37/8.03  --res_passive_queues_freq               [15;5]
% 59.37/8.03  --res_forward_subs                      full
% 59.37/8.03  --res_backward_subs                     full
% 59.37/8.03  --res_forward_subs_resolution           true
% 59.37/8.03  --res_backward_subs_resolution          true
% 59.37/8.03  --res_orphan_elimination                true
% 59.37/8.03  --res_time_limit                        2.
% 59.37/8.03  --res_out_proof                         true
% 59.37/8.03  
% 59.37/8.03  ------ Superposition Options
% 59.37/8.03  
% 59.37/8.03  --superposition_flag                    true
% 59.37/8.03  --sup_passive_queue_type                priority_queues
% 59.37/8.03  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 59.37/8.03  --sup_passive_queues_freq               [1;4]
% 59.37/8.03  --demod_completeness_check              fast
% 59.37/8.03  --demod_use_ground                      true
% 59.37/8.03  --sup_to_prop_solver                    passive
% 59.37/8.03  --sup_prop_simpl_new                    true
% 59.37/8.03  --sup_prop_simpl_given                  true
% 59.37/8.03  --sup_fun_splitting                     false
% 59.37/8.03  --sup_smt_interval                      50000
% 59.37/8.03  
% 59.37/8.03  ------ Superposition Simplification Setup
% 59.37/8.03  
% 59.37/8.03  --sup_indices_passive                   []
% 59.37/8.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 59.37/8.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 59.37/8.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 59.37/8.03  --sup_full_triv                         [TrivRules;PropSubs]
% 59.37/8.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 59.37/8.03  --sup_full_bw                           [BwDemod]
% 59.37/8.03  --sup_immed_triv                        [TrivRules]
% 59.37/8.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 59.37/8.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 59.37/8.03  --sup_immed_bw_main                     []
% 59.37/8.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 59.37/8.03  --sup_input_triv                        [Unflattening;TrivRules]
% 59.37/8.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 59.37/8.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 59.37/8.03  
% 59.37/8.03  ------ Combination Options
% 59.37/8.03  
% 59.37/8.03  --comb_res_mult                         3
% 59.37/8.03  --comb_sup_mult                         2
% 59.37/8.03  --comb_inst_mult                        10
% 59.37/8.03  
% 59.37/8.03  ------ Debug Options
% 59.37/8.03  
% 59.37/8.03  --dbg_backtrace                         false
% 59.37/8.03  --dbg_dump_prop_clauses                 false
% 59.37/8.03  --dbg_dump_prop_clauses_file            -
% 59.37/8.03  --dbg_out_stat                          false
% 59.37/8.03  
% 59.37/8.03  
% 59.37/8.03  
% 59.37/8.03  
% 59.37/8.03  ------ Proving...
% 59.37/8.03  
% 59.37/8.03  
% 59.37/8.03  % SZS status Theorem for theBenchmark.p
% 59.37/8.03  
% 59.37/8.03  % SZS output start CNFRefutation for theBenchmark.p
% 59.37/8.03  
% 59.37/8.03  fof(f4,axiom,(
% 59.37/8.03    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 59.37/8.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.37/8.03  
% 59.37/8.03  fof(f20,plain,(
% 59.37/8.03    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 59.37/8.03    inference(cnf_transformation,[],[f4])).
% 59.37/8.03  
% 59.37/8.03  fof(f10,conjecture,(
% 59.37/8.03    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X1,X2)) => r1_xboole_0(X1,k4_xboole_0(X0,X2)))),
% 59.37/8.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.37/8.03  
% 59.37/8.03  fof(f11,negated_conjecture,(
% 59.37/8.03    ~! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X1,X2)) => r1_xboole_0(X1,k4_xboole_0(X0,X2)))),
% 59.37/8.03    inference(negated_conjecture,[],[f10])).
% 59.37/8.03  
% 59.37/8.03  fof(f12,plain,(
% 59.37/8.03    ? [X0,X1,X2] : (~r1_xboole_0(X1,k4_xboole_0(X0,X2)) & r1_xboole_0(X0,k4_xboole_0(X1,X2)))),
% 59.37/8.03    inference(ennf_transformation,[],[f11])).
% 59.37/8.03  
% 59.37/8.03  fof(f14,plain,(
% 59.37/8.03    ? [X0,X1,X2] : (~r1_xboole_0(X1,k4_xboole_0(X0,X2)) & r1_xboole_0(X0,k4_xboole_0(X1,X2))) => (~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),
% 59.37/8.03    introduced(choice_axiom,[])).
% 59.37/8.03  
% 59.37/8.03  fof(f15,plain,(
% 59.37/8.03    ~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 59.37/8.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f14])).
% 59.37/8.03  
% 59.37/8.03  fof(f26,plain,(
% 59.37/8.03    r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 59.37/8.03    inference(cnf_transformation,[],[f15])).
% 59.37/8.03  
% 59.37/8.03  fof(f2,axiom,(
% 59.37/8.03    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 59.37/8.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.37/8.03  
% 59.37/8.03  fof(f13,plain,(
% 59.37/8.03    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 59.37/8.03    inference(nnf_transformation,[],[f2])).
% 59.37/8.03  
% 59.37/8.03  fof(f17,plain,(
% 59.37/8.03    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 59.37/8.03    inference(cnf_transformation,[],[f13])).
% 59.37/8.03  
% 59.37/8.03  fof(f8,axiom,(
% 59.37/8.03    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 59.37/8.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.37/8.03  
% 59.37/8.03  fof(f24,plain,(
% 59.37/8.03    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 59.37/8.03    inference(cnf_transformation,[],[f8])).
% 59.37/8.03  
% 59.37/8.03  fof(f30,plain,(
% 59.37/8.03    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 59.37/8.03    inference(definition_unfolding,[],[f17,f24])).
% 59.37/8.03  
% 59.37/8.03  fof(f7,axiom,(
% 59.37/8.03    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 59.37/8.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.37/8.03  
% 59.37/8.03  fof(f23,plain,(
% 59.37/8.03    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 59.37/8.03    inference(cnf_transformation,[],[f7])).
% 59.37/8.03  
% 59.37/8.03  fof(f32,plain,(
% 59.37/8.03    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 59.37/8.03    inference(definition_unfolding,[],[f23,f24])).
% 59.37/8.03  
% 59.37/8.03  fof(f5,axiom,(
% 59.37/8.03    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 59.37/8.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.37/8.03  
% 59.37/8.03  fof(f21,plain,(
% 59.37/8.03    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 59.37/8.03    inference(cnf_transformation,[],[f5])).
% 59.37/8.03  
% 59.37/8.03  fof(f6,axiom,(
% 59.37/8.03    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 59.37/8.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.37/8.03  
% 59.37/8.03  fof(f22,plain,(
% 59.37/8.03    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 59.37/8.03    inference(cnf_transformation,[],[f6])).
% 59.37/8.03  
% 59.37/8.03  fof(f1,axiom,(
% 59.37/8.03    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 59.37/8.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.37/8.03  
% 59.37/8.03  fof(f16,plain,(
% 59.37/8.03    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 59.37/8.03    inference(cnf_transformation,[],[f1])).
% 59.37/8.03  
% 59.37/8.03  fof(f28,plain,(
% 59.37/8.03    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 59.37/8.03    inference(definition_unfolding,[],[f16,f24,f24])).
% 59.37/8.03  
% 59.37/8.03  fof(f3,axiom,(
% 59.37/8.03    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 59.37/8.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.37/8.03  
% 59.37/8.03  fof(f19,plain,(
% 59.37/8.03    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 59.37/8.03    inference(cnf_transformation,[],[f3])).
% 59.37/8.03  
% 59.37/8.03  fof(f31,plain,(
% 59.37/8.03    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 59.37/8.03    inference(definition_unfolding,[],[f19,f24])).
% 59.37/8.03  
% 59.37/8.03  fof(f9,axiom,(
% 59.37/8.03    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 59.37/8.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.37/8.03  
% 59.37/8.03  fof(f25,plain,(
% 59.37/8.03    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 59.37/8.03    inference(cnf_transformation,[],[f9])).
% 59.37/8.03  
% 59.37/8.03  fof(f18,plain,(
% 59.37/8.03    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 59.37/8.03    inference(cnf_transformation,[],[f13])).
% 59.37/8.03  
% 59.37/8.03  fof(f29,plain,(
% 59.37/8.03    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 59.37/8.03    inference(definition_unfolding,[],[f18,f24])).
% 59.37/8.03  
% 59.37/8.03  fof(f27,plain,(
% 59.37/8.03    ~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))),
% 59.37/8.03    inference(cnf_transformation,[],[f15])).
% 59.37/8.03  
% 59.37/8.03  cnf(c_4,plain,
% 59.37/8.03      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 59.37/8.03      inference(cnf_transformation,[],[f20]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_10,negated_conjecture,
% 59.37/8.03      ( r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
% 59.37/8.03      inference(cnf_transformation,[],[f26]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_208,plain,
% 59.37/8.03      ( r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = iProver_top ),
% 59.37/8.03      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_2,plain,
% 59.37/8.03      ( ~ r1_xboole_0(X0,X1)
% 59.37/8.03      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 59.37/8.03      inference(cnf_transformation,[],[f30]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_210,plain,
% 59.37/8.03      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
% 59.37/8.03      | r1_xboole_0(X0,X1) != iProver_top ),
% 59.37/8.03      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_961,plain,
% 59.37/8.03      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))) = k1_xboole_0 ),
% 59.37/8.03      inference(superposition,[status(thm)],[c_208,c_210]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_7,plain,
% 59.37/8.03      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 59.37/8.03      inference(cnf_transformation,[],[f32]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_408,plain,
% 59.37/8.03      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
% 59.37/8.03      inference(superposition,[status(thm)],[c_7,c_4]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_20186,plain,
% 59.37/8.03      ( k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),sK0) = k2_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k1_xboole_0) ),
% 59.37/8.03      inference(superposition,[status(thm)],[c_961,c_408]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_5,plain,
% 59.37/8.03      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 59.37/8.03      inference(cnf_transformation,[],[f21]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_20638,plain,
% 59.37/8.03      ( k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)),sK0) = k2_xboole_0(sK0,k1_xboole_0) ),
% 59.37/8.03      inference(demodulation,[status(thm)],[c_20186,c_5,c_7]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_6,plain,
% 59.37/8.03      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 59.37/8.03      inference(cnf_transformation,[],[f22]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_367,plain,
% 59.37/8.03      ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = k2_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 59.37/8.03      inference(superposition,[status(thm)],[c_6,c_4]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_21963,plain,
% 59.37/8.03      ( k2_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)))) = k2_xboole_0(sK0,k4_xboole_0(X0,k2_xboole_0(sK0,k1_xboole_0))) ),
% 59.37/8.03      inference(superposition,[status(thm)],[c_20638,c_367]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_370,plain,
% 59.37/8.03      ( k4_xboole_0(X0,k2_xboole_0(X1,k1_xboole_0)) = k4_xboole_0(X0,X1) ),
% 59.37/8.03      inference(superposition,[status(thm)],[c_6,c_5]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_22014,plain,
% 59.37/8.03      ( k2_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)))) = k2_xboole_0(sK0,X0) ),
% 59.37/8.03      inference(demodulation,[status(thm)],[c_21963,c_4,c_370]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_0,plain,
% 59.37/8.03      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 59.37/8.03      inference(cnf_transformation,[],[f28]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_3,plain,
% 59.37/8.03      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 59.37/8.03      inference(cnf_transformation,[],[f31]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_218,plain,
% 59.37/8.03      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 59.37/8.03      inference(light_normalisation,[status(thm)],[c_3,c_5]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_524,plain,
% 59.37/8.03      ( k2_xboole_0(X0,X0) = k2_xboole_0(X0,k1_xboole_0) ),
% 59.37/8.03      inference(superposition,[status(thm)],[c_218,c_4]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_369,plain,
% 59.37/8.03      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
% 59.37/8.03      inference(superposition,[status(thm)],[c_6,c_0]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_373,plain,
% 59.37/8.03      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2)))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
% 59.37/8.03      inference(light_normalisation,[status(thm)],[c_369,c_6]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_6110,plain,
% 59.37/8.03      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,k1_xboole_0)))) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,X1))) ),
% 59.37/8.03      inference(superposition,[status(thm)],[c_524,c_373]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_6431,plain,
% 59.37/8.03      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))) = k4_xboole_0(X1,k2_xboole_0(X0,k4_xboole_0(X1,X0))) ),
% 59.37/8.03      inference(light_normalisation,[status(thm)],[c_6110,c_370]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_525,plain,
% 59.37/8.03      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
% 59.37/8.03      inference(superposition,[status(thm)],[c_218,c_6]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_527,plain,
% 59.37/8.03      ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 59.37/8.03      inference(demodulation,[status(thm)],[c_525,c_4]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_6432,plain,
% 59.37/8.03      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))) = k1_xboole_0 ),
% 59.37/8.03      inference(demodulation,[status(thm)],[c_6431,c_4,c_527]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_6716,plain,
% 59.37/8.03      ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k1_xboole_0) ),
% 59.37/8.03      inference(superposition,[status(thm)],[c_6432,c_7]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_6751,plain,
% 59.37/8.03      ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
% 59.37/8.03      inference(light_normalisation,[status(thm)],[c_6716,c_5]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_6763,plain,
% 59.37/8.03      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
% 59.37/8.03      inference(superposition,[status(thm)],[c_0,c_6751]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_31350,plain,
% 59.37/8.03      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(X0,X1) ),
% 59.37/8.03      inference(superposition,[status(thm)],[c_6763,c_6]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_46077,plain,
% 59.37/8.03      ( k4_xboole_0(k4_xboole_0(sK1,sK2),k2_xboole_0(sK0,sK0)) = k4_xboole_0(k4_xboole_0(sK1,sK2),sK0) ),
% 59.37/8.03      inference(superposition,[status(thm)],[c_22014,c_31350]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_398,plain,
% 59.37/8.03      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
% 59.37/8.03      inference(superposition,[status(thm)],[c_0,c_7]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_20215,plain,
% 59.37/8.03      ( k4_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0) = k4_xboole_0(k4_xboole_0(sK1,sK2),sK0) ),
% 59.37/8.03      inference(superposition,[status(thm)],[c_961,c_398]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_20572,plain,
% 59.37/8.03      ( k4_xboole_0(sK1,k2_xboole_0(sK2,sK0)) = k4_xboole_0(sK1,sK2) ),
% 59.37/8.03      inference(demodulation,[status(thm)],[c_20215,c_6,c_370]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_46642,plain,
% 59.37/8.03      ( k4_xboole_0(k4_xboole_0(sK1,sK2),k2_xboole_0(sK0,sK0)) = k4_xboole_0(sK1,sK2) ),
% 59.37/8.03      inference(demodulation,[status(thm)],[c_46077,c_6,c_20572]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_6813,plain,
% 59.37/8.03      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X0),X2)) = k4_xboole_0(X0,X2) ),
% 59.37/8.03      inference(superposition,[status(thm)],[c_6751,c_6]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_523,plain,
% 59.37/8.03      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(k1_xboole_0,X1) ),
% 59.37/8.03      inference(superposition,[status(thm)],[c_218,c_6]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_8,plain,
% 59.37/8.03      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 59.37/8.03      inference(cnf_transformation,[],[f25]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_532,plain,
% 59.37/8.03      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
% 59.37/8.03      inference(demodulation,[status(thm)],[c_523,c_8]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_817,plain,
% 59.37/8.03      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
% 59.37/8.03      inference(superposition,[status(thm)],[c_532,c_4]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_368,plain,
% 59.37/8.03      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X2))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
% 59.37/8.03      inference(superposition,[status(thm)],[c_6,c_0]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_4945,plain,
% 59.37/8.03      ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),k1_xboole_0))) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2)))) ),
% 59.37/8.03      inference(superposition,[status(thm)],[c_817,c_368]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_5208,plain,
% 59.37/8.03      ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X0,k2_xboole_0(X1,X2)))) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2)))) ),
% 59.37/8.03      inference(demodulation,[status(thm)],[c_4945,c_6,c_370]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_5209,plain,
% 59.37/8.03      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X0,X2)))) = k1_xboole_0 ),
% 59.37/8.03      inference(demodulation,[status(thm)],[c_5208,c_4,c_527]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_7949,plain,
% 59.37/8.03      ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X1) = k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k1_xboole_0) ),
% 59.37/8.03      inference(superposition,[status(thm)],[c_5209,c_398]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_364,plain,
% 59.37/8.03      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X3)) = k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X3) ),
% 59.37/8.03      inference(superposition,[status(thm)],[c_6,c_6]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_380,plain,
% 59.37/8.03      ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3))) ),
% 59.37/8.03      inference(demodulation,[status(thm)],[c_364,c_6]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_7960,plain,
% 59.37/8.03      ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X1) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,k1_xboole_0))) ),
% 59.37/8.03      inference(demodulation,[status(thm)],[c_7949,c_6,c_380]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_1095,plain,
% 59.37/8.03      ( k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),X0) = k1_xboole_0 ),
% 59.37/8.03      inference(superposition,[status(thm)],[c_370,c_218]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_297,plain,
% 59.37/8.03      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 59.37/8.03      inference(superposition,[status(thm)],[c_0,c_4]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_24337,plain,
% 59.37/8.03      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),X0),k2_xboole_0(X0,k1_xboole_0)) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,k1_xboole_0)))) ),
% 59.37/8.03      inference(superposition,[status(thm)],[c_1095,c_297]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_24432,plain,
% 59.37/8.03      ( k2_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,k1_xboole_0)))) = k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,k1_xboole_0)) ),
% 59.37/8.03      inference(light_normalisation,[status(thm)],[c_24337,c_1095]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_818,plain,
% 59.37/8.03      ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(k4_xboole_0(X0,X1),X2))) = k1_xboole_0 ),
% 59.37/8.03      inference(superposition,[status(thm)],[c_532,c_6]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_2603,plain,
% 59.37/8.03      ( k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,X1))) = k1_xboole_0 ),
% 59.37/8.03      inference(superposition,[status(thm)],[c_5,c_818]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_6699,plain,
% 59.37/8.03      ( k4_xboole_0(k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,X1)),k4_xboole_0(k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,X1)),k1_xboole_0)) = k1_xboole_0 ),
% 59.37/8.03      inference(superposition,[status(thm)],[c_2603,c_6432]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_361,plain,
% 59.37/8.03      ( k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,X1)) = k4_xboole_0(X0,X1) ),
% 59.37/8.03      inference(superposition,[status(thm)],[c_5,c_6]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_6964,plain,
% 59.37/8.03      ( k4_xboole_0(k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,X1)),k2_xboole_0(X0,X1)) = k1_xboole_0 ),
% 59.37/8.03      inference(demodulation,[status(thm)],[c_6699,c_5,c_361]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_9403,plain,
% 59.37/8.03      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,X1)))) = k4_xboole_0(k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,X1)),k1_xboole_0) ),
% 59.37/8.03      inference(superposition,[status(thm)],[c_6964,c_0]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_6766,plain,
% 59.37/8.03      ( k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = X0 ),
% 59.37/8.03      inference(superposition,[status(thm)],[c_6,c_6751]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_9429,plain,
% 59.37/8.03      ( k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
% 59.37/8.03      inference(demodulation,[status(thm)],[c_9403,c_5,c_6766]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_933,plain,
% 59.37/8.03      ( k4_xboole_0(k2_xboole_0(k1_xboole_0,X0),X0) = k1_xboole_0 ),
% 59.37/8.03      inference(superposition,[status(thm)],[c_361,c_218]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_930,plain,
% 59.37/8.03      ( k4_xboole_0(k2_xboole_0(k1_xboole_0,X0),k4_xboole_0(k2_xboole_0(k1_xboole_0,X0),X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 59.37/8.03      inference(superposition,[status(thm)],[c_361,c_0]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_19439,plain,
% 59.37/8.03      ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = k4_xboole_0(k2_xboole_0(k1_xboole_0,X0),k1_xboole_0) ),
% 59.37/8.03      inference(superposition,[status(thm)],[c_933,c_930]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_19451,plain,
% 59.37/8.03      ( k4_xboole_0(k2_xboole_0(k1_xboole_0,X0),k1_xboole_0) = X0 ),
% 59.37/8.03      inference(light_normalisation,[status(thm)],[c_19439,c_5,c_218]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_19831,plain,
% 59.37/8.03      ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
% 59.37/8.03      inference(superposition,[status(thm)],[c_19451,c_5]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_24434,plain,
% 59.37/8.03      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 59.37/8.03      inference(demodulation,
% 59.37/8.03                [status(thm)],
% 59.37/8.03                [c_24432,c_5,c_532,c_9429,c_19831]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_146538,plain,
% 59.37/8.03      ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X1) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 59.37/8.03      inference(demodulation,[status(thm)],[c_7960,c_6,c_24434]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_146620,plain,
% 59.37/8.03      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X0)) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X2,X0),X1)) ),
% 59.37/8.03      inference(superposition,[status(thm)],[c_6813,c_146538]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_147400,plain,
% 59.37/8.03      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X0)) = k4_xboole_0(X0,X1) ),
% 59.37/8.03      inference(demodulation,[status(thm)],[c_146620,c_6,c_6813]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_147899,plain,
% 59.37/8.03      ( k4_xboole_0(k4_xboole_0(k2_xboole_0(sK0,sK0),X0),k4_xboole_0(sK1,sK2)) = k4_xboole_0(k2_xboole_0(sK0,sK0),X0) ),
% 59.37/8.03      inference(superposition,[status(thm)],[c_46642,c_147400]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_4939,plain,
% 59.37/8.03      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X1))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1))) ),
% 59.37/8.03      inference(superposition,[status(thm)],[c_524,c_368]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_5228,plain,
% 59.37/8.03      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X1))) = k1_xboole_0 ),
% 59.37/8.03      inference(demodulation,[status(thm)],[c_4939,c_6,c_8]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_9411,plain,
% 59.37/8.03      ( k4_xboole_0(k4_xboole_0(k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,X0)),X0),k1_xboole_0) = k1_xboole_0 ),
% 59.37/8.03      inference(superposition,[status(thm)],[c_6964,c_5228]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_9681,plain,
% 59.37/8.03      ( k4_xboole_0(k2_xboole_0(X0,X0),k2_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 59.37/8.03      inference(demodulation,[status(thm)],[c_9411,c_6,c_9429]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_407,plain,
% 59.37/8.03      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 59.37/8.03      inference(superposition,[status(thm)],[c_7,c_6]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_418,plain,
% 59.37/8.03      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 59.37/8.03      inference(light_normalisation,[status(thm)],[c_407,c_6]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_11319,plain,
% 59.37/8.03      ( k4_xboole_0(k2_xboole_0(X0,X0),k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X0),k1_xboole_0),X1)) = k4_xboole_0(k2_xboole_0(X0,X0),k2_xboole_0(k2_xboole_0(X0,k1_xboole_0),X1)) ),
% 59.37/8.03      inference(superposition,[status(thm)],[c_9681,c_418]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_9892,plain,
% 59.37/8.03      ( k4_xboole_0(k2_xboole_0(X0,X0),k2_xboole_0(k2_xboole_0(X0,k1_xboole_0),X1)) = k4_xboole_0(k1_xboole_0,X1) ),
% 59.37/8.03      inference(superposition,[status(thm)],[c_9681,c_6]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_9945,plain,
% 59.37/8.03      ( k4_xboole_0(k2_xboole_0(X0,X0),k2_xboole_0(k2_xboole_0(X0,k1_xboole_0),X1)) = k1_xboole_0 ),
% 59.37/8.03      inference(demodulation,[status(thm)],[c_9892,c_8,c_380]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_11455,plain,
% 59.37/8.03      ( k4_xboole_0(k2_xboole_0(X0,X0),k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X0),k1_xboole_0),X1)) = k1_xboole_0 ),
% 59.37/8.03      inference(light_normalisation,[status(thm)],[c_11319,c_9945]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_11456,plain,
% 59.37/8.03      ( k4_xboole_0(k2_xboole_0(X0,X0),k2_xboole_0(X0,k2_xboole_0(X0,X1))) = k1_xboole_0 ),
% 59.37/8.03      inference(demodulation,[status(thm)],[c_11455,c_5,c_380]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_11660,plain,
% 59.37/8.03      ( k4_xboole_0(k2_xboole_0(X0,X0),k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(X0,X1)),X2)) = k4_xboole_0(k1_xboole_0,X2) ),
% 59.37/8.03      inference(superposition,[status(thm)],[c_11456,c_6]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_11695,plain,
% 59.37/8.03      ( k4_xboole_0(k2_xboole_0(X0,X0),k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(X0,X1)),X2)) = k1_xboole_0 ),
% 59.37/8.03      inference(demodulation,[status(thm)],[c_11660,c_8,c_380]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_36482,plain,
% 59.37/8.03      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X0),k4_xboole_0(k2_xboole_0(X0,X0),k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(X0,X1)),X2))),k2_xboole_0(X0,X0)) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X0),k1_xboole_0),k1_xboole_0) ),
% 59.37/8.03      inference(superposition,[status(thm)],[c_11695,c_408]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_36582,plain,
% 59.37/8.03      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X0),k1_xboole_0),k2_xboole_0(X0,X0)) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X0),k1_xboole_0),k1_xboole_0) ),
% 59.37/8.03      inference(light_normalisation,[status(thm)],[c_36482,c_11695]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_36584,plain,
% 59.37/8.03      ( k2_xboole_0(k2_xboole_0(X0,X0),k2_xboole_0(X0,X0)) = k2_xboole_0(X0,X0) ),
% 59.37/8.03      inference(demodulation,[status(thm)],[c_36582,c_5,c_24434]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_7213,plain,
% 59.37/8.03      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,k2_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
% 59.37/8.03      inference(superposition,[status(thm)],[c_4,c_6766]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_36667,plain,
% 59.37/8.03      ( k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X0),k2_xboole_0(X0,X0)),k4_xboole_0(X1,k2_xboole_0(X0,X0))) = k4_xboole_0(k2_xboole_0(X0,X0),k2_xboole_0(X0,X0)) ),
% 59.37/8.03      inference(superposition,[status(thm)],[c_36584,c_7213]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_1087,plain,
% 59.37/8.03      ( k4_xboole_0(X0,k2_xboole_0(X1,X1)) = k4_xboole_0(X0,X1) ),
% 59.37/8.03      inference(superposition,[status(thm)],[c_524,c_370]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_36791,plain,
% 59.37/8.03      ( k4_xboole_0(k2_xboole_0(X0,X0),k2_xboole_0(X0,k4_xboole_0(X1,X0))) = k4_xboole_0(k2_xboole_0(X0,X0),X0) ),
% 59.37/8.03      inference(demodulation,[status(thm)],[c_36667,c_6,c_1087]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_36792,plain,
% 59.37/8.03      ( k4_xboole_0(k2_xboole_0(X0,X0),k2_xboole_0(X0,X1)) = k4_xboole_0(k2_xboole_0(X0,X0),X0) ),
% 59.37/8.03      inference(light_normalisation,[status(thm)],[c_36791,c_4]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_359,plain,
% 59.37/8.03      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
% 59.37/8.03      inference(superposition,[status(thm)],[c_0,c_6]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_53351,plain,
% 59.37/8.03      ( k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X0))),X2) = k4_xboole_0(k2_xboole_0(X0,X0),k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X0),X0),X2)) ),
% 59.37/8.03      inference(superposition,[status(thm)],[c_36792,c_359]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_53368,plain,
% 59.37/8.03      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X0)),X2)) = k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X0),k4_xboole_0(k2_xboole_0(X0,X0),X0)),X2) ),
% 59.37/8.03      inference(superposition,[status(thm)],[c_36792,c_359]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_7184,plain,
% 59.37/8.03      ( k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X3,X0)))) = X0 ),
% 59.37/8.03      inference(superposition,[status(thm)],[c_6,c_6766]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_53403,plain,
% 59.37/8.03      ( k4_xboole_0(X0,k4_xboole_0(k2_xboole_0(X1,X1),X1)) = X0 ),
% 59.37/8.03      inference(superposition,[status(thm)],[c_36792,c_7184]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_53464,plain,
% 59.37/8.03      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X0)),X2)) = k4_xboole_0(k2_xboole_0(X0,X0),X2) ),
% 59.37/8.03      inference(demodulation,[status(thm)],[c_53368,c_53403]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_53466,plain,
% 59.37/8.03      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X0),X2)) = k4_xboole_0(k2_xboole_0(X0,X0),X2) ),
% 59.37/8.03      inference(demodulation,[status(thm)],[c_53464,c_1087]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_53502,plain,
% 59.37/8.03      ( k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X0))),X2) = k4_xboole_0(k2_xboole_0(X0,X0),X2) ),
% 59.37/8.03      inference(demodulation,[status(thm)],[c_53351,c_53466]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_784,plain,
% 59.37/8.03      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 59.37/8.03      inference(superposition,[status(thm)],[c_4,c_527]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_1118,plain,
% 59.37/8.03      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k2_xboole_0(k4_xboole_0(X1,X0),X1)) = k1_xboole_0 ),
% 59.37/8.03      inference(superposition,[status(thm)],[c_0,c_784]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_14596,plain,
% 59.37/8.03      ( k4_xboole_0(k4_xboole_0(X0,k1_xboole_0),k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X0),k2_xboole_0(X0,X1))) = k1_xboole_0 ),
% 59.37/8.03      inference(superposition,[status(thm)],[c_532,c_1118]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_15026,plain,
% 59.37/8.03      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X0),k2_xboole_0(X0,X1))) = k1_xboole_0 ),
% 59.37/8.03      inference(light_normalisation,[status(thm)],[c_14596,c_5]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_41963,plain,
% 59.37/8.03      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(k2_xboole_0(X0,X1),X0)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(k2_xboole_0(X0,X1),X0)),k1_xboole_0) ),
% 59.37/8.03      inference(superposition,[status(thm)],[c_15026,c_368]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_41989,plain,
% 59.37/8.03      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),X0)) = X0 ),
% 59.37/8.03      inference(demodulation,[status(thm)],[c_41963,c_6,c_6751,c_24434]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_53504,plain,
% 59.37/8.03      ( k4_xboole_0(k2_xboole_0(X0,X0),X1) = k4_xboole_0(X0,X1) ),
% 59.37/8.03      inference(demodulation,[status(thm)],[c_53502,c_6,c_1087,c_41989]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_148404,plain,
% 59.37/8.03      ( k4_xboole_0(sK0,k2_xboole_0(X0,k4_xboole_0(sK1,sK2))) = k4_xboole_0(sK0,X0) ),
% 59.37/8.03      inference(demodulation,[status(thm)],[c_147899,c_6,c_53504]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_149308,plain,
% 59.37/8.03      ( k4_xboole_0(sK0,k2_xboole_0(sK2,sK1)) = k4_xboole_0(sK0,sK2) ),
% 59.37/8.03      inference(superposition,[status(thm)],[c_4,c_148404]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_1,plain,
% 59.37/8.03      ( r1_xboole_0(X0,X1)
% 59.37/8.03      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
% 59.37/8.03      inference(cnf_transformation,[],[f29]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_211,plain,
% 59.37/8.03      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0
% 59.37/8.03      | r1_xboole_0(X0,X1) = iProver_top ),
% 59.37/8.03      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_1433,plain,
% 59.37/8.03      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X2))) != k1_xboole_0
% 59.37/8.03      | r1_xboole_0(k4_xboole_0(X0,X1),X2) = iProver_top ),
% 59.37/8.03      inference(superposition,[status(thm)],[c_6,c_211]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_1493,plain,
% 59.37/8.03      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2)))) != k1_xboole_0
% 59.37/8.03      | r1_xboole_0(k4_xboole_0(X0,X1),X2) = iProver_top ),
% 59.37/8.03      inference(demodulation,[status(thm)],[c_1433,c_6]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_150003,plain,
% 59.37/8.03      ( k4_xboole_0(sK0,k2_xboole_0(sK2,k4_xboole_0(sK0,sK2))) != k1_xboole_0
% 59.37/8.03      | r1_xboole_0(k4_xboole_0(sK0,sK2),sK1) = iProver_top ),
% 59.37/8.03      inference(superposition,[status(thm)],[c_149308,c_1493]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_150070,plain,
% 59.37/8.03      ( k1_xboole_0 != k1_xboole_0
% 59.37/8.03      | r1_xboole_0(k4_xboole_0(sK0,sK2),sK1) = iProver_top ),
% 59.37/8.03      inference(demodulation,[status(thm)],[c_150003,c_4,c_527]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_150071,plain,
% 59.37/8.03      ( r1_xboole_0(k4_xboole_0(sK0,sK2),sK1) = iProver_top ),
% 59.37/8.03      inference(equality_resolution_simp,[status(thm)],[c_150070]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_497,plain,
% 59.37/8.03      ( ~ r1_xboole_0(k4_xboole_0(sK0,sK2),sK1)
% 59.37/8.03      | k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(k4_xboole_0(sK0,sK2),sK1)) = k1_xboole_0 ),
% 59.37/8.03      inference(instantiation,[status(thm)],[c_2]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_498,plain,
% 59.37/8.03      ( k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(k4_xboole_0(sK0,sK2),sK1)) = k1_xboole_0
% 59.37/8.03      | r1_xboole_0(k4_xboole_0(sK0,sK2),sK1) != iProver_top ),
% 59.37/8.03      inference(predicate_to_equality,[status(thm)],[c_497]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_72,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_343,plain,
% 59.37/8.03      ( k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(k4_xboole_0(sK0,sK2),sK1)) != X0
% 59.37/8.03      | k1_xboole_0 != X0
% 59.37/8.03      | k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(k4_xboole_0(sK0,sK2),sK1)) ),
% 59.37/8.03      inference(instantiation,[status(thm)],[c_72]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_344,plain,
% 59.37/8.03      ( k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(k4_xboole_0(sK0,sK2),sK1)) != k1_xboole_0
% 59.37/8.03      | k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(k4_xboole_0(sK0,sK2),sK1))
% 59.37/8.03      | k1_xboole_0 != k1_xboole_0 ),
% 59.37/8.03      inference(instantiation,[status(thm)],[c_343]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_320,plain,
% 59.37/8.03      ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK2))) = k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(k4_xboole_0(sK0,sK2),sK1)) ),
% 59.37/8.03      inference(instantiation,[status(thm)],[c_0]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_278,plain,
% 59.37/8.03      ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK2))) != X0
% 59.37/8.03      | k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK2))) = k1_xboole_0
% 59.37/8.03      | k1_xboole_0 != X0 ),
% 59.37/8.03      inference(instantiation,[status(thm)],[c_72]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_319,plain,
% 59.37/8.03      ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK2))) != k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(k4_xboole_0(sK0,sK2),sK1))
% 59.37/8.03      | k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK2))) = k1_xboole_0
% 59.37/8.03      | k1_xboole_0 != k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(k4_xboole_0(sK0,sK2),sK1)) ),
% 59.37/8.03      inference(instantiation,[status(thm)],[c_278]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_258,plain,
% 59.37/8.03      ( r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
% 59.37/8.03      | k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK2))) != k1_xboole_0 ),
% 59.37/8.03      inference(instantiation,[status(thm)],[c_1]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_71,plain,( X0 = X0 ),theory(equality) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_80,plain,
% 59.37/8.03      ( k1_xboole_0 = k1_xboole_0 ),
% 59.37/8.03      inference(instantiation,[status(thm)],[c_71]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(c_9,negated_conjecture,
% 59.37/8.03      ( ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
% 59.37/8.03      inference(cnf_transformation,[],[f27]) ).
% 59.37/8.03  
% 59.37/8.03  cnf(contradiction,plain,
% 59.37/8.03      ( $false ),
% 59.37/8.03      inference(minisat,
% 59.37/8.03                [status(thm)],
% 59.37/8.03                [c_150071,c_498,c_344,c_320,c_319,c_258,c_80,c_9]) ).
% 59.37/8.03  
% 59.37/8.03  
% 59.37/8.03  % SZS output end CNFRefutation for theBenchmark.p
% 59.37/8.03  
% 59.37/8.03  ------                               Statistics
% 59.37/8.03  
% 59.37/8.03  ------ Selected
% 59.37/8.03  
% 59.37/8.03  total_time:                             7.224
% 59.37/8.03  
%------------------------------------------------------------------------------
