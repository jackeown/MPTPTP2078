%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:23:53 EST 2020

% Result     : Theorem 15.97s
% Output     : CNFRefutation 15.97s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 425 expanded)
%              Number of clauses        :   62 ( 155 expanded)
%              Number of leaves         :   17 ( 107 expanded)
%              Depth                    :   20
%              Number of atoms          :  160 ( 648 expanded)
%              Number of equality atoms :  118 ( 478 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    8 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X3,X1)
          & r1_xboole_0(X2,X0)
          & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
       => X1 = X2 ) ),
    inference(negated_conjecture,[],[f14])).

fof(f20,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f21,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(flattening,[],[f20])).

fof(f23,plain,
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

fof(f24,plain,
    ( sK1 != sK2
    & r1_xboole_0(sK3,sK1)
    & r1_xboole_0(sK2,sK0)
    & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f21,f23])).

fof(f41,plain,(
    r1_xboole_0(sK3,sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f25,f37])).

fof(f11,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f47,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f36,f37])).

fof(f8,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f39,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f24])).

fof(f6,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f6])).

fof(f46,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f31,f37])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f13])).

fof(f48,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) ),
    inference(definition_unfolding,[],[f38,f37])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f4,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f10,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f7])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k2_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k2_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f45,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2))) ),
    inference(definition_unfolding,[],[f30,f37,f37])).

fof(f40,plain,(
    r1_xboole_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f42,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f24])).

cnf(c_14,negated_conjecture,
    ( r1_xboole_0(sK3,sK1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_364,plain,
    ( r1_xboole_0(sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_365,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1006,plain,
    ( r1_xboole_0(sK1,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_364,c_365])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_366,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1652,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1006,c_366])).

cnf(c_11,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_34302,plain,
    ( k4_xboole_0(sK1,sK3) = k4_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1652,c_11])).

cnf(c_8,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_34426,plain,
    ( k4_xboole_0(sK1,sK3) = sK1 ),
    inference(demodulation,[status(thm)],[c_34302,c_8])).

cnf(c_16,negated_conjecture,
    ( k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_6,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_368,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_6,c_8])).

cnf(c_12,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_9,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_369,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X2))))) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_12,c_9])).

cnf(c_3743,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,k1_xboole_0)))) = k4_xboole_0(X0,k2_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_368,c_369])).

cnf(c_4,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_553,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_9,c_368])).

cnf(c_3856,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3743,c_4,c_553])).

cnf(c_4088,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,k1_xboole_0)))) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X0))) ),
    inference(superposition,[status(thm)],[c_3856,c_369])).

cnf(c_3781,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X1,k4_xboole_0(X0,X2)))) = k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2)))) ),
    inference(superposition,[status(thm)],[c_369,c_369])).

cnf(c_10,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_7,plain,
    ( r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_123,plain,
    ( k2_xboole_0(X0,X1) = X1
    | k4_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_7,c_3])).

cnf(c_538,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_10,c_123])).

cnf(c_3816,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2)))) = k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X2))) ),
    inference(demodulation,[status(thm)],[c_3781,c_538])).

cnf(c_4124,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X0))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4088,c_8,c_3816,c_3856])).

cnf(c_5318,plain,
    ( k4_xboole_0(sK1,k2_xboole_0(X0,k2_xboole_0(sK2,sK3))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_16,c_4124])).

cnf(c_550,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X2) = X2
    | k4_xboole_0(X0,k2_xboole_0(X1,X2)) != k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_9,c_123])).

cnf(c_6258,plain,
    ( k2_xboole_0(k4_xboole_0(sK1,X0),k2_xboole_0(sK2,sK3)) = k2_xboole_0(sK2,sK3) ),
    inference(superposition,[status(thm)],[c_5318,c_550])).

cnf(c_7155,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,X0),k2_xboole_0(sK2,sK3)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6258,c_10])).

cnf(c_5,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2))) = k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1068,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2))) = k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X0,X2)))) ),
    inference(superposition,[status(thm)],[c_538,c_5])).

cnf(c_1077,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X0,X2)))) = k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(light_normalisation,[status(thm)],[c_1068,c_5])).

cnf(c_56075,plain,
    ( k2_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,X0),k4_xboole_0(k4_xboole_0(sK1,X0),sK3))) = k2_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,X0),k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_7155,c_1077])).

cnf(c_56378,plain,
    ( k2_xboole_0(sK2,k4_xboole_0(sK1,k2_xboole_0(X0,k4_xboole_0(k4_xboole_0(sK1,X0),sK3)))) = k2_xboole_0(sK2,k4_xboole_0(sK1,k2_xboole_0(X0,k1_xboole_0))) ),
    inference(demodulation,[status(thm)],[c_56075,c_9])).

cnf(c_56379,plain,
    ( k2_xboole_0(sK2,k4_xboole_0(sK1,k2_xboole_0(X0,k4_xboole_0(k4_xboole_0(sK1,X0),sK3)))) = k2_xboole_0(sK2,k4_xboole_0(sK1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_56378,c_4])).

cnf(c_56380,plain,
    ( k2_xboole_0(sK2,k4_xboole_0(sK1,k2_xboole_0(X0,k4_xboole_0(sK1,sK3)))) = k2_xboole_0(sK2,k4_xboole_0(sK1,X0)) ),
    inference(demodulation,[status(thm)],[c_56379,c_9,c_3816])).

cnf(c_56381,plain,
    ( k2_xboole_0(sK2,k4_xboole_0(sK1,k2_xboole_0(X0,sK1))) = k2_xboole_0(sK2,k4_xboole_0(sK1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_56380,c_34426])).

cnf(c_56382,plain,
    ( k2_xboole_0(sK2,k4_xboole_0(sK1,X0)) = sK2 ),
    inference(demodulation,[status(thm)],[c_56381,c_4,c_3856])).

cnf(c_56533,plain,
    ( k2_xboole_0(sK2,sK1) = sK2 ),
    inference(superposition,[status(thm)],[c_34426,c_56382])).

cnf(c_15,negated_conjecture,
    ( r1_xboole_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_363,plain,
    ( r1_xboole_0(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1651,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_363,c_366])).

cnf(c_2221,plain,
    ( k4_xboole_0(sK2,sK0) = k4_xboole_0(sK2,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1651,c_11])).

cnf(c_2222,plain,
    ( k4_xboole_0(sK2,sK0) = sK2 ),
    inference(demodulation,[status(thm)],[c_2221,c_8])).

cnf(c_2921,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(sK0,X0)) = k4_xboole_0(sK2,X0) ),
    inference(superposition,[status(thm)],[c_2222,c_9])).

cnf(c_3003,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(sK2,sK3)) = k4_xboole_0(sK2,sK1) ),
    inference(superposition,[status(thm)],[c_16,c_2921])).

cnf(c_3025,plain,
    ( k4_xboole_0(sK2,sK1) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3003,c_10])).

cnf(c_3112,plain,
    ( k2_xboole_0(sK2,sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_3025,c_123])).

cnf(c_56617,plain,
    ( sK2 = sK1 ),
    inference(light_normalisation,[status(thm)],[c_56533,c_3112])).

cnf(c_198,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_378,plain,
    ( sK2 != X0
    | sK1 != X0
    | sK1 = sK2 ),
    inference(instantiation,[status(thm)],[c_198])).

cnf(c_37665,plain,
    ( sK2 != sK1
    | sK1 = sK2
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_378])).

cnf(c_197,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_517,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_197])).

cnf(c_13,negated_conjecture,
    ( sK1 != sK2 ),
    inference(cnf_transformation,[],[f42])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_56617,c_37665,c_517,c_13])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 21:05:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 15.97/2.53  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.97/2.53  
% 15.97/2.53  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.97/2.53  
% 15.97/2.53  ------  iProver source info
% 15.97/2.53  
% 15.97/2.53  git: date: 2020-06-30 10:37:57 +0100
% 15.97/2.53  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.97/2.53  git: non_committed_changes: false
% 15.97/2.53  git: last_make_outside_of_git: false
% 15.97/2.53  
% 15.97/2.53  ------ 
% 15.97/2.53  
% 15.97/2.53  ------ Input Options
% 15.97/2.53  
% 15.97/2.53  --out_options                           all
% 15.97/2.53  --tptp_safe_out                         true
% 15.97/2.53  --problem_path                          ""
% 15.97/2.53  --include_path                          ""
% 15.97/2.53  --clausifier                            res/vclausify_rel
% 15.97/2.53  --clausifier_options                    ""
% 15.97/2.53  --stdin                                 false
% 15.97/2.53  --stats_out                             all
% 15.97/2.53  
% 15.97/2.53  ------ General Options
% 15.97/2.53  
% 15.97/2.53  --fof                                   false
% 15.97/2.53  --time_out_real                         305.
% 15.97/2.53  --time_out_virtual                      -1.
% 15.97/2.53  --symbol_type_check                     false
% 15.97/2.53  --clausify_out                          false
% 15.97/2.53  --sig_cnt_out                           false
% 15.97/2.53  --trig_cnt_out                          false
% 15.97/2.53  --trig_cnt_out_tolerance                1.
% 15.97/2.53  --trig_cnt_out_sk_spl                   false
% 15.97/2.53  --abstr_cl_out                          false
% 15.97/2.53  
% 15.97/2.53  ------ Global Options
% 15.97/2.53  
% 15.97/2.53  --schedule                              default
% 15.97/2.53  --add_important_lit                     false
% 15.97/2.53  --prop_solver_per_cl                    1000
% 15.97/2.53  --min_unsat_core                        false
% 15.97/2.53  --soft_assumptions                      false
% 15.97/2.53  --soft_lemma_size                       3
% 15.97/2.53  --prop_impl_unit_size                   0
% 15.97/2.53  --prop_impl_unit                        []
% 15.97/2.53  --share_sel_clauses                     true
% 15.97/2.53  --reset_solvers                         false
% 15.97/2.53  --bc_imp_inh                            [conj_cone]
% 15.97/2.53  --conj_cone_tolerance                   3.
% 15.97/2.53  --extra_neg_conj                        none
% 15.97/2.53  --large_theory_mode                     true
% 15.97/2.53  --prolific_symb_bound                   200
% 15.97/2.53  --lt_threshold                          2000
% 15.97/2.53  --clause_weak_htbl                      true
% 15.97/2.53  --gc_record_bc_elim                     false
% 15.97/2.53  
% 15.97/2.53  ------ Preprocessing Options
% 15.97/2.53  
% 15.97/2.53  --preprocessing_flag                    true
% 15.97/2.53  --time_out_prep_mult                    0.1
% 15.97/2.53  --splitting_mode                        input
% 15.97/2.53  --splitting_grd                         true
% 15.97/2.53  --splitting_cvd                         false
% 15.97/2.53  --splitting_cvd_svl                     false
% 15.97/2.53  --splitting_nvd                         32
% 15.97/2.53  --sub_typing                            true
% 15.97/2.53  --prep_gs_sim                           true
% 15.97/2.53  --prep_unflatten                        true
% 15.97/2.53  --prep_res_sim                          true
% 15.97/2.53  --prep_upred                            true
% 15.97/2.53  --prep_sem_filter                       exhaustive
% 15.97/2.53  --prep_sem_filter_out                   false
% 15.97/2.53  --pred_elim                             true
% 15.97/2.53  --res_sim_input                         true
% 15.97/2.53  --eq_ax_congr_red                       true
% 15.97/2.53  --pure_diseq_elim                       true
% 15.97/2.53  --brand_transform                       false
% 15.97/2.53  --non_eq_to_eq                          false
% 15.97/2.53  --prep_def_merge                        true
% 15.97/2.53  --prep_def_merge_prop_impl              false
% 15.97/2.53  --prep_def_merge_mbd                    true
% 15.97/2.53  --prep_def_merge_tr_red                 false
% 15.97/2.53  --prep_def_merge_tr_cl                  false
% 15.97/2.53  --smt_preprocessing                     true
% 15.97/2.53  --smt_ac_axioms                         fast
% 15.97/2.53  --preprocessed_out                      false
% 15.97/2.53  --preprocessed_stats                    false
% 15.97/2.53  
% 15.97/2.53  ------ Abstraction refinement Options
% 15.97/2.53  
% 15.97/2.53  --abstr_ref                             []
% 15.97/2.53  --abstr_ref_prep                        false
% 15.97/2.53  --abstr_ref_until_sat                   false
% 15.97/2.53  --abstr_ref_sig_restrict                funpre
% 15.97/2.53  --abstr_ref_af_restrict_to_split_sk     false
% 15.97/2.53  --abstr_ref_under                       []
% 15.97/2.53  
% 15.97/2.53  ------ SAT Options
% 15.97/2.53  
% 15.97/2.53  --sat_mode                              false
% 15.97/2.53  --sat_fm_restart_options                ""
% 15.97/2.53  --sat_gr_def                            false
% 15.97/2.53  --sat_epr_types                         true
% 15.97/2.53  --sat_non_cyclic_types                  false
% 15.97/2.53  --sat_finite_models                     false
% 15.97/2.53  --sat_fm_lemmas                         false
% 15.97/2.53  --sat_fm_prep                           false
% 15.97/2.53  --sat_fm_uc_incr                        true
% 15.97/2.53  --sat_out_model                         small
% 15.97/2.53  --sat_out_clauses                       false
% 15.97/2.53  
% 15.97/2.53  ------ QBF Options
% 15.97/2.53  
% 15.97/2.53  --qbf_mode                              false
% 15.97/2.53  --qbf_elim_univ                         false
% 15.97/2.53  --qbf_dom_inst                          none
% 15.97/2.53  --qbf_dom_pre_inst                      false
% 15.97/2.53  --qbf_sk_in                             false
% 15.97/2.53  --qbf_pred_elim                         true
% 15.97/2.53  --qbf_split                             512
% 15.97/2.53  
% 15.97/2.53  ------ BMC1 Options
% 15.97/2.53  
% 15.97/2.53  --bmc1_incremental                      false
% 15.97/2.53  --bmc1_axioms                           reachable_all
% 15.97/2.53  --bmc1_min_bound                        0
% 15.97/2.53  --bmc1_max_bound                        -1
% 15.97/2.53  --bmc1_max_bound_default                -1
% 15.97/2.53  --bmc1_symbol_reachability              true
% 15.97/2.53  --bmc1_property_lemmas                  false
% 15.97/2.53  --bmc1_k_induction                      false
% 15.97/2.53  --bmc1_non_equiv_states                 false
% 15.97/2.53  --bmc1_deadlock                         false
% 15.97/2.53  --bmc1_ucm                              false
% 15.97/2.53  --bmc1_add_unsat_core                   none
% 15.97/2.53  --bmc1_unsat_core_children              false
% 15.97/2.53  --bmc1_unsat_core_extrapolate_axioms    false
% 15.97/2.53  --bmc1_out_stat                         full
% 15.97/2.53  --bmc1_ground_init                      false
% 15.97/2.53  --bmc1_pre_inst_next_state              false
% 15.97/2.53  --bmc1_pre_inst_state                   false
% 15.97/2.53  --bmc1_pre_inst_reach_state             false
% 15.97/2.53  --bmc1_out_unsat_core                   false
% 15.97/2.53  --bmc1_aig_witness_out                  false
% 15.97/2.53  --bmc1_verbose                          false
% 15.97/2.53  --bmc1_dump_clauses_tptp                false
% 15.97/2.53  --bmc1_dump_unsat_core_tptp             false
% 15.97/2.53  --bmc1_dump_file                        -
% 15.97/2.53  --bmc1_ucm_expand_uc_limit              128
% 15.97/2.53  --bmc1_ucm_n_expand_iterations          6
% 15.97/2.53  --bmc1_ucm_extend_mode                  1
% 15.97/2.53  --bmc1_ucm_init_mode                    2
% 15.97/2.53  --bmc1_ucm_cone_mode                    none
% 15.97/2.53  --bmc1_ucm_reduced_relation_type        0
% 15.97/2.53  --bmc1_ucm_relax_model                  4
% 15.97/2.53  --bmc1_ucm_full_tr_after_sat            true
% 15.97/2.53  --bmc1_ucm_expand_neg_assumptions       false
% 15.97/2.53  --bmc1_ucm_layered_model                none
% 15.97/2.53  --bmc1_ucm_max_lemma_size               10
% 15.97/2.53  
% 15.97/2.53  ------ AIG Options
% 15.97/2.53  
% 15.97/2.53  --aig_mode                              false
% 15.97/2.53  
% 15.97/2.53  ------ Instantiation Options
% 15.97/2.53  
% 15.97/2.53  --instantiation_flag                    true
% 15.97/2.53  --inst_sos_flag                         true
% 15.97/2.53  --inst_sos_phase                        true
% 15.97/2.53  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.97/2.53  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.97/2.53  --inst_lit_sel_side                     num_symb
% 15.97/2.53  --inst_solver_per_active                1400
% 15.97/2.53  --inst_solver_calls_frac                1.
% 15.97/2.53  --inst_passive_queue_type               priority_queues
% 15.97/2.53  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.97/2.53  --inst_passive_queues_freq              [25;2]
% 15.97/2.53  --inst_dismatching                      true
% 15.97/2.53  --inst_eager_unprocessed_to_passive     true
% 15.97/2.53  --inst_prop_sim_given                   true
% 15.97/2.53  --inst_prop_sim_new                     false
% 15.97/2.53  --inst_subs_new                         false
% 15.97/2.53  --inst_eq_res_simp                      false
% 15.97/2.53  --inst_subs_given                       false
% 15.97/2.53  --inst_orphan_elimination               true
% 15.97/2.53  --inst_learning_loop_flag               true
% 15.97/2.53  --inst_learning_start                   3000
% 15.97/2.53  --inst_learning_factor                  2
% 15.97/2.53  --inst_start_prop_sim_after_learn       3
% 15.97/2.53  --inst_sel_renew                        solver
% 15.97/2.53  --inst_lit_activity_flag                true
% 15.97/2.53  --inst_restr_to_given                   false
% 15.97/2.53  --inst_activity_threshold               500
% 15.97/2.53  --inst_out_proof                        true
% 15.97/2.53  
% 15.97/2.53  ------ Resolution Options
% 15.97/2.53  
% 15.97/2.53  --resolution_flag                       true
% 15.97/2.53  --res_lit_sel                           adaptive
% 15.97/2.53  --res_lit_sel_side                      none
% 15.97/2.53  --res_ordering                          kbo
% 15.97/2.53  --res_to_prop_solver                    active
% 15.97/2.53  --res_prop_simpl_new                    false
% 15.97/2.53  --res_prop_simpl_given                  true
% 15.97/2.53  --res_passive_queue_type                priority_queues
% 15.97/2.53  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.97/2.53  --res_passive_queues_freq               [15;5]
% 15.97/2.53  --res_forward_subs                      full
% 15.97/2.53  --res_backward_subs                     full
% 15.97/2.53  --res_forward_subs_resolution           true
% 15.97/2.53  --res_backward_subs_resolution          true
% 15.97/2.53  --res_orphan_elimination                true
% 15.97/2.53  --res_time_limit                        2.
% 15.97/2.53  --res_out_proof                         true
% 15.97/2.53  
% 15.97/2.53  ------ Superposition Options
% 15.97/2.53  
% 15.97/2.53  --superposition_flag                    true
% 15.97/2.53  --sup_passive_queue_type                priority_queues
% 15.97/2.53  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.97/2.53  --sup_passive_queues_freq               [8;1;4]
% 15.97/2.53  --demod_completeness_check              fast
% 15.97/2.53  --demod_use_ground                      true
% 15.97/2.53  --sup_to_prop_solver                    passive
% 15.97/2.53  --sup_prop_simpl_new                    true
% 15.97/2.53  --sup_prop_simpl_given                  true
% 15.97/2.53  --sup_fun_splitting                     true
% 15.97/2.53  --sup_smt_interval                      50000
% 15.97/2.53  
% 15.97/2.53  ------ Superposition Simplification Setup
% 15.97/2.53  
% 15.97/2.53  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 15.97/2.53  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 15.97/2.53  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 15.97/2.53  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 15.97/2.53  --sup_full_triv                         [TrivRules;PropSubs]
% 15.97/2.53  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 15.97/2.53  --sup_full_bw                           [BwDemod;BwSubsumption]
% 15.97/2.53  --sup_immed_triv                        [TrivRules]
% 15.97/2.53  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.97/2.53  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.97/2.53  --sup_immed_bw_main                     []
% 15.97/2.53  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 15.97/2.53  --sup_input_triv                        [Unflattening;TrivRules]
% 15.97/2.53  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.97/2.53  --sup_input_bw                          []
% 15.97/2.53  
% 15.97/2.53  ------ Combination Options
% 15.97/2.53  
% 15.97/2.53  --comb_res_mult                         3
% 15.97/2.53  --comb_sup_mult                         2
% 15.97/2.53  --comb_inst_mult                        10
% 15.97/2.53  
% 15.97/2.53  ------ Debug Options
% 15.97/2.53  
% 15.97/2.53  --dbg_backtrace                         false
% 15.97/2.53  --dbg_dump_prop_clauses                 false
% 15.97/2.53  --dbg_dump_prop_clauses_file            -
% 15.97/2.53  --dbg_out_stat                          false
% 15.97/2.53  ------ Parsing...
% 15.97/2.53  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.97/2.53  
% 15.97/2.53  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 15.97/2.53  
% 15.97/2.53  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.97/2.53  
% 15.97/2.53  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.97/2.53  ------ Proving...
% 15.97/2.53  ------ Problem Properties 
% 15.97/2.53  
% 15.97/2.53  
% 15.97/2.53  clauses                                 16
% 15.97/2.53  conjectures                             4
% 15.97/2.53  EPR                                     4
% 15.97/2.53  Horn                                    16
% 15.97/2.53  unary                                   12
% 15.97/2.53  binary                                  4
% 15.97/2.53  lits                                    20
% 15.97/2.53  lits eq                                 14
% 15.97/2.53  fd_pure                                 0
% 15.97/2.53  fd_pseudo                               0
% 15.97/2.53  fd_cond                                 0
% 15.97/2.53  fd_pseudo_cond                          0
% 15.97/2.53  AC symbols                              0
% 15.97/2.53  
% 15.97/2.53  ------ Schedule dynamic 5 is on 
% 15.97/2.53  
% 15.97/2.53  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 15.97/2.53  
% 15.97/2.53  
% 15.97/2.53  ------ 
% 15.97/2.53  Current options:
% 15.97/2.53  ------ 
% 15.97/2.53  
% 15.97/2.53  ------ Input Options
% 15.97/2.53  
% 15.97/2.53  --out_options                           all
% 15.97/2.53  --tptp_safe_out                         true
% 15.97/2.53  --problem_path                          ""
% 15.97/2.53  --include_path                          ""
% 15.97/2.53  --clausifier                            res/vclausify_rel
% 15.97/2.53  --clausifier_options                    ""
% 15.97/2.53  --stdin                                 false
% 15.97/2.53  --stats_out                             all
% 15.97/2.53  
% 15.97/2.53  ------ General Options
% 15.97/2.53  
% 15.97/2.53  --fof                                   false
% 15.97/2.53  --time_out_real                         305.
% 15.97/2.53  --time_out_virtual                      -1.
% 15.97/2.53  --symbol_type_check                     false
% 15.97/2.53  --clausify_out                          false
% 15.97/2.53  --sig_cnt_out                           false
% 15.97/2.53  --trig_cnt_out                          false
% 15.97/2.53  --trig_cnt_out_tolerance                1.
% 15.97/2.53  --trig_cnt_out_sk_spl                   false
% 15.97/2.53  --abstr_cl_out                          false
% 15.97/2.53  
% 15.97/2.53  ------ Global Options
% 15.97/2.53  
% 15.97/2.53  --schedule                              default
% 15.97/2.53  --add_important_lit                     false
% 15.97/2.53  --prop_solver_per_cl                    1000
% 15.97/2.53  --min_unsat_core                        false
% 15.97/2.53  --soft_assumptions                      false
% 15.97/2.53  --soft_lemma_size                       3
% 15.97/2.53  --prop_impl_unit_size                   0
% 15.97/2.53  --prop_impl_unit                        []
% 15.97/2.53  --share_sel_clauses                     true
% 15.97/2.53  --reset_solvers                         false
% 15.97/2.53  --bc_imp_inh                            [conj_cone]
% 15.97/2.53  --conj_cone_tolerance                   3.
% 15.97/2.53  --extra_neg_conj                        none
% 15.97/2.53  --large_theory_mode                     true
% 15.97/2.53  --prolific_symb_bound                   200
% 15.97/2.53  --lt_threshold                          2000
% 15.97/2.53  --clause_weak_htbl                      true
% 15.97/2.53  --gc_record_bc_elim                     false
% 15.97/2.53  
% 15.97/2.53  ------ Preprocessing Options
% 15.97/2.53  
% 15.97/2.53  --preprocessing_flag                    true
% 15.97/2.53  --time_out_prep_mult                    0.1
% 15.97/2.53  --splitting_mode                        input
% 15.97/2.53  --splitting_grd                         true
% 15.97/2.53  --splitting_cvd                         false
% 15.97/2.53  --splitting_cvd_svl                     false
% 15.97/2.53  --splitting_nvd                         32
% 15.97/2.53  --sub_typing                            true
% 15.97/2.53  --prep_gs_sim                           true
% 15.97/2.53  --prep_unflatten                        true
% 15.97/2.53  --prep_res_sim                          true
% 15.97/2.53  --prep_upred                            true
% 15.97/2.53  --prep_sem_filter                       exhaustive
% 15.97/2.53  --prep_sem_filter_out                   false
% 15.97/2.53  --pred_elim                             true
% 15.97/2.53  --res_sim_input                         true
% 15.97/2.53  --eq_ax_congr_red                       true
% 15.97/2.53  --pure_diseq_elim                       true
% 15.97/2.53  --brand_transform                       false
% 15.97/2.53  --non_eq_to_eq                          false
% 15.97/2.53  --prep_def_merge                        true
% 15.97/2.53  --prep_def_merge_prop_impl              false
% 15.97/2.53  --prep_def_merge_mbd                    true
% 15.97/2.53  --prep_def_merge_tr_red                 false
% 15.97/2.53  --prep_def_merge_tr_cl                  false
% 15.97/2.53  --smt_preprocessing                     true
% 15.97/2.53  --smt_ac_axioms                         fast
% 15.97/2.53  --preprocessed_out                      false
% 15.97/2.53  --preprocessed_stats                    false
% 15.97/2.53  
% 15.97/2.53  ------ Abstraction refinement Options
% 15.97/2.53  
% 15.97/2.53  --abstr_ref                             []
% 15.97/2.53  --abstr_ref_prep                        false
% 15.97/2.53  --abstr_ref_until_sat                   false
% 15.97/2.53  --abstr_ref_sig_restrict                funpre
% 15.97/2.53  --abstr_ref_af_restrict_to_split_sk     false
% 15.97/2.53  --abstr_ref_under                       []
% 15.97/2.53  
% 15.97/2.53  ------ SAT Options
% 15.97/2.53  
% 15.97/2.53  --sat_mode                              false
% 15.97/2.53  --sat_fm_restart_options                ""
% 15.97/2.53  --sat_gr_def                            false
% 15.97/2.53  --sat_epr_types                         true
% 15.97/2.53  --sat_non_cyclic_types                  false
% 15.97/2.53  --sat_finite_models                     false
% 15.97/2.53  --sat_fm_lemmas                         false
% 15.97/2.53  --sat_fm_prep                           false
% 15.97/2.53  --sat_fm_uc_incr                        true
% 15.97/2.53  --sat_out_model                         small
% 15.97/2.53  --sat_out_clauses                       false
% 15.97/2.53  
% 15.97/2.53  ------ QBF Options
% 15.97/2.53  
% 15.97/2.53  --qbf_mode                              false
% 15.97/2.53  --qbf_elim_univ                         false
% 15.97/2.53  --qbf_dom_inst                          none
% 15.97/2.53  --qbf_dom_pre_inst                      false
% 15.97/2.53  --qbf_sk_in                             false
% 15.97/2.53  --qbf_pred_elim                         true
% 15.97/2.53  --qbf_split                             512
% 15.97/2.53  
% 15.97/2.53  ------ BMC1 Options
% 15.97/2.53  
% 15.97/2.53  --bmc1_incremental                      false
% 15.97/2.53  --bmc1_axioms                           reachable_all
% 15.97/2.53  --bmc1_min_bound                        0
% 15.97/2.53  --bmc1_max_bound                        -1
% 15.97/2.53  --bmc1_max_bound_default                -1
% 15.97/2.53  --bmc1_symbol_reachability              true
% 15.97/2.53  --bmc1_property_lemmas                  false
% 15.97/2.53  --bmc1_k_induction                      false
% 15.97/2.53  --bmc1_non_equiv_states                 false
% 15.97/2.53  --bmc1_deadlock                         false
% 15.97/2.53  --bmc1_ucm                              false
% 15.97/2.53  --bmc1_add_unsat_core                   none
% 15.97/2.53  --bmc1_unsat_core_children              false
% 15.97/2.53  --bmc1_unsat_core_extrapolate_axioms    false
% 15.97/2.53  --bmc1_out_stat                         full
% 15.97/2.53  --bmc1_ground_init                      false
% 15.97/2.53  --bmc1_pre_inst_next_state              false
% 15.97/2.53  --bmc1_pre_inst_state                   false
% 15.97/2.53  --bmc1_pre_inst_reach_state             false
% 15.97/2.53  --bmc1_out_unsat_core                   false
% 15.97/2.53  --bmc1_aig_witness_out                  false
% 15.97/2.53  --bmc1_verbose                          false
% 15.97/2.53  --bmc1_dump_clauses_tptp                false
% 15.97/2.53  --bmc1_dump_unsat_core_tptp             false
% 15.97/2.53  --bmc1_dump_file                        -
% 15.97/2.53  --bmc1_ucm_expand_uc_limit              128
% 15.97/2.53  --bmc1_ucm_n_expand_iterations          6
% 15.97/2.53  --bmc1_ucm_extend_mode                  1
% 15.97/2.53  --bmc1_ucm_init_mode                    2
% 15.97/2.53  --bmc1_ucm_cone_mode                    none
% 15.97/2.53  --bmc1_ucm_reduced_relation_type        0
% 15.97/2.53  --bmc1_ucm_relax_model                  4
% 15.97/2.53  --bmc1_ucm_full_tr_after_sat            true
% 15.97/2.53  --bmc1_ucm_expand_neg_assumptions       false
% 15.97/2.53  --bmc1_ucm_layered_model                none
% 15.97/2.53  --bmc1_ucm_max_lemma_size               10
% 15.97/2.53  
% 15.97/2.53  ------ AIG Options
% 15.97/2.53  
% 15.97/2.53  --aig_mode                              false
% 15.97/2.53  
% 15.97/2.53  ------ Instantiation Options
% 15.97/2.53  
% 15.97/2.53  --instantiation_flag                    true
% 15.97/2.53  --inst_sos_flag                         true
% 15.97/2.53  --inst_sos_phase                        true
% 15.97/2.53  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.97/2.53  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.97/2.53  --inst_lit_sel_side                     none
% 15.97/2.53  --inst_solver_per_active                1400
% 15.97/2.53  --inst_solver_calls_frac                1.
% 15.97/2.53  --inst_passive_queue_type               priority_queues
% 15.97/2.53  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.97/2.53  --inst_passive_queues_freq              [25;2]
% 15.97/2.53  --inst_dismatching                      true
% 15.97/2.53  --inst_eager_unprocessed_to_passive     true
% 15.97/2.53  --inst_prop_sim_given                   true
% 15.97/2.53  --inst_prop_sim_new                     false
% 15.97/2.53  --inst_subs_new                         false
% 15.97/2.53  --inst_eq_res_simp                      false
% 15.97/2.53  --inst_subs_given                       false
% 15.97/2.53  --inst_orphan_elimination               true
% 15.97/2.53  --inst_learning_loop_flag               true
% 15.97/2.53  --inst_learning_start                   3000
% 15.97/2.53  --inst_learning_factor                  2
% 15.97/2.53  --inst_start_prop_sim_after_learn       3
% 15.97/2.53  --inst_sel_renew                        solver
% 15.97/2.53  --inst_lit_activity_flag                true
% 15.97/2.53  --inst_restr_to_given                   false
% 15.97/2.53  --inst_activity_threshold               500
% 15.97/2.53  --inst_out_proof                        true
% 15.97/2.53  
% 15.97/2.53  ------ Resolution Options
% 15.97/2.53  
% 15.97/2.53  --resolution_flag                       false
% 15.97/2.53  --res_lit_sel                           adaptive
% 15.97/2.53  --res_lit_sel_side                      none
% 15.97/2.53  --res_ordering                          kbo
% 15.97/2.53  --res_to_prop_solver                    active
% 15.97/2.53  --res_prop_simpl_new                    false
% 15.97/2.53  --res_prop_simpl_given                  true
% 15.97/2.53  --res_passive_queue_type                priority_queues
% 15.97/2.53  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.97/2.53  --res_passive_queues_freq               [15;5]
% 15.97/2.53  --res_forward_subs                      full
% 15.97/2.53  --res_backward_subs                     full
% 15.97/2.53  --res_forward_subs_resolution           true
% 15.97/2.53  --res_backward_subs_resolution          true
% 15.97/2.53  --res_orphan_elimination                true
% 15.97/2.53  --res_time_limit                        2.
% 15.97/2.53  --res_out_proof                         true
% 15.97/2.53  
% 15.97/2.53  ------ Superposition Options
% 15.97/2.53  
% 15.97/2.53  --superposition_flag                    true
% 15.97/2.53  --sup_passive_queue_type                priority_queues
% 15.97/2.53  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.97/2.53  --sup_passive_queues_freq               [8;1;4]
% 15.97/2.53  --demod_completeness_check              fast
% 15.97/2.53  --demod_use_ground                      true
% 15.97/2.53  --sup_to_prop_solver                    passive
% 15.97/2.53  --sup_prop_simpl_new                    true
% 15.97/2.53  --sup_prop_simpl_given                  true
% 15.97/2.53  --sup_fun_splitting                     true
% 15.97/2.53  --sup_smt_interval                      50000
% 15.97/2.53  
% 15.97/2.53  ------ Superposition Simplification Setup
% 15.97/2.53  
% 15.97/2.53  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 15.97/2.53  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 15.97/2.53  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 15.97/2.53  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 15.97/2.53  --sup_full_triv                         [TrivRules;PropSubs]
% 15.97/2.53  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 15.97/2.53  --sup_full_bw                           [BwDemod;BwSubsumption]
% 15.97/2.53  --sup_immed_triv                        [TrivRules]
% 15.97/2.53  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.97/2.53  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.97/2.53  --sup_immed_bw_main                     []
% 15.97/2.53  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 15.97/2.53  --sup_input_triv                        [Unflattening;TrivRules]
% 15.97/2.53  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.97/2.53  --sup_input_bw                          []
% 15.97/2.53  
% 15.97/2.53  ------ Combination Options
% 15.97/2.53  
% 15.97/2.53  --comb_res_mult                         3
% 15.97/2.53  --comb_sup_mult                         2
% 15.97/2.53  --comb_inst_mult                        10
% 15.97/2.53  
% 15.97/2.53  ------ Debug Options
% 15.97/2.53  
% 15.97/2.53  --dbg_backtrace                         false
% 15.97/2.53  --dbg_dump_prop_clauses                 false
% 15.97/2.53  --dbg_dump_prop_clauses_file            -
% 15.97/2.53  --dbg_out_stat                          false
% 15.97/2.53  
% 15.97/2.53  
% 15.97/2.53  
% 15.97/2.53  
% 15.97/2.53  ------ Proving...
% 15.97/2.53  
% 15.97/2.53  
% 15.97/2.53  % SZS status Theorem for theBenchmark.p
% 15.97/2.53  
% 15.97/2.53  % SZS output start CNFRefutation for theBenchmark.p
% 15.97/2.53  
% 15.97/2.53  fof(f14,conjecture,(
% 15.97/2.53    ! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 15.97/2.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.97/2.53  
% 15.97/2.53  fof(f15,negated_conjecture,(
% 15.97/2.53    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 15.97/2.53    inference(negated_conjecture,[],[f14])).
% 15.97/2.53  
% 15.97/2.53  fof(f20,plain,(
% 15.97/2.53    ? [X0,X1,X2,X3] : (X1 != X2 & (r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)))),
% 15.97/2.53    inference(ennf_transformation,[],[f15])).
% 15.97/2.53  
% 15.97/2.53  fof(f21,plain,(
% 15.97/2.53    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3))),
% 15.97/2.53    inference(flattening,[],[f20])).
% 15.97/2.53  
% 15.97/2.53  fof(f23,plain,(
% 15.97/2.53    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => (sK1 != sK2 & r1_xboole_0(sK3,sK1) & r1_xboole_0(sK2,sK0) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3))),
% 15.97/2.53    introduced(choice_axiom,[])).
% 15.97/2.53  
% 15.97/2.53  fof(f24,plain,(
% 15.97/2.53    sK1 != sK2 & r1_xboole_0(sK3,sK1) & r1_xboole_0(sK2,sK0) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 15.97/2.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f21,f23])).
% 15.97/2.53  
% 15.97/2.53  fof(f41,plain,(
% 15.97/2.53    r1_xboole_0(sK3,sK1)),
% 15.97/2.53    inference(cnf_transformation,[],[f24])).
% 15.97/2.53  
% 15.97/2.53  fof(f2,axiom,(
% 15.97/2.53    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 15.97/2.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.97/2.53  
% 15.97/2.53  fof(f17,plain,(
% 15.97/2.53    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 15.97/2.53    inference(ennf_transformation,[],[f2])).
% 15.97/2.53  
% 15.97/2.53  fof(f27,plain,(
% 15.97/2.53    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 15.97/2.53    inference(cnf_transformation,[],[f17])).
% 15.97/2.53  
% 15.97/2.53  fof(f1,axiom,(
% 15.97/2.53    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 15.97/2.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.97/2.53  
% 15.97/2.53  fof(f22,plain,(
% 15.97/2.53    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 15.97/2.53    inference(nnf_transformation,[],[f1])).
% 15.97/2.53  
% 15.97/2.53  fof(f25,plain,(
% 15.97/2.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 15.97/2.53    inference(cnf_transformation,[],[f22])).
% 15.97/2.53  
% 15.97/2.53  fof(f12,axiom,(
% 15.97/2.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 15.97/2.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.97/2.53  
% 15.97/2.53  fof(f37,plain,(
% 15.97/2.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 15.97/2.53    inference(cnf_transformation,[],[f12])).
% 15.97/2.53  
% 15.97/2.53  fof(f44,plain,(
% 15.97/2.53    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 15.97/2.53    inference(definition_unfolding,[],[f25,f37])).
% 15.97/2.53  
% 15.97/2.53  fof(f11,axiom,(
% 15.97/2.53    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 15.97/2.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.97/2.53  
% 15.97/2.53  fof(f36,plain,(
% 15.97/2.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 15.97/2.53    inference(cnf_transformation,[],[f11])).
% 15.97/2.53  
% 15.97/2.53  fof(f47,plain,(
% 15.97/2.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 15.97/2.53    inference(definition_unfolding,[],[f36,f37])).
% 15.97/2.53  
% 15.97/2.53  fof(f8,axiom,(
% 15.97/2.53    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 15.97/2.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.97/2.53  
% 15.97/2.53  fof(f33,plain,(
% 15.97/2.53    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 15.97/2.53    inference(cnf_transformation,[],[f8])).
% 15.97/2.53  
% 15.97/2.53  fof(f39,plain,(
% 15.97/2.53    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 15.97/2.53    inference(cnf_transformation,[],[f24])).
% 15.97/2.53  
% 15.97/2.53  fof(f6,axiom,(
% 15.97/2.53    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 15.97/2.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.97/2.53  
% 15.97/2.53  fof(f31,plain,(
% 15.97/2.53    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 15.97/2.53    inference(cnf_transformation,[],[f6])).
% 15.97/2.53  
% 15.97/2.53  fof(f46,plain,(
% 15.97/2.53    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 15.97/2.53    inference(definition_unfolding,[],[f31,f37])).
% 15.97/2.53  
% 15.97/2.53  fof(f13,axiom,(
% 15.97/2.53    ! [X0,X1,X2] : k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 15.97/2.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.97/2.53  
% 15.97/2.53  fof(f38,plain,(
% 15.97/2.53    ( ! [X2,X0,X1] : (k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 15.97/2.53    inference(cnf_transformation,[],[f13])).
% 15.97/2.53  
% 15.97/2.53  fof(f48,plain,(
% 15.97/2.53    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)))) )),
% 15.97/2.53    inference(definition_unfolding,[],[f38,f37])).
% 15.97/2.53  
% 15.97/2.53  fof(f9,axiom,(
% 15.97/2.53    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 15.97/2.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.97/2.53  
% 15.97/2.53  fof(f34,plain,(
% 15.97/2.53    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 15.97/2.53    inference(cnf_transformation,[],[f9])).
% 15.97/2.53  
% 15.97/2.53  fof(f4,axiom,(
% 15.97/2.53    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 15.97/2.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.97/2.53  
% 15.97/2.53  fof(f29,plain,(
% 15.97/2.53    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 15.97/2.53    inference(cnf_transformation,[],[f4])).
% 15.97/2.53  
% 15.97/2.53  fof(f10,axiom,(
% 15.97/2.53    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 15.97/2.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.97/2.53  
% 15.97/2.53  fof(f35,plain,(
% 15.97/2.53    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 15.97/2.53    inference(cnf_transformation,[],[f10])).
% 15.97/2.53  
% 15.97/2.53  fof(f7,axiom,(
% 15.97/2.53    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 15.97/2.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.97/2.53  
% 15.97/2.53  fof(f16,plain,(
% 15.97/2.53    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) => r1_tarski(X0,X1))),
% 15.97/2.53    inference(unused_predicate_definition_removal,[],[f7])).
% 15.97/2.53  
% 15.97/2.53  fof(f19,plain,(
% 15.97/2.53    ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1))),
% 15.97/2.53    inference(ennf_transformation,[],[f16])).
% 15.97/2.53  
% 15.97/2.53  fof(f32,plain,(
% 15.97/2.53    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)) )),
% 15.97/2.53    inference(cnf_transformation,[],[f19])).
% 15.97/2.53  
% 15.97/2.53  fof(f3,axiom,(
% 15.97/2.53    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 15.97/2.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.97/2.53  
% 15.97/2.53  fof(f18,plain,(
% 15.97/2.53    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 15.97/2.53    inference(ennf_transformation,[],[f3])).
% 15.97/2.53  
% 15.97/2.53  fof(f28,plain,(
% 15.97/2.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 15.97/2.53    inference(cnf_transformation,[],[f18])).
% 15.97/2.53  
% 15.97/2.53  fof(f5,axiom,(
% 15.97/2.53    ! [X0,X1,X2] : k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k2_xboole_0(X0,k3_xboole_0(X1,X2))),
% 15.97/2.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.97/2.53  
% 15.97/2.53  fof(f30,plain,(
% 15.97/2.53    ( ! [X2,X0,X1] : (k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k2_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 15.97/2.53    inference(cnf_transformation,[],[f5])).
% 15.97/2.53  
% 15.97/2.53  fof(f45,plain,(
% 15.97/2.53    ( ! [X2,X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)))) )),
% 15.97/2.53    inference(definition_unfolding,[],[f30,f37,f37])).
% 15.97/2.53  
% 15.97/2.53  fof(f40,plain,(
% 15.97/2.53    r1_xboole_0(sK2,sK0)),
% 15.97/2.53    inference(cnf_transformation,[],[f24])).
% 15.97/2.53  
% 15.97/2.53  fof(f42,plain,(
% 15.97/2.53    sK1 != sK2),
% 15.97/2.53    inference(cnf_transformation,[],[f24])).
% 15.97/2.53  
% 15.97/2.53  cnf(c_14,negated_conjecture,
% 15.97/2.53      ( r1_xboole_0(sK3,sK1) ),
% 15.97/2.53      inference(cnf_transformation,[],[f41]) ).
% 15.97/2.53  
% 15.97/2.53  cnf(c_364,plain,
% 15.97/2.53      ( r1_xboole_0(sK3,sK1) = iProver_top ),
% 15.97/2.53      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 15.97/2.53  
% 15.97/2.53  cnf(c_2,plain,
% 15.97/2.53      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 15.97/2.53      inference(cnf_transformation,[],[f27]) ).
% 15.97/2.53  
% 15.97/2.53  cnf(c_365,plain,
% 15.97/2.53      ( r1_xboole_0(X0,X1) != iProver_top
% 15.97/2.53      | r1_xboole_0(X1,X0) = iProver_top ),
% 15.97/2.53      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 15.97/2.53  
% 15.97/2.53  cnf(c_1006,plain,
% 15.97/2.53      ( r1_xboole_0(sK1,sK3) = iProver_top ),
% 15.97/2.53      inference(superposition,[status(thm)],[c_364,c_365]) ).
% 15.97/2.53  
% 15.97/2.53  cnf(c_1,plain,
% 15.97/2.53      ( ~ r1_xboole_0(X0,X1)
% 15.97/2.53      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 15.97/2.53      inference(cnf_transformation,[],[f44]) ).
% 15.97/2.53  
% 15.97/2.53  cnf(c_366,plain,
% 15.97/2.53      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
% 15.97/2.53      | r1_xboole_0(X0,X1) != iProver_top ),
% 15.97/2.53      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 15.97/2.53  
% 15.97/2.53  cnf(c_1652,plain,
% 15.97/2.53      ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) = k1_xboole_0 ),
% 15.97/2.53      inference(superposition,[status(thm)],[c_1006,c_366]) ).
% 15.97/2.53  
% 15.97/2.53  cnf(c_11,plain,
% 15.97/2.53      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 15.97/2.53      inference(cnf_transformation,[],[f47]) ).
% 15.97/2.53  
% 15.97/2.53  cnf(c_34302,plain,
% 15.97/2.53      ( k4_xboole_0(sK1,sK3) = k4_xboole_0(sK1,k1_xboole_0) ),
% 15.97/2.53      inference(superposition,[status(thm)],[c_1652,c_11]) ).
% 15.97/2.53  
% 15.97/2.53  cnf(c_8,plain,
% 15.97/2.53      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 15.97/2.53      inference(cnf_transformation,[],[f33]) ).
% 15.97/2.53  
% 15.97/2.53  cnf(c_34426,plain,
% 15.97/2.53      ( k4_xboole_0(sK1,sK3) = sK1 ),
% 15.97/2.53      inference(demodulation,[status(thm)],[c_34302,c_8]) ).
% 15.97/2.53  
% 15.97/2.53  cnf(c_16,negated_conjecture,
% 15.97/2.53      ( k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
% 15.97/2.53      inference(cnf_transformation,[],[f39]) ).
% 15.97/2.53  
% 15.97/2.53  cnf(c_6,plain,
% 15.97/2.53      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 15.97/2.53      inference(cnf_transformation,[],[f46]) ).
% 15.97/2.53  
% 15.97/2.53  cnf(c_368,plain,
% 15.97/2.53      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 15.97/2.53      inference(light_normalisation,[status(thm)],[c_6,c_8]) ).
% 15.97/2.53  
% 15.97/2.53  cnf(c_12,plain,
% 15.97/2.53      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 15.97/2.53      inference(cnf_transformation,[],[f48]) ).
% 15.97/2.53  
% 15.97/2.53  cnf(c_9,plain,
% 15.97/2.53      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 15.97/2.53      inference(cnf_transformation,[],[f34]) ).
% 15.97/2.53  
% 15.97/2.53  cnf(c_369,plain,
% 15.97/2.53      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X2))))) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 15.97/2.53      inference(demodulation,[status(thm)],[c_12,c_9]) ).
% 15.97/2.53  
% 15.97/2.53  cnf(c_3743,plain,
% 15.97/2.53      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,k1_xboole_0)))) = k4_xboole_0(X0,k2_xboole_0(X1,X0)) ),
% 15.97/2.53      inference(superposition,[status(thm)],[c_368,c_369]) ).
% 15.97/2.53  
% 15.97/2.53  cnf(c_4,plain,
% 15.97/2.53      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 15.97/2.53      inference(cnf_transformation,[],[f29]) ).
% 15.97/2.53  
% 15.97/2.53  cnf(c_553,plain,
% 15.97/2.53      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
% 15.97/2.53      inference(superposition,[status(thm)],[c_9,c_368]) ).
% 15.97/2.53  
% 15.97/2.53  cnf(c_3856,plain,
% 15.97/2.53      ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 15.97/2.53      inference(demodulation,[status(thm)],[c_3743,c_4,c_553]) ).
% 15.97/2.53  
% 15.97/2.53  cnf(c_4088,plain,
% 15.97/2.53      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,k1_xboole_0)))) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X0))) ),
% 15.97/2.53      inference(superposition,[status(thm)],[c_3856,c_369]) ).
% 15.97/2.53  
% 15.97/2.53  cnf(c_3781,plain,
% 15.97/2.53      ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X1,k4_xboole_0(X0,X2)))) = k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2)))) ),
% 15.97/2.53      inference(superposition,[status(thm)],[c_369,c_369]) ).
% 15.97/2.53  
% 15.97/2.53  cnf(c_10,plain,
% 15.97/2.53      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
% 15.97/2.53      inference(cnf_transformation,[],[f35]) ).
% 15.97/2.53  
% 15.97/2.53  cnf(c_7,plain,
% 15.97/2.53      ( r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0 ),
% 15.97/2.53      inference(cnf_transformation,[],[f32]) ).
% 15.97/2.53  
% 15.97/2.53  cnf(c_3,plain,
% 15.97/2.53      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 15.97/2.53      inference(cnf_transformation,[],[f28]) ).
% 15.97/2.53  
% 15.97/2.53  cnf(c_123,plain,
% 15.97/2.53      ( k2_xboole_0(X0,X1) = X1 | k4_xboole_0(X0,X1) != k1_xboole_0 ),
% 15.97/2.53      inference(resolution,[status(thm)],[c_7,c_3]) ).
% 15.97/2.53  
% 15.97/2.53  cnf(c_538,plain,
% 15.97/2.53      ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
% 15.97/2.53      inference(superposition,[status(thm)],[c_10,c_123]) ).
% 15.97/2.53  
% 15.97/2.53  cnf(c_3816,plain,
% 15.97/2.53      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2)))) = k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X2))) ),
% 15.97/2.53      inference(demodulation,[status(thm)],[c_3781,c_538]) ).
% 15.97/2.53  
% 15.97/2.53  cnf(c_4124,plain,
% 15.97/2.53      ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X0))) = k1_xboole_0 ),
% 15.97/2.53      inference(demodulation,[status(thm)],[c_4088,c_8,c_3816,c_3856]) ).
% 15.97/2.53  
% 15.97/2.53  cnf(c_5318,plain,
% 15.97/2.53      ( k4_xboole_0(sK1,k2_xboole_0(X0,k2_xboole_0(sK2,sK3))) = k1_xboole_0 ),
% 15.97/2.53      inference(superposition,[status(thm)],[c_16,c_4124]) ).
% 15.97/2.53  
% 15.97/2.53  cnf(c_550,plain,
% 15.97/2.53      ( k2_xboole_0(k4_xboole_0(X0,X1),X2) = X2
% 15.97/2.53      | k4_xboole_0(X0,k2_xboole_0(X1,X2)) != k1_xboole_0 ),
% 15.97/2.53      inference(superposition,[status(thm)],[c_9,c_123]) ).
% 15.97/2.53  
% 15.97/2.53  cnf(c_6258,plain,
% 15.97/2.53      ( k2_xboole_0(k4_xboole_0(sK1,X0),k2_xboole_0(sK2,sK3)) = k2_xboole_0(sK2,sK3) ),
% 15.97/2.53      inference(superposition,[status(thm)],[c_5318,c_550]) ).
% 15.97/2.53  
% 15.97/2.53  cnf(c_7155,plain,
% 15.97/2.53      ( k4_xboole_0(k4_xboole_0(sK1,X0),k2_xboole_0(sK2,sK3)) = k1_xboole_0 ),
% 15.97/2.53      inference(superposition,[status(thm)],[c_6258,c_10]) ).
% 15.97/2.53  
% 15.97/2.53  cnf(c_5,plain,
% 15.97/2.53      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2))) = k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
% 15.97/2.53      inference(cnf_transformation,[],[f45]) ).
% 15.97/2.53  
% 15.97/2.53  cnf(c_1068,plain,
% 15.97/2.53      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2))) = k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X0,X2)))) ),
% 15.97/2.53      inference(superposition,[status(thm)],[c_538,c_5]) ).
% 15.97/2.53  
% 15.97/2.53  cnf(c_1077,plain,
% 15.97/2.53      ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X0,X2)))) = k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
% 15.97/2.53      inference(light_normalisation,[status(thm)],[c_1068,c_5]) ).
% 15.97/2.53  
% 15.97/2.53  cnf(c_56075,plain,
% 15.97/2.53      ( k2_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,X0),k4_xboole_0(k4_xboole_0(sK1,X0),sK3))) = k2_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,X0),k1_xboole_0)) ),
% 15.97/2.53      inference(superposition,[status(thm)],[c_7155,c_1077]) ).
% 15.97/2.53  
% 15.97/2.53  cnf(c_56378,plain,
% 15.97/2.53      ( k2_xboole_0(sK2,k4_xboole_0(sK1,k2_xboole_0(X0,k4_xboole_0(k4_xboole_0(sK1,X0),sK3)))) = k2_xboole_0(sK2,k4_xboole_0(sK1,k2_xboole_0(X0,k1_xboole_0))) ),
% 15.97/2.53      inference(demodulation,[status(thm)],[c_56075,c_9]) ).
% 15.97/2.53  
% 15.97/2.53  cnf(c_56379,plain,
% 15.97/2.53      ( k2_xboole_0(sK2,k4_xboole_0(sK1,k2_xboole_0(X0,k4_xboole_0(k4_xboole_0(sK1,X0),sK3)))) = k2_xboole_0(sK2,k4_xboole_0(sK1,X0)) ),
% 15.97/2.53      inference(light_normalisation,[status(thm)],[c_56378,c_4]) ).
% 15.97/2.53  
% 15.97/2.53  cnf(c_56380,plain,
% 15.97/2.53      ( k2_xboole_0(sK2,k4_xboole_0(sK1,k2_xboole_0(X0,k4_xboole_0(sK1,sK3)))) = k2_xboole_0(sK2,k4_xboole_0(sK1,X0)) ),
% 15.97/2.53      inference(demodulation,[status(thm)],[c_56379,c_9,c_3816]) ).
% 15.97/2.53  
% 15.97/2.53  cnf(c_56381,plain,
% 15.97/2.53      ( k2_xboole_0(sK2,k4_xboole_0(sK1,k2_xboole_0(X0,sK1))) = k2_xboole_0(sK2,k4_xboole_0(sK1,X0)) ),
% 15.97/2.53      inference(light_normalisation,[status(thm)],[c_56380,c_34426]) ).
% 15.97/2.53  
% 15.97/2.53  cnf(c_56382,plain,
% 15.97/2.53      ( k2_xboole_0(sK2,k4_xboole_0(sK1,X0)) = sK2 ),
% 15.97/2.53      inference(demodulation,[status(thm)],[c_56381,c_4,c_3856]) ).
% 15.97/2.53  
% 15.97/2.53  cnf(c_56533,plain,
% 15.97/2.53      ( k2_xboole_0(sK2,sK1) = sK2 ),
% 15.97/2.53      inference(superposition,[status(thm)],[c_34426,c_56382]) ).
% 15.97/2.53  
% 15.97/2.53  cnf(c_15,negated_conjecture,
% 15.97/2.53      ( r1_xboole_0(sK2,sK0) ),
% 15.97/2.53      inference(cnf_transformation,[],[f40]) ).
% 15.97/2.53  
% 15.97/2.53  cnf(c_363,plain,
% 15.97/2.53      ( r1_xboole_0(sK2,sK0) = iProver_top ),
% 15.97/2.53      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 15.97/2.53  
% 15.97/2.53  cnf(c_1651,plain,
% 15.97/2.53      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) = k1_xboole_0 ),
% 15.97/2.53      inference(superposition,[status(thm)],[c_363,c_366]) ).
% 15.97/2.53  
% 15.97/2.53  cnf(c_2221,plain,
% 15.97/2.53      ( k4_xboole_0(sK2,sK0) = k4_xboole_0(sK2,k1_xboole_0) ),
% 15.97/2.53      inference(superposition,[status(thm)],[c_1651,c_11]) ).
% 15.97/2.53  
% 15.97/2.53  cnf(c_2222,plain,
% 15.97/2.53      ( k4_xboole_0(sK2,sK0) = sK2 ),
% 15.97/2.53      inference(demodulation,[status(thm)],[c_2221,c_8]) ).
% 15.97/2.53  
% 15.97/2.53  cnf(c_2921,plain,
% 15.97/2.53      ( k4_xboole_0(sK2,k2_xboole_0(sK0,X0)) = k4_xboole_0(sK2,X0) ),
% 15.97/2.53      inference(superposition,[status(thm)],[c_2222,c_9]) ).
% 15.97/2.53  
% 15.97/2.53  cnf(c_3003,plain,
% 15.97/2.53      ( k4_xboole_0(sK2,k2_xboole_0(sK2,sK3)) = k4_xboole_0(sK2,sK1) ),
% 15.97/2.53      inference(superposition,[status(thm)],[c_16,c_2921]) ).
% 15.97/2.53  
% 15.97/2.53  cnf(c_3025,plain,
% 15.97/2.53      ( k4_xboole_0(sK2,sK1) = k1_xboole_0 ),
% 15.97/2.53      inference(demodulation,[status(thm)],[c_3003,c_10]) ).
% 15.97/2.53  
% 15.97/2.53  cnf(c_3112,plain,
% 15.97/2.53      ( k2_xboole_0(sK2,sK1) = sK1 ),
% 15.97/2.53      inference(superposition,[status(thm)],[c_3025,c_123]) ).
% 15.97/2.53  
% 15.97/2.53  cnf(c_56617,plain,
% 15.97/2.53      ( sK2 = sK1 ),
% 15.97/2.53      inference(light_normalisation,[status(thm)],[c_56533,c_3112]) ).
% 15.97/2.53  
% 15.97/2.53  cnf(c_198,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 15.97/2.53  
% 15.97/2.53  cnf(c_378,plain,
% 15.97/2.53      ( sK2 != X0 | sK1 != X0 | sK1 = sK2 ),
% 15.97/2.53      inference(instantiation,[status(thm)],[c_198]) ).
% 15.97/2.53  
% 15.97/2.53  cnf(c_37665,plain,
% 15.97/2.53      ( sK2 != sK1 | sK1 = sK2 | sK1 != sK1 ),
% 15.97/2.53      inference(instantiation,[status(thm)],[c_378]) ).
% 15.97/2.53  
% 15.97/2.53  cnf(c_197,plain,( X0 = X0 ),theory(equality) ).
% 15.97/2.53  
% 15.97/2.53  cnf(c_517,plain,
% 15.97/2.53      ( sK1 = sK1 ),
% 15.97/2.53      inference(instantiation,[status(thm)],[c_197]) ).
% 15.97/2.53  
% 15.97/2.53  cnf(c_13,negated_conjecture,
% 15.97/2.53      ( sK1 != sK2 ),
% 15.97/2.53      inference(cnf_transformation,[],[f42]) ).
% 15.97/2.53  
% 15.97/2.53  cnf(contradiction,plain,
% 15.97/2.53      ( $false ),
% 15.97/2.53      inference(minisat,[status(thm)],[c_56617,c_37665,c_517,c_13]) ).
% 15.97/2.53  
% 15.97/2.53  
% 15.97/2.53  % SZS output end CNFRefutation for theBenchmark.p
% 15.97/2.53  
% 15.97/2.53  ------                               Statistics
% 15.97/2.53  
% 15.97/2.53  ------ General
% 15.97/2.53  
% 15.97/2.53  abstr_ref_over_cycles:                  0
% 15.97/2.53  abstr_ref_under_cycles:                 0
% 15.97/2.53  gc_basic_clause_elim:                   0
% 15.97/2.53  forced_gc_time:                         0
% 15.97/2.53  parsing_time:                           0.022
% 15.97/2.53  unif_index_cands_time:                  0.
% 15.97/2.53  unif_index_add_time:                    0.
% 15.97/2.53  orderings_time:                         0.
% 15.97/2.53  out_proof_time:                         0.008
% 15.97/2.53  total_time:                             1.963
% 15.97/2.53  num_of_symbols:                         40
% 15.97/2.53  num_of_terms:                           86616
% 15.97/2.53  
% 15.97/2.53  ------ Preprocessing
% 15.97/2.53  
% 15.97/2.53  num_of_splits:                          0
% 15.97/2.53  num_of_split_atoms:                     0
% 15.97/2.53  num_of_reused_defs:                     0
% 15.97/2.53  num_eq_ax_congr_red:                    2
% 15.97/2.53  num_of_sem_filtered_clauses:            1
% 15.97/2.53  num_of_subtypes:                        0
% 15.97/2.53  monotx_restored_types:                  0
% 15.97/2.53  sat_num_of_epr_types:                   0
% 15.97/2.53  sat_num_of_non_cyclic_types:            0
% 15.97/2.53  sat_guarded_non_collapsed_types:        0
% 15.97/2.53  num_pure_diseq_elim:                    0
% 15.97/2.53  simp_replaced_by:                       0
% 15.97/2.53  res_preprocessed:                       76
% 15.97/2.53  prep_upred:                             0
% 15.97/2.53  prep_unflattend:                        0
% 15.97/2.53  smt_new_axioms:                         0
% 15.97/2.53  pred_elim_cands:                        1
% 15.97/2.53  pred_elim:                              1
% 15.97/2.53  pred_elim_cl:                           1
% 15.97/2.53  pred_elim_cycles:                       3
% 15.97/2.53  merged_defs:                            8
% 15.97/2.53  merged_defs_ncl:                        0
% 15.97/2.53  bin_hyper_res:                          8
% 15.97/2.53  prep_cycles:                            4
% 15.97/2.53  pred_elim_time:                         0.
% 15.97/2.53  splitting_time:                         0.
% 15.97/2.53  sem_filter_time:                        0.
% 15.97/2.53  monotx_time:                            0.
% 15.97/2.53  subtype_inf_time:                       0.
% 15.97/2.53  
% 15.97/2.53  ------ Problem properties
% 15.97/2.53  
% 15.97/2.53  clauses:                                16
% 15.97/2.53  conjectures:                            4
% 15.97/2.53  epr:                                    4
% 15.97/2.53  horn:                                   16
% 15.97/2.53  ground:                                 4
% 15.97/2.53  unary:                                  12
% 15.97/2.53  binary:                                 4
% 15.97/2.53  lits:                                   20
% 15.97/2.53  lits_eq:                                14
% 15.97/2.53  fd_pure:                                0
% 15.97/2.53  fd_pseudo:                              0
% 15.97/2.53  fd_cond:                                0
% 15.97/2.53  fd_pseudo_cond:                         0
% 15.97/2.53  ac_symbols:                             0
% 15.97/2.53  
% 15.97/2.53  ------ Propositional Solver
% 15.97/2.53  
% 15.97/2.53  prop_solver_calls:                      38
% 15.97/2.53  prop_fast_solver_calls:                 731
% 15.97/2.53  smt_solver_calls:                       0
% 15.97/2.53  smt_fast_solver_calls:                  0
% 15.97/2.53  prop_num_of_clauses:                    17054
% 15.97/2.53  prop_preprocess_simplified:             21959
% 15.97/2.53  prop_fo_subsumed:                       0
% 15.97/2.53  prop_solver_time:                       0.
% 15.97/2.53  smt_solver_time:                        0.
% 15.97/2.53  smt_fast_solver_time:                   0.
% 15.97/2.53  prop_fast_solver_time:                  0.
% 15.97/2.53  prop_unsat_core_time:                   0.001
% 15.97/2.53  
% 15.97/2.53  ------ QBF
% 15.97/2.53  
% 15.97/2.53  qbf_q_res:                              0
% 15.97/2.53  qbf_num_tautologies:                    0
% 15.97/2.53  qbf_prep_cycles:                        0
% 15.97/2.53  
% 15.97/2.53  ------ BMC1
% 15.97/2.53  
% 15.97/2.53  bmc1_current_bound:                     -1
% 15.97/2.53  bmc1_last_solved_bound:                 -1
% 15.97/2.53  bmc1_unsat_core_size:                   -1
% 15.97/2.53  bmc1_unsat_core_parents_size:           -1
% 15.97/2.53  bmc1_merge_next_fun:                    0
% 15.97/2.53  bmc1_unsat_core_clauses_time:           0.
% 15.97/2.53  
% 15.97/2.53  ------ Instantiation
% 15.97/2.53  
% 15.97/2.53  inst_num_of_clauses:                    7343
% 15.97/2.53  inst_num_in_passive:                    2936
% 15.97/2.53  inst_num_in_active:                     1242
% 15.97/2.53  inst_num_in_unprocessed:                3165
% 15.97/2.53  inst_num_of_loops:                      1780
% 15.97/2.53  inst_num_of_learning_restarts:          0
% 15.97/2.53  inst_num_moves_active_passive:          530
% 15.97/2.53  inst_lit_activity:                      0
% 15.97/2.53  inst_lit_activity_moves:                1
% 15.97/2.53  inst_num_tautologies:                   0
% 15.97/2.53  inst_num_prop_implied:                  0
% 15.97/2.53  inst_num_existing_simplified:           0
% 15.97/2.53  inst_num_eq_res_simplified:             0
% 15.97/2.53  inst_num_child_elim:                    0
% 15.97/2.53  inst_num_of_dismatching_blockings:      3417
% 15.97/2.53  inst_num_of_non_proper_insts:           6640
% 15.97/2.53  inst_num_of_duplicates:                 0
% 15.97/2.53  inst_inst_num_from_inst_to_res:         0
% 15.97/2.53  inst_dismatching_checking_time:         0.
% 15.97/2.53  
% 15.97/2.53  ------ Resolution
% 15.97/2.53  
% 15.97/2.53  res_num_of_clauses:                     0
% 15.97/2.53  res_num_in_passive:                     0
% 15.97/2.53  res_num_in_active:                      0
% 15.97/2.53  res_num_of_loops:                       80
% 15.97/2.53  res_forward_subset_subsumed:            2994
% 15.97/2.53  res_backward_subset_subsumed:           0
% 15.97/2.53  res_forward_subsumed:                   0
% 15.97/2.53  res_backward_subsumed:                  0
% 15.97/2.53  res_forward_subsumption_resolution:     0
% 15.97/2.53  res_backward_subsumption_resolution:    0
% 15.97/2.53  res_clause_to_clause_subsumption:       37446
% 15.97/2.53  res_orphan_elimination:                 0
% 15.97/2.53  res_tautology_del:                      308
% 15.97/2.53  res_num_eq_res_simplified:              0
% 15.97/2.53  res_num_sel_changes:                    0
% 15.97/2.53  res_moves_from_active_to_pass:          0
% 15.97/2.53  
% 15.97/2.53  ------ Superposition
% 15.97/2.53  
% 15.97/2.53  sup_time_total:                         0.
% 15.97/2.53  sup_time_generating:                    0.
% 15.97/2.53  sup_time_sim_full:                      0.
% 15.97/2.53  sup_time_sim_immed:                     0.
% 15.97/2.53  
% 15.97/2.53  sup_num_of_clauses:                     3398
% 15.97/2.53  sup_num_in_active:                      172
% 15.97/2.53  sup_num_in_passive:                     3226
% 15.97/2.53  sup_num_of_loops:                       355
% 15.97/2.53  sup_fw_superposition:                   6910
% 15.97/2.53  sup_bw_superposition:                   7129
% 15.97/2.53  sup_immediate_simplified:               9689
% 15.97/2.53  sup_given_eliminated:                   19
% 15.97/2.53  comparisons_done:                       0
% 15.97/2.53  comparisons_avoided:                    0
% 15.97/2.53  
% 15.97/2.53  ------ Simplifications
% 15.97/2.53  
% 15.97/2.53  
% 15.97/2.53  sim_fw_subset_subsumed:                 6
% 15.97/2.53  sim_bw_subset_subsumed:                 0
% 15.97/2.53  sim_fw_subsumed:                        2035
% 15.97/2.53  sim_bw_subsumed:                        73
% 15.97/2.53  sim_fw_subsumption_res:                 0
% 15.97/2.53  sim_bw_subsumption_res:                 0
% 15.97/2.53  sim_tautology_del:                      44
% 15.97/2.53  sim_eq_tautology_del:                   3461
% 15.97/2.53  sim_eq_res_simp:                        54
% 15.97/2.53  sim_fw_demodulated:                     7781
% 15.97/2.53  sim_bw_demodulated:                     344
% 15.97/2.53  sim_light_normalised:                   3533
% 15.97/2.53  sim_joinable_taut:                      0
% 15.97/2.53  sim_joinable_simp:                      0
% 15.97/2.53  sim_ac_normalised:                      0
% 15.97/2.53  sim_smt_subsumption:                    0
% 15.97/2.53  
%------------------------------------------------------------------------------
