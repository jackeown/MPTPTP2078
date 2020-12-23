%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:23:48 EST 2020

% Result     : Theorem 3.13s
% Output     : CNFRefutation 3.13s
% Verified   : 
% Statistics : Number of formulae       :  117 (1608 expanded)
%              Number of clauses        :   86 ( 495 expanded)
%              Number of leaves         :   10 ( 389 expanded)
%              Depth                    :   29
%              Number of atoms          :  149 (3090 expanded)
%              Number of equality atoms :  124 (2015 expanded)
%              Maximal formula depth    :    9 (   2 average)
%              Maximal clause size      :    8 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

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
    inference(definition_unfolding,[],[f19,f24])).

fof(f9,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X3,X1)
          & r1_xboole_0(X2,X0)
          & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
       => X1 = X2 ) ),
    inference(negated_conjecture,[],[f9])).

fof(f13,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f14,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(flattening,[],[f13])).

fof(f15,plain,
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

fof(f16,plain,
    ( sK1 != sK2
    & r1_xboole_0(sK3,sK1)
    & r1_xboole_0(sK2,sK0)
    & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f14,f15])).

fof(f26,plain,(
    r1_xboole_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f31,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f23,f24])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f27,plain,(
    r1_xboole_0(sK3,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f29,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f18,f24,f24])).

fof(f25,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f16])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f28,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f16])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_9,negated_conjecture,
    ( r1_xboole_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_55,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
    | sK0 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_9])).

cnf(c_56,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_55])).

cnf(c_6,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_127,plain,
    ( k4_xboole_0(sK2,k1_xboole_0) = k4_xboole_0(sK2,sK0) ),
    inference(superposition,[status(thm)],[c_56,c_6])).

cnf(c_3,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f20])).

cnf(c_152,plain,
    ( k4_xboole_0(sK2,sK0) = sK2 ),
    inference(demodulation,[status(thm)],[c_127,c_3])).

cnf(c_5,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_212,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(sK0,X0)) = k4_xboole_0(sK2,X0) ),
    inference(superposition,[status(thm)],[c_152,c_5])).

cnf(c_375,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(X0,sK0)) = k4_xboole_0(sK2,X0) ),
    inference(superposition,[status(thm)],[c_0,c_212])).

cnf(c_8,negated_conjecture,
    ( r1_xboole_0(sK3,sK1) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_50,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
    | sK3 != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_8])).

cnf(c_51,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_50])).

cnf(c_133,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,k1_xboole_0)) = k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)) ),
    inference(superposition,[status(thm)],[c_51,c_6])).

cnf(c_146,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,k1_xboole_0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_133,c_51])).

cnf(c_147,plain,
    ( k4_xboole_0(sK3,sK3) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_146,c_3])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_91,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_3,c_1])).

cnf(c_249,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X0)) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_91,c_6])).

cnf(c_532,plain,
    ( k4_xboole_0(k1_xboole_0,sK3) = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_147,c_249])).

cnf(c_541,plain,
    ( k4_xboole_0(k1_xboole_0,sK3) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_532,c_3])).

cnf(c_10,negated_conjecture,
    ( k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_72,plain,
    ( k2_xboole_0(sK1,sK0) = k2_xboole_0(sK2,sK3) ),
    inference(demodulation,[status(thm)],[c_0,c_10])).

cnf(c_106,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK2,sK0),X0)) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_56,c_5])).

cnf(c_187,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(sK2,X0)) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(light_normalisation,[status(thm)],[c_106,c_106,c_152])).

cnf(c_191,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(sK1,sK0)) = k4_xboole_0(k1_xboole_0,sK3) ),
    inference(superposition,[status(thm)],[c_72,c_187])).

cnf(c_787,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(sK1,sK0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_541,c_191])).

cnf(c_2009,plain,
    ( k4_xboole_0(sK2,sK1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_375,c_787])).

cnf(c_4,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_92,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_4,c_1])).

cnf(c_2065,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,k2_xboole_0(sK2,sK1))) = k4_xboole_0(k2_xboole_0(sK2,sK1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2009,c_92])).

cnf(c_95,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1,c_51])).

cnf(c_163,plain,
    ( k4_xboole_0(sK1,k2_xboole_0(k4_xboole_0(sK1,sK3),X0)) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_95,c_5])).

cnf(c_164,plain,
    ( k4_xboole_0(sK1,sK3) = k4_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_95,c_6])).

cnf(c_165,plain,
    ( k4_xboole_0(sK1,sK3) = sK1 ),
    inference(demodulation,[status(thm)],[c_164,c_3])).

cnf(c_174,plain,
    ( k4_xboole_0(sK1,k2_xboole_0(sK1,X0)) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(light_normalisation,[status(thm)],[c_163,c_165])).

cnf(c_290,plain,
    ( k4_xboole_0(sK1,k2_xboole_0(X0,sK1)) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_0,c_174])).

cnf(c_2079,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(k1_xboole_0,sK2)) = k2_xboole_0(sK2,sK1) ),
    inference(demodulation,[status(thm)],[c_2065,c_3,c_290])).

cnf(c_134,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k1_xboole_0)) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) ),
    inference(superposition,[status(thm)],[c_56,c_6])).

cnf(c_144,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k1_xboole_0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_134,c_56])).

cnf(c_145,plain,
    ( k4_xboole_0(sK2,sK2) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_144,c_3])).

cnf(c_531,plain,
    ( k4_xboole_0(k1_xboole_0,sK2) = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_145,c_249])).

cnf(c_542,plain,
    ( k4_xboole_0(k1_xboole_0,sK2) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_531,c_3])).

cnf(c_2080,plain,
    ( k4_xboole_0(sK1,k1_xboole_0) = k2_xboole_0(sK2,sK1) ),
    inference(light_normalisation,[status(thm)],[c_2079,c_542])).

cnf(c_2081,plain,
    ( k2_xboole_0(sK2,sK1) = sK1 ),
    inference(demodulation,[status(thm)],[c_2080,c_3])).

cnf(c_74,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_4])).

cnf(c_82,plain,
    ( k4_xboole_0(k2_xboole_0(sK1,sK0),sK2) = k4_xboole_0(sK3,sK2) ),
    inference(superposition,[status(thm)],[c_72,c_74])).

cnf(c_168,plain,
    ( k4_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK2,X0)) = k4_xboole_0(k4_xboole_0(sK3,sK2),X0) ),
    inference(superposition,[status(thm)],[c_82,c_5])).

cnf(c_171,plain,
    ( k4_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK2,X0)) = k4_xboole_0(sK3,k2_xboole_0(sK2,X0)) ),
    inference(demodulation,[status(thm)],[c_168,c_5])).

cnf(c_2510,plain,
    ( k4_xboole_0(k2_xboole_0(sK1,sK0),sK1) = k4_xboole_0(sK3,k2_xboole_0(sK2,sK1)) ),
    inference(superposition,[status(thm)],[c_2081,c_171])).

cnf(c_2513,plain,
    ( k4_xboole_0(k2_xboole_0(sK1,sK0),sK1) = k4_xboole_0(sK3,sK1) ),
    inference(demodulation,[status(thm)],[c_2510,c_2081])).

cnf(c_126,plain,
    ( k4_xboole_0(sK3,k1_xboole_0) = k4_xboole_0(sK3,sK1) ),
    inference(superposition,[status(thm)],[c_51,c_6])).

cnf(c_153,plain,
    ( k4_xboole_0(sK3,sK1) = sK3 ),
    inference(demodulation,[status(thm)],[c_126,c_3])).

cnf(c_2514,plain,
    ( k4_xboole_0(k2_xboole_0(sK1,sK0),sK1) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_2513,c_153])).

cnf(c_2637,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,k2_xboole_0(sK1,sK0))) = k4_xboole_0(k2_xboole_0(sK1,sK0),sK3) ),
    inference(superposition,[status(thm)],[c_2514,c_1])).

cnf(c_105,plain,
    ( k4_xboole_0(sK3,k2_xboole_0(k4_xboole_0(sK3,sK1),X0)) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_51,c_5])).

cnf(c_177,plain,
    ( k4_xboole_0(sK3,k2_xboole_0(sK3,X0)) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(light_normalisation,[status(thm)],[c_105,c_105,c_153])).

cnf(c_179,plain,
    ( k4_xboole_0(sK3,k2_xboole_0(X0,sK3)) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_0,c_177])).

cnf(c_301,plain,
    ( k4_xboole_0(sK3,k2_xboole_0(sK1,sK0)) = k4_xboole_0(k1_xboole_0,sK2) ),
    inference(superposition,[status(thm)],[c_72,c_179])).

cnf(c_223,plain,
    ( k4_xboole_0(sK3,k2_xboole_0(sK1,X0)) = k4_xboole_0(sK3,X0) ),
    inference(superposition,[status(thm)],[c_153,c_5])).

cnf(c_406,plain,
    ( k4_xboole_0(sK3,sK0) = k4_xboole_0(k1_xboole_0,sK2) ),
    inference(superposition,[status(thm)],[c_301,c_223])).

cnf(c_811,plain,
    ( k4_xboole_0(sK3,sK0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_542,c_406])).

cnf(c_93,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_74,c_1])).

cnf(c_863,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK0,sK3))) = k4_xboole_0(k2_xboole_0(sK0,sK3),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_811,c_93])).

cnf(c_189,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(X0,sK2)) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_0,c_187])).

cnf(c_380,plain,
    ( k4_xboole_0(k1_xboole_0,sK0) = k4_xboole_0(sK2,sK2) ),
    inference(superposition,[status(thm)],[c_212,c_189])).

cnf(c_381,plain,
    ( k4_xboole_0(k1_xboole_0,sK0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_380,c_145])).

cnf(c_426,plain,
    ( k4_xboole_0(sK0,sK0) = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_381,c_91])).

cnf(c_427,plain,
    ( k4_xboole_0(sK0,sK0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_426,c_3])).

cnf(c_510,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(sK0,X0)) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_427,c_5])).

cnf(c_864,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(k1_xboole_0,sK3)) = k2_xboole_0(sK0,sK3) ),
    inference(demodulation,[status(thm)],[c_863,c_3,c_510])).

cnf(c_865,plain,
    ( k4_xboole_0(sK0,k1_xboole_0) = k2_xboole_0(sK0,sK3) ),
    inference(light_normalisation,[status(thm)],[c_864,c_541])).

cnf(c_866,plain,
    ( k2_xboole_0(sK0,sK3) = sK0 ),
    inference(demodulation,[status(thm)],[c_865,c_3])).

cnf(c_1291,plain,
    ( k4_xboole_0(sK2,sK3) = k4_xboole_0(sK2,sK0) ),
    inference(superposition,[status(thm)],[c_866,c_212])).

cnf(c_1292,plain,
    ( k4_xboole_0(sK2,sK3) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_1291,c_152])).

cnf(c_76,plain,
    ( k4_xboole_0(k2_xboole_0(sK1,sK0),sK3) = k4_xboole_0(sK2,sK3) ),
    inference(superposition,[status(thm)],[c_72,c_4])).

cnf(c_1616,plain,
    ( k4_xboole_0(k2_xboole_0(sK1,sK0),sK3) = sK2 ),
    inference(demodulation,[status(thm)],[c_1292,c_76])).

cnf(c_2639,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,k2_xboole_0(sK1,sK0))) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_2637,c_1616])).

cnf(c_2640,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(k1_xboole_0,sK0)) = sK2 ),
    inference(demodulation,[status(thm)],[c_2639,c_174])).

cnf(c_2641,plain,
    ( k4_xboole_0(sK1,k1_xboole_0) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_2640,c_381])).

cnf(c_2642,plain,
    ( sK2 = sK1 ),
    inference(demodulation,[status(thm)],[c_2641,c_3])).

cnf(c_7,negated_conjecture,
    ( sK1 != sK2 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_2910,plain,
    ( sK1 != sK1 ),
    inference(demodulation,[status(thm)],[c_2642,c_7])).

cnf(c_2911,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_2910])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:02:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 3.13/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.13/0.99  
% 3.13/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.13/0.99  
% 3.13/0.99  ------  iProver source info
% 3.13/0.99  
% 3.13/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.13/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.13/0.99  git: non_committed_changes: false
% 3.13/0.99  git: last_make_outside_of_git: false
% 3.13/0.99  
% 3.13/0.99  ------ 
% 3.13/0.99  
% 3.13/0.99  ------ Input Options
% 3.13/0.99  
% 3.13/0.99  --out_options                           all
% 3.13/0.99  --tptp_safe_out                         true
% 3.13/0.99  --problem_path                          ""
% 3.13/0.99  --include_path                          ""
% 3.13/0.99  --clausifier                            res/vclausify_rel
% 3.13/0.99  --clausifier_options                    --mode clausify
% 3.13/0.99  --stdin                                 false
% 3.13/0.99  --stats_out                             all
% 3.13/0.99  
% 3.13/0.99  ------ General Options
% 3.13/0.99  
% 3.13/0.99  --fof                                   false
% 3.13/0.99  --time_out_real                         305.
% 3.13/0.99  --time_out_virtual                      -1.
% 3.13/0.99  --symbol_type_check                     false
% 3.13/0.99  --clausify_out                          false
% 3.13/0.99  --sig_cnt_out                           false
% 3.13/0.99  --trig_cnt_out                          false
% 3.13/0.99  --trig_cnt_out_tolerance                1.
% 3.13/0.99  --trig_cnt_out_sk_spl                   false
% 3.13/0.99  --abstr_cl_out                          false
% 3.13/0.99  
% 3.13/0.99  ------ Global Options
% 3.13/0.99  
% 3.13/0.99  --schedule                              default
% 3.13/0.99  --add_important_lit                     false
% 3.13/0.99  --prop_solver_per_cl                    1000
% 3.13/0.99  --min_unsat_core                        false
% 3.13/0.99  --soft_assumptions                      false
% 3.13/0.99  --soft_lemma_size                       3
% 3.13/0.99  --prop_impl_unit_size                   0
% 3.13/0.99  --prop_impl_unit                        []
% 3.13/0.99  --share_sel_clauses                     true
% 3.13/0.99  --reset_solvers                         false
% 3.13/0.99  --bc_imp_inh                            [conj_cone]
% 3.13/0.99  --conj_cone_tolerance                   3.
% 3.13/0.99  --extra_neg_conj                        none
% 3.13/0.99  --large_theory_mode                     true
% 3.13/0.99  --prolific_symb_bound                   200
% 3.13/0.99  --lt_threshold                          2000
% 3.13/0.99  --clause_weak_htbl                      true
% 3.13/0.99  --gc_record_bc_elim                     false
% 3.13/0.99  
% 3.13/0.99  ------ Preprocessing Options
% 3.13/0.99  
% 3.13/0.99  --preprocessing_flag                    true
% 3.13/0.99  --time_out_prep_mult                    0.1
% 3.13/0.99  --splitting_mode                        input
% 3.13/0.99  --splitting_grd                         true
% 3.13/0.99  --splitting_cvd                         false
% 3.13/0.99  --splitting_cvd_svl                     false
% 3.13/0.99  --splitting_nvd                         32
% 3.13/0.99  --sub_typing                            true
% 3.13/0.99  --prep_gs_sim                           true
% 3.13/0.99  --prep_unflatten                        true
% 3.13/0.99  --prep_res_sim                          true
% 3.13/0.99  --prep_upred                            true
% 3.13/0.99  --prep_sem_filter                       exhaustive
% 3.13/0.99  --prep_sem_filter_out                   false
% 3.13/0.99  --pred_elim                             true
% 3.13/0.99  --res_sim_input                         true
% 3.13/0.99  --eq_ax_congr_red                       true
% 3.13/0.99  --pure_diseq_elim                       true
% 3.13/0.99  --brand_transform                       false
% 3.13/0.99  --non_eq_to_eq                          false
% 3.13/0.99  --prep_def_merge                        true
% 3.13/0.99  --prep_def_merge_prop_impl              false
% 3.13/0.99  --prep_def_merge_mbd                    true
% 3.13/0.99  --prep_def_merge_tr_red                 false
% 3.13/0.99  --prep_def_merge_tr_cl                  false
% 3.13/0.99  --smt_preprocessing                     true
% 3.13/0.99  --smt_ac_axioms                         fast
% 3.13/0.99  --preprocessed_out                      false
% 3.13/0.99  --preprocessed_stats                    false
% 3.13/0.99  
% 3.13/0.99  ------ Abstraction refinement Options
% 3.13/0.99  
% 3.13/0.99  --abstr_ref                             []
% 3.13/0.99  --abstr_ref_prep                        false
% 3.13/0.99  --abstr_ref_until_sat                   false
% 3.13/0.99  --abstr_ref_sig_restrict                funpre
% 3.13/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.13/0.99  --abstr_ref_under                       []
% 3.13/0.99  
% 3.13/0.99  ------ SAT Options
% 3.13/0.99  
% 3.13/0.99  --sat_mode                              false
% 3.13/0.99  --sat_fm_restart_options                ""
% 3.13/0.99  --sat_gr_def                            false
% 3.13/0.99  --sat_epr_types                         true
% 3.13/0.99  --sat_non_cyclic_types                  false
% 3.13/0.99  --sat_finite_models                     false
% 3.13/0.99  --sat_fm_lemmas                         false
% 3.13/0.99  --sat_fm_prep                           false
% 3.13/0.99  --sat_fm_uc_incr                        true
% 3.13/0.99  --sat_out_model                         small
% 3.13/0.99  --sat_out_clauses                       false
% 3.13/0.99  
% 3.13/0.99  ------ QBF Options
% 3.13/0.99  
% 3.13/0.99  --qbf_mode                              false
% 3.13/0.99  --qbf_elim_univ                         false
% 3.13/0.99  --qbf_dom_inst                          none
% 3.13/0.99  --qbf_dom_pre_inst                      false
% 3.13/0.99  --qbf_sk_in                             false
% 3.13/0.99  --qbf_pred_elim                         true
% 3.13/0.99  --qbf_split                             512
% 3.13/0.99  
% 3.13/0.99  ------ BMC1 Options
% 3.13/0.99  
% 3.13/0.99  --bmc1_incremental                      false
% 3.13/0.99  --bmc1_axioms                           reachable_all
% 3.13/0.99  --bmc1_min_bound                        0
% 3.13/0.99  --bmc1_max_bound                        -1
% 3.13/0.99  --bmc1_max_bound_default                -1
% 3.13/0.99  --bmc1_symbol_reachability              true
% 3.13/0.99  --bmc1_property_lemmas                  false
% 3.13/0.99  --bmc1_k_induction                      false
% 3.13/0.99  --bmc1_non_equiv_states                 false
% 3.13/0.99  --bmc1_deadlock                         false
% 3.13/0.99  --bmc1_ucm                              false
% 3.13/0.99  --bmc1_add_unsat_core                   none
% 3.13/0.99  --bmc1_unsat_core_children              false
% 3.13/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.13/0.99  --bmc1_out_stat                         full
% 3.13/0.99  --bmc1_ground_init                      false
% 3.13/0.99  --bmc1_pre_inst_next_state              false
% 3.13/0.99  --bmc1_pre_inst_state                   false
% 3.13/0.99  --bmc1_pre_inst_reach_state             false
% 3.13/0.99  --bmc1_out_unsat_core                   false
% 3.13/0.99  --bmc1_aig_witness_out                  false
% 3.13/0.99  --bmc1_verbose                          false
% 3.13/0.99  --bmc1_dump_clauses_tptp                false
% 3.13/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.13/0.99  --bmc1_dump_file                        -
% 3.13/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.13/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.13/0.99  --bmc1_ucm_extend_mode                  1
% 3.13/0.99  --bmc1_ucm_init_mode                    2
% 3.13/0.99  --bmc1_ucm_cone_mode                    none
% 3.13/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.13/0.99  --bmc1_ucm_relax_model                  4
% 3.13/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.13/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.13/0.99  --bmc1_ucm_layered_model                none
% 3.13/0.99  --bmc1_ucm_max_lemma_size               10
% 3.13/0.99  
% 3.13/0.99  ------ AIG Options
% 3.13/0.99  
% 3.13/0.99  --aig_mode                              false
% 3.13/0.99  
% 3.13/0.99  ------ Instantiation Options
% 3.13/0.99  
% 3.13/0.99  --instantiation_flag                    true
% 3.13/0.99  --inst_sos_flag                         false
% 3.13/0.99  --inst_sos_phase                        true
% 3.13/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.13/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.13/0.99  --inst_lit_sel_side                     num_symb
% 3.13/0.99  --inst_solver_per_active                1400
% 3.13/0.99  --inst_solver_calls_frac                1.
% 3.13/0.99  --inst_passive_queue_type               priority_queues
% 3.13/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.13/0.99  --inst_passive_queues_freq              [25;2]
% 3.13/0.99  --inst_dismatching                      true
% 3.13/0.99  --inst_eager_unprocessed_to_passive     true
% 3.13/0.99  --inst_prop_sim_given                   true
% 3.13/0.99  --inst_prop_sim_new                     false
% 3.13/0.99  --inst_subs_new                         false
% 3.13/0.99  --inst_eq_res_simp                      false
% 3.13/0.99  --inst_subs_given                       false
% 3.13/0.99  --inst_orphan_elimination               true
% 3.13/0.99  --inst_learning_loop_flag               true
% 3.13/0.99  --inst_learning_start                   3000
% 3.13/0.99  --inst_learning_factor                  2
% 3.13/0.99  --inst_start_prop_sim_after_learn       3
% 3.13/0.99  --inst_sel_renew                        solver
% 3.13/0.99  --inst_lit_activity_flag                true
% 3.13/0.99  --inst_restr_to_given                   false
% 3.13/0.99  --inst_activity_threshold               500
% 3.13/0.99  --inst_out_proof                        true
% 3.13/0.99  
% 3.13/0.99  ------ Resolution Options
% 3.13/0.99  
% 3.13/0.99  --resolution_flag                       true
% 3.13/0.99  --res_lit_sel                           adaptive
% 3.13/0.99  --res_lit_sel_side                      none
% 3.13/0.99  --res_ordering                          kbo
% 3.13/0.99  --res_to_prop_solver                    active
% 3.13/0.99  --res_prop_simpl_new                    false
% 3.13/0.99  --res_prop_simpl_given                  true
% 3.13/0.99  --res_passive_queue_type                priority_queues
% 3.13/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.13/0.99  --res_passive_queues_freq               [15;5]
% 3.13/0.99  --res_forward_subs                      full
% 3.13/0.99  --res_backward_subs                     full
% 3.13/0.99  --res_forward_subs_resolution           true
% 3.13/0.99  --res_backward_subs_resolution          true
% 3.13/0.99  --res_orphan_elimination                true
% 3.13/0.99  --res_time_limit                        2.
% 3.13/0.99  --res_out_proof                         true
% 3.13/0.99  
% 3.13/0.99  ------ Superposition Options
% 3.13/0.99  
% 3.13/0.99  --superposition_flag                    true
% 3.13/0.99  --sup_passive_queue_type                priority_queues
% 3.13/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.13/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.13/0.99  --demod_completeness_check              fast
% 3.13/0.99  --demod_use_ground                      true
% 3.13/0.99  --sup_to_prop_solver                    passive
% 3.13/0.99  --sup_prop_simpl_new                    true
% 3.13/0.99  --sup_prop_simpl_given                  true
% 3.13/0.99  --sup_fun_splitting                     false
% 3.13/0.99  --sup_smt_interval                      50000
% 3.13/0.99  
% 3.13/0.99  ------ Superposition Simplification Setup
% 3.13/0.99  
% 3.13/0.99  --sup_indices_passive                   []
% 3.13/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.13/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.13/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.13/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.13/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.13/0.99  --sup_full_bw                           [BwDemod]
% 3.13/0.99  --sup_immed_triv                        [TrivRules]
% 3.13/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.13/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.13/0.99  --sup_immed_bw_main                     []
% 3.13/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.13/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.13/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.13/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.13/0.99  
% 3.13/0.99  ------ Combination Options
% 3.13/0.99  
% 3.13/0.99  --comb_res_mult                         3
% 3.13/0.99  --comb_sup_mult                         2
% 3.13/0.99  --comb_inst_mult                        10
% 3.13/0.99  
% 3.13/0.99  ------ Debug Options
% 3.13/0.99  
% 3.13/0.99  --dbg_backtrace                         false
% 3.13/0.99  --dbg_dump_prop_clauses                 false
% 3.13/0.99  --dbg_dump_prop_clauses_file            -
% 3.13/0.99  --dbg_out_stat                          false
% 3.13/0.99  ------ Parsing...
% 3.13/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.13/0.99  
% 3.13/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.13/0.99  
% 3.13/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.13/0.99  
% 3.13/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.13/0.99  ------ Proving...
% 3.13/0.99  ------ Problem Properties 
% 3.13/0.99  
% 3.13/0.99  
% 3.13/0.99  clauses                                 10
% 3.13/0.99  conjectures                             2
% 3.13/0.99  EPR                                     1
% 3.13/0.99  Horn                                    10
% 3.13/0.99  unary                                   10
% 3.13/0.99  binary                                  0
% 3.13/0.99  lits                                    10
% 3.13/0.99  lits eq                                 10
% 3.13/0.99  fd_pure                                 0
% 3.13/0.99  fd_pseudo                               0
% 3.13/0.99  fd_cond                                 0
% 3.13/0.99  fd_pseudo_cond                          0
% 3.13/0.99  AC symbols                              0
% 3.13/0.99  
% 3.13/0.99  ------ Schedule UEQ
% 3.13/0.99  
% 3.13/0.99  ------ pure equality problem: resolution off 
% 3.13/0.99  
% 3.13/0.99  ------ Option_UEQ Time Limit: Unbounded
% 3.13/0.99  
% 3.13/0.99  
% 3.13/0.99  ------ 
% 3.13/0.99  Current options:
% 3.13/0.99  ------ 
% 3.13/0.99  
% 3.13/0.99  ------ Input Options
% 3.13/0.99  
% 3.13/0.99  --out_options                           all
% 3.13/0.99  --tptp_safe_out                         true
% 3.13/0.99  --problem_path                          ""
% 3.13/0.99  --include_path                          ""
% 3.13/0.99  --clausifier                            res/vclausify_rel
% 3.13/0.99  --clausifier_options                    --mode clausify
% 3.13/0.99  --stdin                                 false
% 3.13/0.99  --stats_out                             all
% 3.13/0.99  
% 3.13/0.99  ------ General Options
% 3.13/0.99  
% 3.13/0.99  --fof                                   false
% 3.13/0.99  --time_out_real                         305.
% 3.13/0.99  --time_out_virtual                      -1.
% 3.13/0.99  --symbol_type_check                     false
% 3.13/0.99  --clausify_out                          false
% 3.13/0.99  --sig_cnt_out                           false
% 3.13/0.99  --trig_cnt_out                          false
% 3.13/0.99  --trig_cnt_out_tolerance                1.
% 3.13/0.99  --trig_cnt_out_sk_spl                   false
% 3.13/0.99  --abstr_cl_out                          false
% 3.13/0.99  
% 3.13/0.99  ------ Global Options
% 3.13/0.99  
% 3.13/0.99  --schedule                              default
% 3.13/0.99  --add_important_lit                     false
% 3.13/0.99  --prop_solver_per_cl                    1000
% 3.13/0.99  --min_unsat_core                        false
% 3.13/0.99  --soft_assumptions                      false
% 3.13/0.99  --soft_lemma_size                       3
% 3.13/0.99  --prop_impl_unit_size                   0
% 3.13/0.99  --prop_impl_unit                        []
% 3.13/0.99  --share_sel_clauses                     true
% 3.13/0.99  --reset_solvers                         false
% 3.13/0.99  --bc_imp_inh                            [conj_cone]
% 3.13/0.99  --conj_cone_tolerance                   3.
% 3.13/0.99  --extra_neg_conj                        none
% 3.13/0.99  --large_theory_mode                     true
% 3.13/0.99  --prolific_symb_bound                   200
% 3.13/0.99  --lt_threshold                          2000
% 3.13/0.99  --clause_weak_htbl                      true
% 3.13/0.99  --gc_record_bc_elim                     false
% 3.13/0.99  
% 3.13/0.99  ------ Preprocessing Options
% 3.13/0.99  
% 3.13/0.99  --preprocessing_flag                    true
% 3.13/0.99  --time_out_prep_mult                    0.1
% 3.13/0.99  --splitting_mode                        input
% 3.13/0.99  --splitting_grd                         true
% 3.13/0.99  --splitting_cvd                         false
% 3.13/0.99  --splitting_cvd_svl                     false
% 3.13/0.99  --splitting_nvd                         32
% 3.13/0.99  --sub_typing                            true
% 3.13/0.99  --prep_gs_sim                           true
% 3.13/0.99  --prep_unflatten                        true
% 3.13/0.99  --prep_res_sim                          true
% 3.13/0.99  --prep_upred                            true
% 3.13/0.99  --prep_sem_filter                       exhaustive
% 3.13/0.99  --prep_sem_filter_out                   false
% 3.13/0.99  --pred_elim                             true
% 3.13/0.99  --res_sim_input                         true
% 3.13/0.99  --eq_ax_congr_red                       true
% 3.13/0.99  --pure_diseq_elim                       true
% 3.13/0.99  --brand_transform                       false
% 3.13/0.99  --non_eq_to_eq                          false
% 3.13/0.99  --prep_def_merge                        true
% 3.13/0.99  --prep_def_merge_prop_impl              false
% 3.13/0.99  --prep_def_merge_mbd                    true
% 3.13/0.99  --prep_def_merge_tr_red                 false
% 3.13/0.99  --prep_def_merge_tr_cl                  false
% 3.13/0.99  --smt_preprocessing                     true
% 3.13/0.99  --smt_ac_axioms                         fast
% 3.13/0.99  --preprocessed_out                      false
% 3.13/0.99  --preprocessed_stats                    false
% 3.13/0.99  
% 3.13/0.99  ------ Abstraction refinement Options
% 3.13/0.99  
% 3.13/0.99  --abstr_ref                             []
% 3.13/0.99  --abstr_ref_prep                        false
% 3.13/0.99  --abstr_ref_until_sat                   false
% 3.13/0.99  --abstr_ref_sig_restrict                funpre
% 3.13/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.13/0.99  --abstr_ref_under                       []
% 3.13/0.99  
% 3.13/0.99  ------ SAT Options
% 3.13/0.99  
% 3.13/0.99  --sat_mode                              false
% 3.13/0.99  --sat_fm_restart_options                ""
% 3.13/0.99  --sat_gr_def                            false
% 3.13/0.99  --sat_epr_types                         true
% 3.13/0.99  --sat_non_cyclic_types                  false
% 3.13/0.99  --sat_finite_models                     false
% 3.13/0.99  --sat_fm_lemmas                         false
% 3.13/0.99  --sat_fm_prep                           false
% 3.13/0.99  --sat_fm_uc_incr                        true
% 3.13/0.99  --sat_out_model                         small
% 3.13/0.99  --sat_out_clauses                       false
% 3.13/0.99  
% 3.13/0.99  ------ QBF Options
% 3.13/0.99  
% 3.13/0.99  --qbf_mode                              false
% 3.13/0.99  --qbf_elim_univ                         false
% 3.13/0.99  --qbf_dom_inst                          none
% 3.13/0.99  --qbf_dom_pre_inst                      false
% 3.13/0.99  --qbf_sk_in                             false
% 3.13/0.99  --qbf_pred_elim                         true
% 3.13/0.99  --qbf_split                             512
% 3.13/0.99  
% 3.13/0.99  ------ BMC1 Options
% 3.13/0.99  
% 3.13/0.99  --bmc1_incremental                      false
% 3.13/0.99  --bmc1_axioms                           reachable_all
% 3.13/0.99  --bmc1_min_bound                        0
% 3.13/0.99  --bmc1_max_bound                        -1
% 3.13/0.99  --bmc1_max_bound_default                -1
% 3.13/0.99  --bmc1_symbol_reachability              true
% 3.13/0.99  --bmc1_property_lemmas                  false
% 3.13/0.99  --bmc1_k_induction                      false
% 3.13/0.99  --bmc1_non_equiv_states                 false
% 3.13/0.99  --bmc1_deadlock                         false
% 3.13/0.99  --bmc1_ucm                              false
% 3.13/0.99  --bmc1_add_unsat_core                   none
% 3.13/0.99  --bmc1_unsat_core_children              false
% 3.13/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.13/0.99  --bmc1_out_stat                         full
% 3.13/0.99  --bmc1_ground_init                      false
% 3.13/0.99  --bmc1_pre_inst_next_state              false
% 3.13/0.99  --bmc1_pre_inst_state                   false
% 3.13/0.99  --bmc1_pre_inst_reach_state             false
% 3.13/0.99  --bmc1_out_unsat_core                   false
% 3.13/0.99  --bmc1_aig_witness_out                  false
% 3.13/0.99  --bmc1_verbose                          false
% 3.13/0.99  --bmc1_dump_clauses_tptp                false
% 3.13/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.13/0.99  --bmc1_dump_file                        -
% 3.13/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.13/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.13/0.99  --bmc1_ucm_extend_mode                  1
% 3.13/0.99  --bmc1_ucm_init_mode                    2
% 3.13/0.99  --bmc1_ucm_cone_mode                    none
% 3.13/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.13/0.99  --bmc1_ucm_relax_model                  4
% 3.13/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.13/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.13/0.99  --bmc1_ucm_layered_model                none
% 3.13/0.99  --bmc1_ucm_max_lemma_size               10
% 3.13/0.99  
% 3.13/0.99  ------ AIG Options
% 3.13/0.99  
% 3.13/0.99  --aig_mode                              false
% 3.13/0.99  
% 3.13/0.99  ------ Instantiation Options
% 3.13/0.99  
% 3.13/0.99  --instantiation_flag                    false
% 3.13/0.99  --inst_sos_flag                         false
% 3.13/0.99  --inst_sos_phase                        true
% 3.13/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.13/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.13/0.99  --inst_lit_sel_side                     num_symb
% 3.13/0.99  --inst_solver_per_active                1400
% 3.13/0.99  --inst_solver_calls_frac                1.
% 3.13/0.99  --inst_passive_queue_type               priority_queues
% 3.13/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.13/0.99  --inst_passive_queues_freq              [25;2]
% 3.13/0.99  --inst_dismatching                      true
% 3.13/0.99  --inst_eager_unprocessed_to_passive     true
% 3.13/0.99  --inst_prop_sim_given                   true
% 3.13/0.99  --inst_prop_sim_new                     false
% 3.13/0.99  --inst_subs_new                         false
% 3.13/0.99  --inst_eq_res_simp                      false
% 3.13/0.99  --inst_subs_given                       false
% 3.13/0.99  --inst_orphan_elimination               true
% 3.13/0.99  --inst_learning_loop_flag               true
% 3.13/0.99  --inst_learning_start                   3000
% 3.13/0.99  --inst_learning_factor                  2
% 3.13/0.99  --inst_start_prop_sim_after_learn       3
% 3.13/0.99  --inst_sel_renew                        solver
% 3.13/0.99  --inst_lit_activity_flag                true
% 3.13/0.99  --inst_restr_to_given                   false
% 3.13/0.99  --inst_activity_threshold               500
% 3.13/0.99  --inst_out_proof                        true
% 3.13/0.99  
% 3.13/0.99  ------ Resolution Options
% 3.13/0.99  
% 3.13/0.99  --resolution_flag                       false
% 3.13/0.99  --res_lit_sel                           adaptive
% 3.13/0.99  --res_lit_sel_side                      none
% 3.13/0.99  --res_ordering                          kbo
% 3.13/0.99  --res_to_prop_solver                    active
% 3.13/0.99  --res_prop_simpl_new                    false
% 3.13/0.99  --res_prop_simpl_given                  true
% 3.13/0.99  --res_passive_queue_type                priority_queues
% 3.13/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.13/0.99  --res_passive_queues_freq               [15;5]
% 3.13/0.99  --res_forward_subs                      full
% 3.13/0.99  --res_backward_subs                     full
% 3.13/0.99  --res_forward_subs_resolution           true
% 3.13/0.99  --res_backward_subs_resolution          true
% 3.13/0.99  --res_orphan_elimination                true
% 3.13/0.99  --res_time_limit                        2.
% 3.13/0.99  --res_out_proof                         true
% 3.13/0.99  
% 3.13/0.99  ------ Superposition Options
% 3.13/0.99  
% 3.13/0.99  --superposition_flag                    true
% 3.13/0.99  --sup_passive_queue_type                priority_queues
% 3.13/0.99  --sup_passive_queues                    [[-conj_dist;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.13/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.13/0.99  --demod_completeness_check              fast
% 3.13/0.99  --demod_use_ground                      true
% 3.13/0.99  --sup_to_prop_solver                    active
% 3.13/0.99  --sup_prop_simpl_new                    false
% 3.13/0.99  --sup_prop_simpl_given                  false
% 3.13/0.99  --sup_fun_splitting                     true
% 3.13/0.99  --sup_smt_interval                      10000
% 3.13/0.99  
% 3.13/0.99  ------ Superposition Simplification Setup
% 3.13/0.99  
% 3.13/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.13/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.13/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.13/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.13/0.99  --sup_full_triv                         [TrivRules]
% 3.13/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.13/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.13/0.99  --sup_immed_triv                        [TrivRules]
% 3.13/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.13/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.13/0.99  --sup_immed_bw_main                     []
% 3.13/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.13/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.13/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.13/0.99  --sup_input_bw                          [BwDemod;BwSubsumption]
% 3.13/0.99  
% 3.13/0.99  ------ Combination Options
% 3.13/0.99  
% 3.13/0.99  --comb_res_mult                         1
% 3.13/0.99  --comb_sup_mult                         1
% 3.13/0.99  --comb_inst_mult                        1000000
% 3.13/0.99  
% 3.13/0.99  ------ Debug Options
% 3.13/0.99  
% 3.13/0.99  --dbg_backtrace                         false
% 3.13/0.99  --dbg_dump_prop_clauses                 false
% 3.13/0.99  --dbg_dump_prop_clauses_file            -
% 3.13/0.99  --dbg_out_stat                          false
% 3.13/0.99  
% 3.13/0.99  
% 3.13/0.99  
% 3.13/0.99  
% 3.13/0.99  ------ Proving...
% 3.13/0.99  
% 3.13/0.99  
% 3.13/0.99  % SZS status Theorem for theBenchmark.p
% 3.13/0.99  
% 3.13/0.99   Resolution empty clause
% 3.13/0.99  
% 3.13/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.13/0.99  
% 3.13/0.99  fof(f1,axiom,(
% 3.13/0.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 3.13/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.13/0.99  
% 3.13/0.99  fof(f17,plain,(
% 3.13/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 3.13/0.99    inference(cnf_transformation,[],[f1])).
% 3.13/0.99  
% 3.13/0.99  fof(f3,axiom,(
% 3.13/0.99    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 3.13/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.13/0.99  
% 3.13/0.99  fof(f11,plain,(
% 3.13/0.99    ! [X0,X1] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,X1) = k1_xboole_0)),
% 3.13/0.99    inference(unused_predicate_definition_removal,[],[f3])).
% 3.13/0.99  
% 3.13/0.99  fof(f12,plain,(
% 3.13/0.99    ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1))),
% 3.13/0.99    inference(ennf_transformation,[],[f11])).
% 3.13/0.99  
% 3.13/0.99  fof(f19,plain,(
% 3.13/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 3.13/0.99    inference(cnf_transformation,[],[f12])).
% 3.13/0.99  
% 3.13/0.99  fof(f8,axiom,(
% 3.13/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.13/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.13/0.99  
% 3.13/0.99  fof(f24,plain,(
% 3.13/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.13/0.99    inference(cnf_transformation,[],[f8])).
% 3.13/0.99  
% 3.13/0.99  fof(f30,plain,(
% 3.13/0.99    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 3.13/0.99    inference(definition_unfolding,[],[f19,f24])).
% 3.13/0.99  
% 3.13/0.99  fof(f9,conjecture,(
% 3.13/0.99    ! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 3.13/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.13/0.99  
% 3.13/0.99  fof(f10,negated_conjecture,(
% 3.13/0.99    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 3.13/0.99    inference(negated_conjecture,[],[f9])).
% 3.13/0.99  
% 3.13/0.99  fof(f13,plain,(
% 3.13/0.99    ? [X0,X1,X2,X3] : (X1 != X2 & (r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)))),
% 3.13/0.99    inference(ennf_transformation,[],[f10])).
% 3.13/0.99  
% 3.13/0.99  fof(f14,plain,(
% 3.13/0.99    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3))),
% 3.13/0.99    inference(flattening,[],[f13])).
% 3.13/0.99  
% 3.13/0.99  fof(f15,plain,(
% 3.13/0.99    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => (sK1 != sK2 & r1_xboole_0(sK3,sK1) & r1_xboole_0(sK2,sK0) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3))),
% 3.13/0.99    introduced(choice_axiom,[])).
% 3.13/0.99  
% 3.13/0.99  fof(f16,plain,(
% 3.13/0.99    sK1 != sK2 & r1_xboole_0(sK3,sK1) & r1_xboole_0(sK2,sK0) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 3.13/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f14,f15])).
% 3.13/0.99  
% 3.13/0.99  fof(f26,plain,(
% 3.13/0.99    r1_xboole_0(sK2,sK0)),
% 3.13/0.99    inference(cnf_transformation,[],[f16])).
% 3.13/0.99  
% 3.13/0.99  fof(f7,axiom,(
% 3.13/0.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.13/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.13/0.99  
% 3.13/0.99  fof(f23,plain,(
% 3.13/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.13/0.99    inference(cnf_transformation,[],[f7])).
% 3.13/0.99  
% 3.13/0.99  fof(f31,plain,(
% 3.13/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 3.13/0.99    inference(definition_unfolding,[],[f23,f24])).
% 3.13/0.99  
% 3.13/0.99  fof(f4,axiom,(
% 3.13/0.99    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 3.13/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.13/0.99  
% 3.13/0.99  fof(f20,plain,(
% 3.13/0.99    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.13/0.99    inference(cnf_transformation,[],[f4])).
% 3.13/0.99  
% 3.13/0.99  fof(f6,axiom,(
% 3.13/0.99    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 3.13/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.13/0.99  
% 3.13/0.99  fof(f22,plain,(
% 3.13/0.99    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 3.13/0.99    inference(cnf_transformation,[],[f6])).
% 3.13/0.99  
% 3.13/0.99  fof(f27,plain,(
% 3.13/0.99    r1_xboole_0(sK3,sK1)),
% 3.13/0.99    inference(cnf_transformation,[],[f16])).
% 3.13/0.99  
% 3.13/0.99  fof(f2,axiom,(
% 3.13/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.13/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.13/0.99  
% 3.13/0.99  fof(f18,plain,(
% 3.13/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.13/0.99    inference(cnf_transformation,[],[f2])).
% 3.13/0.99  
% 3.13/0.99  fof(f29,plain,(
% 3.13/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 3.13/0.99    inference(definition_unfolding,[],[f18,f24,f24])).
% 3.13/0.99  
% 3.13/0.99  fof(f25,plain,(
% 3.13/0.99    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 3.13/0.99    inference(cnf_transformation,[],[f16])).
% 3.13/0.99  
% 3.13/0.99  fof(f5,axiom,(
% 3.13/0.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 3.13/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.13/0.99  
% 3.13/0.99  fof(f21,plain,(
% 3.13/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 3.13/0.99    inference(cnf_transformation,[],[f5])).
% 3.13/0.99  
% 3.13/0.99  fof(f28,plain,(
% 3.13/0.99    sK1 != sK2),
% 3.13/0.99    inference(cnf_transformation,[],[f16])).
% 3.13/0.99  
% 3.13/0.99  cnf(c_0,plain,
% 3.13/0.99      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 3.13/0.99      inference(cnf_transformation,[],[f17]) ).
% 3.13/0.99  
% 3.13/0.99  cnf(c_2,plain,
% 3.13/0.99      ( ~ r1_xboole_0(X0,X1)
% 3.13/0.99      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 3.13/0.99      inference(cnf_transformation,[],[f30]) ).
% 3.13/0.99  
% 3.13/0.99  cnf(c_9,negated_conjecture,
% 3.13/0.99      ( r1_xboole_0(sK2,sK0) ),
% 3.13/0.99      inference(cnf_transformation,[],[f26]) ).
% 3.13/0.99  
% 3.13/0.99  cnf(c_55,plain,
% 3.13/0.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
% 3.13/0.99      | sK0 != X1
% 3.13/0.99      | sK2 != X0 ),
% 3.13/0.99      inference(resolution_lifted,[status(thm)],[c_2,c_9]) ).
% 3.13/0.99  
% 3.13/0.99  cnf(c_56,plain,
% 3.13/0.99      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) = k1_xboole_0 ),
% 3.13/0.99      inference(unflattening,[status(thm)],[c_55]) ).
% 3.13/0.99  
% 3.13/0.99  cnf(c_6,plain,
% 3.13/0.99      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 3.13/0.99      inference(cnf_transformation,[],[f31]) ).
% 3.13/0.99  
% 3.13/0.99  cnf(c_127,plain,
% 3.13/0.99      ( k4_xboole_0(sK2,k1_xboole_0) = k4_xboole_0(sK2,sK0) ),
% 3.13/0.99      inference(superposition,[status(thm)],[c_56,c_6]) ).
% 3.13/0.99  
% 3.13/0.99  cnf(c_3,plain,
% 3.13/0.99      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.13/0.99      inference(cnf_transformation,[],[f20]) ).
% 3.13/0.99  
% 3.13/0.99  cnf(c_152,plain,
% 3.13/0.99      ( k4_xboole_0(sK2,sK0) = sK2 ),
% 3.13/0.99      inference(demodulation,[status(thm)],[c_127,c_3]) ).
% 3.13/0.99  
% 3.13/0.99  cnf(c_5,plain,
% 3.13/0.99      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 3.13/0.99      inference(cnf_transformation,[],[f22]) ).
% 3.13/0.99  
% 3.13/0.99  cnf(c_212,plain,
% 3.13/0.99      ( k4_xboole_0(sK2,k2_xboole_0(sK0,X0)) = k4_xboole_0(sK2,X0) ),
% 3.13/0.99      inference(superposition,[status(thm)],[c_152,c_5]) ).
% 3.13/0.99  
% 3.13/0.99  cnf(c_375,plain,
% 3.13/0.99      ( k4_xboole_0(sK2,k2_xboole_0(X0,sK0)) = k4_xboole_0(sK2,X0) ),
% 3.13/0.99      inference(superposition,[status(thm)],[c_0,c_212]) ).
% 3.13/0.99  
% 3.13/0.99  cnf(c_8,negated_conjecture,
% 3.13/0.99      ( r1_xboole_0(sK3,sK1) ),
% 3.13/0.99      inference(cnf_transformation,[],[f27]) ).
% 3.13/0.99  
% 3.13/0.99  cnf(c_50,plain,
% 3.13/0.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
% 3.13/0.99      | sK3 != X0
% 3.13/0.99      | sK1 != X1 ),
% 3.13/0.99      inference(resolution_lifted,[status(thm)],[c_2,c_8]) ).
% 3.13/0.99  
% 3.13/0.99  cnf(c_51,plain,
% 3.13/0.99      ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)) = k1_xboole_0 ),
% 3.13/0.99      inference(unflattening,[status(thm)],[c_50]) ).
% 3.13/0.99  
% 3.13/0.99  cnf(c_133,plain,
% 3.13/0.99      ( k4_xboole_0(sK3,k4_xboole_0(sK3,k1_xboole_0)) = k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)) ),
% 3.13/0.99      inference(superposition,[status(thm)],[c_51,c_6]) ).
% 3.13/0.99  
% 3.13/0.99  cnf(c_146,plain,
% 3.13/0.99      ( k4_xboole_0(sK3,k4_xboole_0(sK3,k1_xboole_0)) = k1_xboole_0 ),
% 3.13/0.99      inference(light_normalisation,[status(thm)],[c_133,c_51]) ).
% 3.13/0.99  
% 3.13/0.99  cnf(c_147,plain,
% 3.13/0.99      ( k4_xboole_0(sK3,sK3) = k1_xboole_0 ),
% 3.13/0.99      inference(demodulation,[status(thm)],[c_146,c_3]) ).
% 3.13/0.99  
% 3.13/0.99  cnf(c_1,plain,
% 3.13/0.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 3.13/0.99      inference(cnf_transformation,[],[f29]) ).
% 3.13/0.99  
% 3.13/0.99  cnf(c_91,plain,
% 3.13/0.99      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(X0,X0) ),
% 3.13/0.99      inference(superposition,[status(thm)],[c_3,c_1]) ).
% 3.13/0.99  
% 3.13/0.99  cnf(c_249,plain,
% 3.13/0.99      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X0)) = k4_xboole_0(k1_xboole_0,X0) ),
% 3.13/0.99      inference(superposition,[status(thm)],[c_91,c_6]) ).
% 3.13/0.99  
% 3.13/0.99  cnf(c_532,plain,
% 3.13/0.99      ( k4_xboole_0(k1_xboole_0,sK3) = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 3.13/0.99      inference(superposition,[status(thm)],[c_147,c_249]) ).
% 3.13/0.99  
% 3.13/0.99  cnf(c_541,plain,
% 3.13/0.99      ( k4_xboole_0(k1_xboole_0,sK3) = k1_xboole_0 ),
% 3.13/0.99      inference(demodulation,[status(thm)],[c_532,c_3]) ).
% 3.13/0.99  
% 3.13/0.99  cnf(c_10,negated_conjecture,
% 3.13/0.99      ( k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
% 3.13/0.99      inference(cnf_transformation,[],[f25]) ).
% 3.13/0.99  
% 3.13/0.99  cnf(c_72,plain,
% 3.13/0.99      ( k2_xboole_0(sK1,sK0) = k2_xboole_0(sK2,sK3) ),
% 3.13/0.99      inference(demodulation,[status(thm)],[c_0,c_10]) ).
% 3.13/0.99  
% 3.13/0.99  cnf(c_106,plain,
% 3.13/0.99      ( k4_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK2,sK0),X0)) = k4_xboole_0(k1_xboole_0,X0) ),
% 3.13/0.99      inference(superposition,[status(thm)],[c_56,c_5]) ).
% 3.13/0.99  
% 3.13/0.99  cnf(c_187,plain,
% 3.13/0.99      ( k4_xboole_0(sK2,k2_xboole_0(sK2,X0)) = k4_xboole_0(k1_xboole_0,X0) ),
% 3.13/0.99      inference(light_normalisation,[status(thm)],[c_106,c_106,c_152]) ).
% 3.13/0.99  
% 3.13/0.99  cnf(c_191,plain,
% 3.13/0.99      ( k4_xboole_0(sK2,k2_xboole_0(sK1,sK0)) = k4_xboole_0(k1_xboole_0,sK3) ),
% 3.13/0.99      inference(superposition,[status(thm)],[c_72,c_187]) ).
% 3.13/0.99  
% 3.13/0.99  cnf(c_787,plain,
% 3.13/0.99      ( k4_xboole_0(sK2,k2_xboole_0(sK1,sK0)) = k1_xboole_0 ),
% 3.13/0.99      inference(demodulation,[status(thm)],[c_541,c_191]) ).
% 3.13/0.99  
% 3.13/0.99  cnf(c_2009,plain,
% 3.13/0.99      ( k4_xboole_0(sK2,sK1) = k1_xboole_0 ),
% 3.13/0.99      inference(superposition,[status(thm)],[c_375,c_787]) ).
% 3.13/0.99  
% 3.13/0.99  cnf(c_4,plain,
% 3.13/0.99      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
% 3.13/0.99      inference(cnf_transformation,[],[f21]) ).
% 3.13/0.99  
% 3.13/0.99  cnf(c_92,plain,
% 3.13/0.99      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X0,X1))) ),
% 3.13/0.99      inference(superposition,[status(thm)],[c_4,c_1]) ).
% 3.13/0.99  
% 3.13/0.99  cnf(c_2065,plain,
% 3.13/0.99      ( k4_xboole_0(sK1,k4_xboole_0(sK1,k2_xboole_0(sK2,sK1))) = k4_xboole_0(k2_xboole_0(sK2,sK1),k1_xboole_0) ),
% 3.13/0.99      inference(superposition,[status(thm)],[c_2009,c_92]) ).
% 3.13/0.99  
% 3.13/0.99  cnf(c_95,plain,
% 3.13/0.99      ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) = k1_xboole_0 ),
% 3.13/0.99      inference(superposition,[status(thm)],[c_1,c_51]) ).
% 3.13/0.99  
% 3.13/0.99  cnf(c_163,plain,
% 3.13/0.99      ( k4_xboole_0(sK1,k2_xboole_0(k4_xboole_0(sK1,sK3),X0)) = k4_xboole_0(k1_xboole_0,X0) ),
% 3.13/0.99      inference(superposition,[status(thm)],[c_95,c_5]) ).
% 3.13/0.99  
% 3.13/0.99  cnf(c_164,plain,
% 3.13/0.99      ( k4_xboole_0(sK1,sK3) = k4_xboole_0(sK1,k1_xboole_0) ),
% 3.13/0.99      inference(superposition,[status(thm)],[c_95,c_6]) ).
% 3.13/0.99  
% 3.13/0.99  cnf(c_165,plain,
% 3.13/0.99      ( k4_xboole_0(sK1,sK3) = sK1 ),
% 3.13/0.99      inference(demodulation,[status(thm)],[c_164,c_3]) ).
% 3.13/0.99  
% 3.13/0.99  cnf(c_174,plain,
% 3.13/0.99      ( k4_xboole_0(sK1,k2_xboole_0(sK1,X0)) = k4_xboole_0(k1_xboole_0,X0) ),
% 3.13/0.99      inference(light_normalisation,[status(thm)],[c_163,c_165]) ).
% 3.13/0.99  
% 3.13/0.99  cnf(c_290,plain,
% 3.13/0.99      ( k4_xboole_0(sK1,k2_xboole_0(X0,sK1)) = k4_xboole_0(k1_xboole_0,X0) ),
% 3.13/0.99      inference(superposition,[status(thm)],[c_0,c_174]) ).
% 3.13/0.99  
% 3.13/0.99  cnf(c_2079,plain,
% 3.13/0.99      ( k4_xboole_0(sK1,k4_xboole_0(k1_xboole_0,sK2)) = k2_xboole_0(sK2,sK1) ),
% 3.13/0.99      inference(demodulation,[status(thm)],[c_2065,c_3,c_290]) ).
% 3.13/0.99  
% 3.13/0.99  cnf(c_134,plain,
% 3.13/0.99      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k1_xboole_0)) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) ),
% 3.13/0.99      inference(superposition,[status(thm)],[c_56,c_6]) ).
% 3.13/0.99  
% 3.13/0.99  cnf(c_144,plain,
% 3.13/0.99      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k1_xboole_0)) = k1_xboole_0 ),
% 3.13/0.99      inference(light_normalisation,[status(thm)],[c_134,c_56]) ).
% 3.13/0.99  
% 3.13/0.99  cnf(c_145,plain,
% 3.13/0.99      ( k4_xboole_0(sK2,sK2) = k1_xboole_0 ),
% 3.13/0.99      inference(demodulation,[status(thm)],[c_144,c_3]) ).
% 3.13/0.99  
% 3.13/0.99  cnf(c_531,plain,
% 3.13/0.99      ( k4_xboole_0(k1_xboole_0,sK2) = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 3.13/0.99      inference(superposition,[status(thm)],[c_145,c_249]) ).
% 3.13/0.99  
% 3.13/0.99  cnf(c_542,plain,
% 3.13/0.99      ( k4_xboole_0(k1_xboole_0,sK2) = k1_xboole_0 ),
% 3.13/0.99      inference(demodulation,[status(thm)],[c_531,c_3]) ).
% 3.13/0.99  
% 3.13/0.99  cnf(c_2080,plain,
% 3.13/0.99      ( k4_xboole_0(sK1,k1_xboole_0) = k2_xboole_0(sK2,sK1) ),
% 3.13/0.99      inference(light_normalisation,[status(thm)],[c_2079,c_542]) ).
% 3.13/0.99  
% 3.13/0.99  cnf(c_2081,plain,
% 3.13/0.99      ( k2_xboole_0(sK2,sK1) = sK1 ),
% 3.13/0.99      inference(demodulation,[status(thm)],[c_2080,c_3]) ).
% 3.13/0.99  
% 3.13/0.99  cnf(c_74,plain,
% 3.13/0.99      ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(X1,X0) ),
% 3.13/0.99      inference(superposition,[status(thm)],[c_0,c_4]) ).
% 3.13/0.99  
% 3.13/0.99  cnf(c_82,plain,
% 3.13/0.99      ( k4_xboole_0(k2_xboole_0(sK1,sK0),sK2) = k4_xboole_0(sK3,sK2) ),
% 3.13/0.99      inference(superposition,[status(thm)],[c_72,c_74]) ).
% 3.13/0.99  
% 3.13/0.99  cnf(c_168,plain,
% 3.13/0.99      ( k4_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK2,X0)) = k4_xboole_0(k4_xboole_0(sK3,sK2),X0) ),
% 3.13/0.99      inference(superposition,[status(thm)],[c_82,c_5]) ).
% 3.13/0.99  
% 3.13/0.99  cnf(c_171,plain,
% 3.13/0.99      ( k4_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK2,X0)) = k4_xboole_0(sK3,k2_xboole_0(sK2,X0)) ),
% 3.13/0.99      inference(demodulation,[status(thm)],[c_168,c_5]) ).
% 3.13/0.99  
% 3.13/0.99  cnf(c_2510,plain,
% 3.13/0.99      ( k4_xboole_0(k2_xboole_0(sK1,sK0),sK1) = k4_xboole_0(sK3,k2_xboole_0(sK2,sK1)) ),
% 3.13/0.99      inference(superposition,[status(thm)],[c_2081,c_171]) ).
% 3.13/0.99  
% 3.13/0.99  cnf(c_2513,plain,
% 3.13/0.99      ( k4_xboole_0(k2_xboole_0(sK1,sK0),sK1) = k4_xboole_0(sK3,sK1) ),
% 3.13/0.99      inference(demodulation,[status(thm)],[c_2510,c_2081]) ).
% 3.13/0.99  
% 3.13/0.99  cnf(c_126,plain,
% 3.13/0.99      ( k4_xboole_0(sK3,k1_xboole_0) = k4_xboole_0(sK3,sK1) ),
% 3.13/0.99      inference(superposition,[status(thm)],[c_51,c_6]) ).
% 3.13/0.99  
% 3.13/0.99  cnf(c_153,plain,
% 3.13/0.99      ( k4_xboole_0(sK3,sK1) = sK3 ),
% 3.13/0.99      inference(demodulation,[status(thm)],[c_126,c_3]) ).
% 3.13/0.99  
% 3.13/0.99  cnf(c_2514,plain,
% 3.13/0.99      ( k4_xboole_0(k2_xboole_0(sK1,sK0),sK1) = sK3 ),
% 3.13/0.99      inference(light_normalisation,[status(thm)],[c_2513,c_153]) ).
% 3.13/0.99  
% 3.13/0.99  cnf(c_2637,plain,
% 3.13/0.99      ( k4_xboole_0(sK1,k4_xboole_0(sK1,k2_xboole_0(sK1,sK0))) = k4_xboole_0(k2_xboole_0(sK1,sK0),sK3) ),
% 3.13/0.99      inference(superposition,[status(thm)],[c_2514,c_1]) ).
% 3.13/0.99  
% 3.13/0.99  cnf(c_105,plain,
% 3.13/0.99      ( k4_xboole_0(sK3,k2_xboole_0(k4_xboole_0(sK3,sK1),X0)) = k4_xboole_0(k1_xboole_0,X0) ),
% 3.13/0.99      inference(superposition,[status(thm)],[c_51,c_5]) ).
% 3.13/0.99  
% 3.13/0.99  cnf(c_177,plain,
% 3.13/0.99      ( k4_xboole_0(sK3,k2_xboole_0(sK3,X0)) = k4_xboole_0(k1_xboole_0,X0) ),
% 3.13/0.99      inference(light_normalisation,[status(thm)],[c_105,c_105,c_153]) ).
% 3.13/0.99  
% 3.13/0.99  cnf(c_179,plain,
% 3.13/0.99      ( k4_xboole_0(sK3,k2_xboole_0(X0,sK3)) = k4_xboole_0(k1_xboole_0,X0) ),
% 3.13/0.99      inference(superposition,[status(thm)],[c_0,c_177]) ).
% 3.13/0.99  
% 3.13/0.99  cnf(c_301,plain,
% 3.13/0.99      ( k4_xboole_0(sK3,k2_xboole_0(sK1,sK0)) = k4_xboole_0(k1_xboole_0,sK2) ),
% 3.13/0.99      inference(superposition,[status(thm)],[c_72,c_179]) ).
% 3.13/0.99  
% 3.13/0.99  cnf(c_223,plain,
% 3.13/0.99      ( k4_xboole_0(sK3,k2_xboole_0(sK1,X0)) = k4_xboole_0(sK3,X0) ),
% 3.13/0.99      inference(superposition,[status(thm)],[c_153,c_5]) ).
% 3.13/0.99  
% 3.13/0.99  cnf(c_406,plain,
% 3.13/0.99      ( k4_xboole_0(sK3,sK0) = k4_xboole_0(k1_xboole_0,sK2) ),
% 3.13/0.99      inference(superposition,[status(thm)],[c_301,c_223]) ).
% 3.13/0.99  
% 3.13/0.99  cnf(c_811,plain,
% 3.13/0.99      ( k4_xboole_0(sK3,sK0) = k1_xboole_0 ),
% 3.13/0.99      inference(demodulation,[status(thm)],[c_542,c_406]) ).
% 3.13/0.99  
% 3.13/0.99  cnf(c_93,plain,
% 3.13/0.99      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) ),
% 3.13/0.99      inference(superposition,[status(thm)],[c_74,c_1]) ).
% 3.13/0.99  
% 3.13/0.99  cnf(c_863,plain,
% 3.13/0.99      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK0,sK3))) = k4_xboole_0(k2_xboole_0(sK0,sK3),k1_xboole_0) ),
% 3.13/0.99      inference(superposition,[status(thm)],[c_811,c_93]) ).
% 3.13/0.99  
% 3.13/0.99  cnf(c_189,plain,
% 3.13/0.99      ( k4_xboole_0(sK2,k2_xboole_0(X0,sK2)) = k4_xboole_0(k1_xboole_0,X0) ),
% 3.13/0.99      inference(superposition,[status(thm)],[c_0,c_187]) ).
% 3.13/0.99  
% 3.13/0.99  cnf(c_380,plain,
% 3.13/0.99      ( k4_xboole_0(k1_xboole_0,sK0) = k4_xboole_0(sK2,sK2) ),
% 3.13/0.99      inference(superposition,[status(thm)],[c_212,c_189]) ).
% 3.13/0.99  
% 3.13/0.99  cnf(c_381,plain,
% 3.13/0.99      ( k4_xboole_0(k1_xboole_0,sK0) = k1_xboole_0 ),
% 3.13/0.99      inference(light_normalisation,[status(thm)],[c_380,c_145]) ).
% 3.13/0.99  
% 3.13/0.99  cnf(c_426,plain,
% 3.13/0.99      ( k4_xboole_0(sK0,sK0) = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 3.13/0.99      inference(superposition,[status(thm)],[c_381,c_91]) ).
% 3.13/0.99  
% 3.13/0.99  cnf(c_427,plain,
% 3.13/0.99      ( k4_xboole_0(sK0,sK0) = k1_xboole_0 ),
% 3.13/0.99      inference(demodulation,[status(thm)],[c_426,c_3]) ).
% 3.13/0.99  
% 3.13/0.99  cnf(c_510,plain,
% 3.13/0.99      ( k4_xboole_0(sK0,k2_xboole_0(sK0,X0)) = k4_xboole_0(k1_xboole_0,X0) ),
% 3.13/0.99      inference(superposition,[status(thm)],[c_427,c_5]) ).
% 3.13/0.99  
% 3.13/0.99  cnf(c_864,plain,
% 3.13/0.99      ( k4_xboole_0(sK0,k4_xboole_0(k1_xboole_0,sK3)) = k2_xboole_0(sK0,sK3) ),
% 3.13/0.99      inference(demodulation,[status(thm)],[c_863,c_3,c_510]) ).
% 3.13/0.99  
% 3.13/0.99  cnf(c_865,plain,
% 3.13/0.99      ( k4_xboole_0(sK0,k1_xboole_0) = k2_xboole_0(sK0,sK3) ),
% 3.13/0.99      inference(light_normalisation,[status(thm)],[c_864,c_541]) ).
% 3.13/0.99  
% 3.13/0.99  cnf(c_866,plain,
% 3.13/0.99      ( k2_xboole_0(sK0,sK3) = sK0 ),
% 3.13/0.99      inference(demodulation,[status(thm)],[c_865,c_3]) ).
% 3.13/0.99  
% 3.13/0.99  cnf(c_1291,plain,
% 3.13/0.99      ( k4_xboole_0(sK2,sK3) = k4_xboole_0(sK2,sK0) ),
% 3.13/0.99      inference(superposition,[status(thm)],[c_866,c_212]) ).
% 3.13/0.99  
% 3.13/0.99  cnf(c_1292,plain,
% 3.13/0.99      ( k4_xboole_0(sK2,sK3) = sK2 ),
% 3.13/0.99      inference(light_normalisation,[status(thm)],[c_1291,c_152]) ).
% 3.13/0.99  
% 3.13/0.99  cnf(c_76,plain,
% 3.13/0.99      ( k4_xboole_0(k2_xboole_0(sK1,sK0),sK3) = k4_xboole_0(sK2,sK3) ),
% 3.13/0.99      inference(superposition,[status(thm)],[c_72,c_4]) ).
% 3.13/0.99  
% 3.13/0.99  cnf(c_1616,plain,
% 3.13/0.99      ( k4_xboole_0(k2_xboole_0(sK1,sK0),sK3) = sK2 ),
% 3.13/0.99      inference(demodulation,[status(thm)],[c_1292,c_76]) ).
% 3.13/0.99  
% 3.13/0.99  cnf(c_2639,plain,
% 3.13/0.99      ( k4_xboole_0(sK1,k4_xboole_0(sK1,k2_xboole_0(sK1,sK0))) = sK2 ),
% 3.13/0.99      inference(light_normalisation,[status(thm)],[c_2637,c_1616]) ).
% 3.13/0.99  
% 3.13/0.99  cnf(c_2640,plain,
% 3.13/0.99      ( k4_xboole_0(sK1,k4_xboole_0(k1_xboole_0,sK0)) = sK2 ),
% 3.13/0.99      inference(demodulation,[status(thm)],[c_2639,c_174]) ).
% 3.13/0.99  
% 3.13/0.99  cnf(c_2641,plain,
% 3.13/0.99      ( k4_xboole_0(sK1,k1_xboole_0) = sK2 ),
% 3.13/0.99      inference(light_normalisation,[status(thm)],[c_2640,c_381]) ).
% 3.13/0.99  
% 3.13/0.99  cnf(c_2642,plain,
% 3.13/0.99      ( sK2 = sK1 ),
% 3.13/0.99      inference(demodulation,[status(thm)],[c_2641,c_3]) ).
% 3.13/0.99  
% 3.13/0.99  cnf(c_7,negated_conjecture,
% 3.13/0.99      ( sK1 != sK2 ),
% 3.13/0.99      inference(cnf_transformation,[],[f28]) ).
% 3.13/0.99  
% 3.13/0.99  cnf(c_2910,plain,
% 3.13/0.99      ( sK1 != sK1 ),
% 3.13/0.99      inference(demodulation,[status(thm)],[c_2642,c_7]) ).
% 3.13/0.99  
% 3.13/0.99  cnf(c_2911,plain,
% 3.13/0.99      ( $false ),
% 3.13/0.99      inference(equality_resolution_simp,[status(thm)],[c_2910]) ).
% 3.13/0.99  
% 3.13/0.99  
% 3.13/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.13/0.99  
% 3.13/0.99  ------                               Statistics
% 3.13/0.99  
% 3.13/0.99  ------ General
% 3.13/0.99  
% 3.13/0.99  abstr_ref_over_cycles:                  0
% 3.13/0.99  abstr_ref_under_cycles:                 0
% 3.13/0.99  gc_basic_clause_elim:                   0
% 3.13/0.99  forced_gc_time:                         0
% 3.13/0.99  parsing_time:                           0.019
% 3.13/0.99  unif_index_cands_time:                  0.
% 3.13/0.99  unif_index_add_time:                    0.
% 3.13/0.99  orderings_time:                         0.
% 3.13/0.99  out_proof_time:                         0.008
% 3.13/0.99  total_time:                             0.201
% 3.13/0.99  num_of_symbols:                         39
% 3.13/0.99  num_of_terms:                           9106
% 3.13/0.99  
% 3.13/0.99  ------ Preprocessing
% 3.13/0.99  
% 3.13/0.99  num_of_splits:                          0
% 3.13/0.99  num_of_split_atoms:                     0
% 3.13/0.99  num_of_reused_defs:                     0
% 3.13/0.99  num_eq_ax_congr_red:                    0
% 3.13/0.99  num_of_sem_filtered_clauses:            0
% 3.13/0.99  num_of_subtypes:                        0
% 3.13/0.99  monotx_restored_types:                  0
% 3.13/0.99  sat_num_of_epr_types:                   0
% 3.13/0.99  sat_num_of_non_cyclic_types:            0
% 3.13/0.99  sat_guarded_non_collapsed_types:        0
% 3.13/0.99  num_pure_diseq_elim:                    0
% 3.13/0.99  simp_replaced_by:                       0
% 3.13/0.99  res_preprocessed:                       35
% 3.13/0.99  prep_upred:                             0
% 3.13/0.99  prep_unflattend:                        4
% 3.13/0.99  smt_new_axioms:                         0
% 3.13/0.99  pred_elim_cands:                        0
% 3.13/0.99  pred_elim:                              1
% 3.13/0.99  pred_elim_cl:                           1
% 3.13/0.99  pred_elim_cycles:                       2
% 3.13/0.99  merged_defs:                            0
% 3.13/0.99  merged_defs_ncl:                        0
% 3.13/0.99  bin_hyper_res:                          0
% 3.13/0.99  prep_cycles:                            3
% 3.13/0.99  pred_elim_time:                         0.
% 3.13/0.99  splitting_time:                         0.
% 3.13/0.99  sem_filter_time:                        0.
% 3.13/0.99  monotx_time:                            0.
% 3.13/0.99  subtype_inf_time:                       0.
% 3.13/0.99  
% 3.13/0.99  ------ Problem properties
% 3.13/0.99  
% 3.13/0.99  clauses:                                10
% 3.13/0.99  conjectures:                            2
% 3.13/0.99  epr:                                    1
% 3.13/0.99  horn:                                   10
% 3.13/0.99  ground:                                 4
% 3.13/0.99  unary:                                  10
% 3.13/0.99  binary:                                 0
% 3.13/0.99  lits:                                   10
% 3.13/0.99  lits_eq:                                10
% 3.13/0.99  fd_pure:                                0
% 3.13/0.99  fd_pseudo:                              0
% 3.13/0.99  fd_cond:                                0
% 3.13/0.99  fd_pseudo_cond:                         0
% 3.13/0.99  ac_symbols:                             0
% 3.13/0.99  
% 3.13/0.99  ------ Propositional Solver
% 3.13/0.99  
% 3.13/0.99  prop_solver_calls:                      17
% 3.13/0.99  prop_fast_solver_calls:                 86
% 3.13/0.99  smt_solver_calls:                       0
% 3.13/0.99  smt_fast_solver_calls:                  0
% 3.13/0.99  prop_num_of_clauses:                    171
% 3.13/0.99  prop_preprocess_simplified:             438
% 3.13/0.99  prop_fo_subsumed:                       0
% 3.13/0.99  prop_solver_time:                       0.
% 3.13/0.99  smt_solver_time:                        0.
% 3.13/0.99  smt_fast_solver_time:                   0.
% 3.13/0.99  prop_fast_solver_time:                  0.
% 3.13/0.99  prop_unsat_core_time:                   0.
% 3.13/0.99  
% 3.13/0.99  ------ QBF
% 3.13/0.99  
% 3.13/0.99  qbf_q_res:                              0
% 3.13/0.99  qbf_num_tautologies:                    0
% 3.13/0.99  qbf_prep_cycles:                        0
% 3.13/0.99  
% 3.13/0.99  ------ BMC1
% 3.13/0.99  
% 3.13/0.99  bmc1_current_bound:                     -1
% 3.13/0.99  bmc1_last_solved_bound:                 -1
% 3.13/0.99  bmc1_unsat_core_size:                   -1
% 3.13/0.99  bmc1_unsat_core_parents_size:           -1
% 3.13/0.99  bmc1_merge_next_fun:                    0
% 3.13/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.13/0.99  
% 3.13/0.99  ------ Instantiation
% 3.13/0.99  
% 3.13/0.99  inst_num_of_clauses:                    0
% 3.13/0.99  inst_num_in_passive:                    0
% 3.13/0.99  inst_num_in_active:                     0
% 3.13/0.99  inst_num_in_unprocessed:                0
% 3.13/0.99  inst_num_of_loops:                      0
% 3.13/0.99  inst_num_of_learning_restarts:          0
% 3.13/0.99  inst_num_moves_active_passive:          0
% 3.13/0.99  inst_lit_activity:                      0
% 3.13/0.99  inst_lit_activity_moves:                0
% 3.13/0.99  inst_num_tautologies:                   0
% 3.13/0.99  inst_num_prop_implied:                  0
% 3.13/0.99  inst_num_existing_simplified:           0
% 3.13/0.99  inst_num_eq_res_simplified:             0
% 3.13/0.99  inst_num_child_elim:                    0
% 3.13/0.99  inst_num_of_dismatching_blockings:      0
% 3.13/0.99  inst_num_of_non_proper_insts:           0
% 3.13/0.99  inst_num_of_duplicates:                 0
% 3.13/0.99  inst_inst_num_from_inst_to_res:         0
% 3.13/0.99  inst_dismatching_checking_time:         0.
% 3.13/0.99  
% 3.13/0.99  ------ Resolution
% 3.13/0.99  
% 3.13/0.99  res_num_of_clauses:                     0
% 3.13/0.99  res_num_in_passive:                     0
% 3.13/0.99  res_num_in_active:                      0
% 3.13/0.99  res_num_of_loops:                       38
% 3.13/0.99  res_forward_subset_subsumed:            0
% 3.13/0.99  res_backward_subset_subsumed:           0
% 3.13/0.99  res_forward_subsumed:                   0
% 3.13/0.99  res_backward_subsumed:                  0
% 3.13/0.99  res_forward_subsumption_resolution:     0
% 3.13/0.99  res_backward_subsumption_resolution:    0
% 3.13/0.99  res_clause_to_clause_subsumption:       4852
% 3.13/0.99  res_orphan_elimination:                 0
% 3.13/0.99  res_tautology_del:                      0
% 3.13/0.99  res_num_eq_res_simplified:              0
% 3.13/0.99  res_num_sel_changes:                    0
% 3.13/0.99  res_moves_from_active_to_pass:          0
% 3.13/0.99  
% 3.13/0.99  ------ Superposition
% 3.13/0.99  
% 3.13/0.99  sup_time_total:                         0.
% 3.13/0.99  sup_time_generating:                    0.
% 3.13/0.99  sup_time_sim_full:                      0.
% 3.13/0.99  sup_time_sim_immed:                     0.
% 3.13/0.99  
% 3.13/0.99  sup_num_of_clauses:                     530
% 3.13/0.99  sup_num_in_active:                      54
% 3.13/0.99  sup_num_in_passive:                     476
% 3.13/0.99  sup_num_of_loops:                       110
% 3.13/0.99  sup_fw_superposition:                   755
% 3.13/0.99  sup_bw_superposition:                   730
% 3.13/0.99  sup_immediate_simplified:               1072
% 3.13/0.99  sup_given_eliminated:                   2
% 3.13/0.99  comparisons_done:                       0
% 3.13/0.99  comparisons_avoided:                    0
% 3.13/0.99  
% 3.13/0.99  ------ Simplifications
% 3.13/0.99  
% 3.13/0.99  
% 3.13/0.99  sim_fw_subset_subsumed:                 0
% 3.13/0.99  sim_bw_subset_subsumed:                 0
% 3.13/0.99  sim_fw_subsumed:                        134
% 3.13/0.99  sim_bw_subsumed:                        4
% 3.13/0.99  sim_fw_subsumption_res:                 0
% 3.13/0.99  sim_bw_subsumption_res:                 0
% 3.13/0.99  sim_tautology_del:                      0
% 3.13/0.99  sim_eq_tautology_del:                   227
% 3.13/0.99  sim_eq_res_simp:                        0
% 3.13/0.99  sim_fw_demodulated:                     736
% 3.13/0.99  sim_bw_demodulated:                     67
% 3.13/0.99  sim_light_normalised:                   511
% 3.13/0.99  sim_joinable_taut:                      0
% 3.13/0.99  sim_joinable_simp:                      0
% 3.13/0.99  sim_ac_normalised:                      0
% 3.13/0.99  sim_smt_subsumption:                    0
% 3.13/0.99  
%------------------------------------------------------------------------------
