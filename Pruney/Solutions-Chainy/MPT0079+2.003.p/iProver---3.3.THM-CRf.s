%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:23:45 EST 2020

% Result     : Theorem 11.78s
% Output     : CNFRefutation 11.78s
% Verified   : 
% Statistics : Number of formulae       :  111 (1224 expanded)
%              Number of clauses        :   74 ( 457 expanded)
%              Number of leaves         :   14 ( 294 expanded)
%              Depth                    :   21
%              Number of atoms          :  160 (2072 expanded)
%              Number of equality atoms :  120 (1415 expanded)
%              Maximal formula depth    :    9 (   2 average)
%              Maximal clause size      :    8 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f12,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X3,X1)
          & r1_xboole_0(X2,X0)
          & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
       => X1 = X2 ) ),
    inference(negated_conjecture,[],[f12])).

fof(f19,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f20,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(flattening,[],[f19])).

fof(f21,plain,
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

fof(f22,plain,
    ( sK1 != sK2
    & r1_xboole_0(sK3,sK1)
    & r1_xboole_0(sK2,sK0)
    & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f20,f21])).

fof(f34,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f22])).

fof(f11,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f25,f31])).

fof(f36,plain,(
    r1_xboole_0(sK3,sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f40,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f32,f31])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f38,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f24,f31,f31])).

fof(f35,plain,(
    r1_xboole_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f37,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f22])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_13,negated_conjecture,
    ( k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_241,plain,
    ( k2_xboole_0(sK1,sK0) = k2_xboole_0(sK2,sK3) ),
    inference(demodulation,[status(thm)],[c_0,c_13])).

cnf(c_9,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_224,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_512,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_224])).

cnf(c_1815,plain,
    ( r1_tarski(sK3,k2_xboole_0(sK1,sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_241,c_512])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
    | r1_tarski(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_225,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
    | r1_tarski(k4_xboole_0(X0,X1),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2110,plain,
    ( r1_tarski(k4_xboole_0(sK3,sK1),sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1815,c_225])).

cnf(c_6,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_5,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_659,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = k2_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_6,c_5])).

cnf(c_661,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_659,c_5])).

cnf(c_1052,plain,
    ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_661,c_0])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_11,negated_conjecture,
    ( r1_xboole_0(sK3,sK1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_94,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
    | sK3 != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_11])).

cnf(c_95,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_94])).

cnf(c_8,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_836,plain,
    ( k2_xboole_0(k1_xboole_0,k4_xboole_0(sK3,sK1)) = sK3 ),
    inference(superposition,[status(thm)],[c_95,c_8])).

cnf(c_1699,plain,
    ( k4_xboole_0(sK3,sK1) = sK3 ),
    inference(superposition,[status(thm)],[c_1052,c_836])).

cnf(c_3379,plain,
    ( r1_tarski(sK3,sK0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2110,c_1699])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f27])).

cnf(c_226,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3382,plain,
    ( k2_xboole_0(sK3,sK0) = sK0 ),
    inference(superposition,[status(thm)],[c_3379,c_226])).

cnf(c_656,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_6])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_3053,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_656,c_1])).

cnf(c_44216,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,k2_xboole_0(sK3,sK0))) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK3)) ),
    inference(superposition,[status(thm)],[c_3382,c_3053])).

cnf(c_44221,plain,
    ( k4_xboole_0(sK0,sK0) = k4_xboole_0(sK3,sK0) ),
    inference(superposition,[status(thm)],[c_3382,c_6])).

cnf(c_1694,plain,
    ( k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_1052,c_6])).

cnf(c_2810,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X0)) = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_1694,c_1])).

cnf(c_2813,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X0)) = k4_xboole_0(X0,X0) ),
    inference(light_normalisation,[status(thm)],[c_2810,c_5])).

cnf(c_834,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0)) = X1 ),
    inference(superposition,[status(thm)],[c_1,c_8])).

cnf(c_6649,plain,
    ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(k4_xboole_0(X0,X0),k1_xboole_0)),k4_xboole_0(X0,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2813,c_834])).

cnf(c_846,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X0),X0) = X0 ),
    inference(superposition,[status(thm)],[c_5,c_8])).

cnf(c_6678,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6649,c_5,c_846])).

cnf(c_44250,plain,
    ( k4_xboole_0(sK3,sK0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_44221,c_6678])).

cnf(c_44265,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK3)) = k4_xboole_0(sK3,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_44216,c_3382,c_44250])).

cnf(c_12,negated_conjecture,
    ( r1_xboole_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_99,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
    | sK0 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_12])).

cnf(c_100,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_99])).

cnf(c_837,plain,
    ( k2_xboole_0(k1_xboole_0,k4_xboole_0(sK2,sK0)) = sK2 ),
    inference(superposition,[status(thm)],[c_100,c_8])).

cnf(c_1700,plain,
    ( k4_xboole_0(sK2,sK0) = sK2 ),
    inference(superposition,[status(thm)],[c_1052,c_837])).

cnf(c_6657,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = X0 ),
    inference(superposition,[status(thm)],[c_834,c_0])).

cnf(c_24033,plain,
    ( k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK2,sK2)) = sK0 ),
    inference(superposition,[status(thm)],[c_1700,c_6657])).

cnf(c_2450,plain,
    ( k4_xboole_0(sK2,sK2) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1700,c_100])).

cnf(c_24140,plain,
    ( k2_xboole_0(k4_xboole_0(sK0,sK2),k1_xboole_0) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_24033,c_2450])).

cnf(c_25116,plain,
    ( k4_xboole_0(sK0,sK2) = sK0 ),
    inference(superposition,[status(thm)],[c_24140,c_661])).

cnf(c_633,plain,
    ( r1_tarski(X0,k2_xboole_0(sK1,sK0)) != iProver_top
    | r1_tarski(k4_xboole_0(X0,sK2),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_241,c_225])).

cnf(c_1822,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK2),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_512,c_633])).

cnf(c_3377,plain,
    ( k2_xboole_0(k4_xboole_0(sK0,sK2),sK3) = sK3 ),
    inference(superposition,[status(thm)],[c_1822,c_226])).

cnf(c_12076,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,sK2),sK3) = k4_xboole_0(sK3,sK3) ),
    inference(superposition,[status(thm)],[c_3377,c_6])).

cnf(c_2210,plain,
    ( k4_xboole_0(sK3,sK3) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1699,c_95])).

cnf(c_12095,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,sK2),sK3) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_12076,c_2210])).

cnf(c_28685,plain,
    ( k4_xboole_0(sK0,sK3) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_25116,c_12095])).

cnf(c_44267,plain,
    ( k4_xboole_0(sK0,k1_xboole_0) = k4_xboole_0(sK3,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_44265,c_28685])).

cnf(c_44268,plain,
    ( sK0 = sK3 ),
    inference(demodulation,[status(thm)],[c_44267,c_5])).

cnf(c_44775,plain,
    ( k4_xboole_0(sK2,sK3) = sK2 ),
    inference(demodulation,[status(thm)],[c_44268,c_1700])).

cnf(c_658,plain,
    ( k4_xboole_0(k2_xboole_0(sK1,sK0),sK3) = k4_xboole_0(sK2,sK3) ),
    inference(superposition,[status(thm)],[c_241,c_6])).

cnf(c_44778,plain,
    ( k4_xboole_0(k2_xboole_0(sK1,sK3),sK3) = k4_xboole_0(sK2,sK3) ),
    inference(demodulation,[status(thm)],[c_44268,c_658])).

cnf(c_821,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1,c_95])).

cnf(c_1073,plain,
    ( k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK3)) = sK1 ),
    inference(superposition,[status(thm)],[c_821,c_8])).

cnf(c_2767,plain,
    ( k4_xboole_0(sK1,sK3) = sK1 ),
    inference(superposition,[status(thm)],[c_1073,c_1052])).

cnf(c_44786,plain,
    ( k4_xboole_0(sK2,sK3) = sK1 ),
    inference(demodulation,[status(thm)],[c_44778,c_6,c_2767])).

cnf(c_44792,plain,
    ( sK2 = sK1 ),
    inference(light_normalisation,[status(thm)],[c_44775,c_44786])).

cnf(c_141,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_285,plain,
    ( sK2 != X0
    | sK1 != X0
    | sK1 = sK2 ),
    inference(instantiation,[status(thm)],[c_141])).

cnf(c_286,plain,
    ( sK2 != sK1
    | sK1 = sK2
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_285])).

cnf(c_140,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_148,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_140])).

cnf(c_10,negated_conjecture,
    ( sK1 != sK2 ),
    inference(cnf_transformation,[],[f37])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_44792,c_286,c_148,c_10])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:17:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 11.78/1.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.78/1.98  
% 11.78/1.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.78/1.98  
% 11.78/1.98  ------  iProver source info
% 11.78/1.98  
% 11.78/1.98  git: date: 2020-06-30 10:37:57 +0100
% 11.78/1.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.78/1.98  git: non_committed_changes: false
% 11.78/1.98  git: last_make_outside_of_git: false
% 11.78/1.98  
% 11.78/1.98  ------ 
% 11.78/1.98  
% 11.78/1.98  ------ Input Options
% 11.78/1.98  
% 11.78/1.98  --out_options                           all
% 11.78/1.98  --tptp_safe_out                         true
% 11.78/1.98  --problem_path                          ""
% 11.78/1.98  --include_path                          ""
% 11.78/1.98  --clausifier                            res/vclausify_rel
% 11.78/1.98  --clausifier_options                    --mode clausify
% 11.78/1.98  --stdin                                 false
% 11.78/1.98  --stats_out                             all
% 11.78/1.98  
% 11.78/1.98  ------ General Options
% 11.78/1.98  
% 11.78/1.98  --fof                                   false
% 11.78/1.98  --time_out_real                         305.
% 11.78/1.98  --time_out_virtual                      -1.
% 11.78/1.98  --symbol_type_check                     false
% 11.78/1.98  --clausify_out                          false
% 11.78/1.98  --sig_cnt_out                           false
% 11.78/1.98  --trig_cnt_out                          false
% 11.78/1.98  --trig_cnt_out_tolerance                1.
% 11.78/1.98  --trig_cnt_out_sk_spl                   false
% 11.78/1.98  --abstr_cl_out                          false
% 11.78/1.98  
% 11.78/1.98  ------ Global Options
% 11.78/1.98  
% 11.78/1.98  --schedule                              default
% 11.78/1.98  --add_important_lit                     false
% 11.78/1.98  --prop_solver_per_cl                    1000
% 11.78/1.98  --min_unsat_core                        false
% 11.78/1.98  --soft_assumptions                      false
% 11.78/1.98  --soft_lemma_size                       3
% 11.78/1.98  --prop_impl_unit_size                   0
% 11.78/1.98  --prop_impl_unit                        []
% 11.78/1.98  --share_sel_clauses                     true
% 11.78/1.98  --reset_solvers                         false
% 11.78/1.98  --bc_imp_inh                            [conj_cone]
% 11.78/1.98  --conj_cone_tolerance                   3.
% 11.78/1.98  --extra_neg_conj                        none
% 11.78/1.98  --large_theory_mode                     true
% 11.78/1.98  --prolific_symb_bound                   200
% 11.78/1.98  --lt_threshold                          2000
% 11.78/1.98  --clause_weak_htbl                      true
% 11.78/1.98  --gc_record_bc_elim                     false
% 11.78/1.98  
% 11.78/1.98  ------ Preprocessing Options
% 11.78/1.98  
% 11.78/1.98  --preprocessing_flag                    true
% 11.78/1.98  --time_out_prep_mult                    0.1
% 11.78/1.98  --splitting_mode                        input
% 11.78/1.98  --splitting_grd                         true
% 11.78/1.98  --splitting_cvd                         false
% 11.78/1.98  --splitting_cvd_svl                     false
% 11.78/1.98  --splitting_nvd                         32
% 11.78/1.98  --sub_typing                            true
% 11.78/1.98  --prep_gs_sim                           true
% 11.78/1.98  --prep_unflatten                        true
% 11.78/1.98  --prep_res_sim                          true
% 11.78/1.98  --prep_upred                            true
% 11.78/1.98  --prep_sem_filter                       exhaustive
% 11.78/1.98  --prep_sem_filter_out                   false
% 11.78/1.98  --pred_elim                             true
% 11.78/1.98  --res_sim_input                         true
% 11.78/1.98  --eq_ax_congr_red                       true
% 11.78/1.98  --pure_diseq_elim                       true
% 11.78/1.98  --brand_transform                       false
% 11.78/1.98  --non_eq_to_eq                          false
% 11.78/1.98  --prep_def_merge                        true
% 11.78/1.98  --prep_def_merge_prop_impl              false
% 11.78/1.98  --prep_def_merge_mbd                    true
% 11.78/1.98  --prep_def_merge_tr_red                 false
% 11.78/1.98  --prep_def_merge_tr_cl                  false
% 11.78/1.98  --smt_preprocessing                     true
% 11.78/1.98  --smt_ac_axioms                         fast
% 11.78/1.98  --preprocessed_out                      false
% 11.78/1.98  --preprocessed_stats                    false
% 11.78/1.98  
% 11.78/1.98  ------ Abstraction refinement Options
% 11.78/1.98  
% 11.78/1.98  --abstr_ref                             []
% 11.78/1.98  --abstr_ref_prep                        false
% 11.78/1.98  --abstr_ref_until_sat                   false
% 11.78/1.98  --abstr_ref_sig_restrict                funpre
% 11.78/1.98  --abstr_ref_af_restrict_to_split_sk     false
% 11.78/1.98  --abstr_ref_under                       []
% 11.78/1.98  
% 11.78/1.98  ------ SAT Options
% 11.78/1.98  
% 11.78/1.98  --sat_mode                              false
% 11.78/1.98  --sat_fm_restart_options                ""
% 11.78/1.98  --sat_gr_def                            false
% 11.78/1.98  --sat_epr_types                         true
% 11.78/1.98  --sat_non_cyclic_types                  false
% 11.78/1.98  --sat_finite_models                     false
% 11.78/1.98  --sat_fm_lemmas                         false
% 11.78/1.98  --sat_fm_prep                           false
% 11.78/1.98  --sat_fm_uc_incr                        true
% 11.78/1.98  --sat_out_model                         small
% 11.78/1.98  --sat_out_clauses                       false
% 11.78/1.98  
% 11.78/1.98  ------ QBF Options
% 11.78/1.98  
% 11.78/1.98  --qbf_mode                              false
% 11.78/1.98  --qbf_elim_univ                         false
% 11.78/1.98  --qbf_dom_inst                          none
% 11.78/1.98  --qbf_dom_pre_inst                      false
% 11.78/1.98  --qbf_sk_in                             false
% 11.78/1.98  --qbf_pred_elim                         true
% 11.78/1.98  --qbf_split                             512
% 11.78/1.98  
% 11.78/1.98  ------ BMC1 Options
% 11.78/1.98  
% 11.78/1.98  --bmc1_incremental                      false
% 11.78/1.98  --bmc1_axioms                           reachable_all
% 11.78/1.98  --bmc1_min_bound                        0
% 11.78/1.98  --bmc1_max_bound                        -1
% 11.78/1.98  --bmc1_max_bound_default                -1
% 11.78/1.98  --bmc1_symbol_reachability              true
% 11.78/1.98  --bmc1_property_lemmas                  false
% 11.78/1.98  --bmc1_k_induction                      false
% 11.78/1.98  --bmc1_non_equiv_states                 false
% 11.78/1.98  --bmc1_deadlock                         false
% 11.78/1.98  --bmc1_ucm                              false
% 11.78/1.98  --bmc1_add_unsat_core                   none
% 11.78/1.98  --bmc1_unsat_core_children              false
% 11.78/1.98  --bmc1_unsat_core_extrapolate_axioms    false
% 11.78/1.98  --bmc1_out_stat                         full
% 11.78/1.98  --bmc1_ground_init                      false
% 11.78/1.98  --bmc1_pre_inst_next_state              false
% 11.78/1.98  --bmc1_pre_inst_state                   false
% 11.78/1.98  --bmc1_pre_inst_reach_state             false
% 11.78/1.98  --bmc1_out_unsat_core                   false
% 11.78/1.98  --bmc1_aig_witness_out                  false
% 11.78/1.98  --bmc1_verbose                          false
% 11.78/1.98  --bmc1_dump_clauses_tptp                false
% 11.78/1.98  --bmc1_dump_unsat_core_tptp             false
% 11.78/1.98  --bmc1_dump_file                        -
% 11.78/1.98  --bmc1_ucm_expand_uc_limit              128
% 11.78/1.98  --bmc1_ucm_n_expand_iterations          6
% 11.78/1.98  --bmc1_ucm_extend_mode                  1
% 11.78/1.98  --bmc1_ucm_init_mode                    2
% 11.78/1.98  --bmc1_ucm_cone_mode                    none
% 11.78/1.98  --bmc1_ucm_reduced_relation_type        0
% 11.78/1.98  --bmc1_ucm_relax_model                  4
% 11.78/1.98  --bmc1_ucm_full_tr_after_sat            true
% 11.78/1.98  --bmc1_ucm_expand_neg_assumptions       false
% 11.78/1.98  --bmc1_ucm_layered_model                none
% 11.78/1.98  --bmc1_ucm_max_lemma_size               10
% 11.78/1.98  
% 11.78/1.98  ------ AIG Options
% 11.78/1.98  
% 11.78/1.98  --aig_mode                              false
% 11.78/1.98  
% 11.78/1.98  ------ Instantiation Options
% 11.78/1.98  
% 11.78/1.98  --instantiation_flag                    true
% 11.78/1.98  --inst_sos_flag                         false
% 11.78/1.98  --inst_sos_phase                        true
% 11.78/1.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.78/1.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.78/1.98  --inst_lit_sel_side                     num_symb
% 11.78/1.98  --inst_solver_per_active                1400
% 11.78/1.98  --inst_solver_calls_frac                1.
% 11.78/1.98  --inst_passive_queue_type               priority_queues
% 11.78/1.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.78/1.98  --inst_passive_queues_freq              [25;2]
% 11.78/1.98  --inst_dismatching                      true
% 11.78/1.98  --inst_eager_unprocessed_to_passive     true
% 11.78/1.98  --inst_prop_sim_given                   true
% 11.78/1.98  --inst_prop_sim_new                     false
% 11.78/1.98  --inst_subs_new                         false
% 11.78/1.98  --inst_eq_res_simp                      false
% 11.78/1.98  --inst_subs_given                       false
% 11.78/1.98  --inst_orphan_elimination               true
% 11.78/1.98  --inst_learning_loop_flag               true
% 11.78/1.98  --inst_learning_start                   3000
% 11.78/1.98  --inst_learning_factor                  2
% 11.78/1.98  --inst_start_prop_sim_after_learn       3
% 11.78/1.98  --inst_sel_renew                        solver
% 11.78/1.98  --inst_lit_activity_flag                true
% 11.78/1.98  --inst_restr_to_given                   false
% 11.78/1.98  --inst_activity_threshold               500
% 11.78/1.98  --inst_out_proof                        true
% 11.78/1.98  
% 11.78/1.98  ------ Resolution Options
% 11.78/1.98  
% 11.78/1.98  --resolution_flag                       true
% 11.78/1.98  --res_lit_sel                           adaptive
% 11.78/1.98  --res_lit_sel_side                      none
% 11.78/1.98  --res_ordering                          kbo
% 11.78/1.98  --res_to_prop_solver                    active
% 11.78/1.98  --res_prop_simpl_new                    false
% 11.78/1.98  --res_prop_simpl_given                  true
% 11.78/1.98  --res_passive_queue_type                priority_queues
% 11.78/1.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.78/1.98  --res_passive_queues_freq               [15;5]
% 11.78/1.98  --res_forward_subs                      full
% 11.78/1.98  --res_backward_subs                     full
% 11.78/1.98  --res_forward_subs_resolution           true
% 11.78/1.98  --res_backward_subs_resolution          true
% 11.78/1.98  --res_orphan_elimination                true
% 11.78/1.98  --res_time_limit                        2.
% 11.78/1.98  --res_out_proof                         true
% 11.78/1.98  
% 11.78/1.98  ------ Superposition Options
% 11.78/1.98  
% 11.78/1.98  --superposition_flag                    true
% 11.78/1.98  --sup_passive_queue_type                priority_queues
% 11.78/1.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.78/1.98  --sup_passive_queues_freq               [8;1;4]
% 11.78/1.98  --demod_completeness_check              fast
% 11.78/1.98  --demod_use_ground                      true
% 11.78/1.98  --sup_to_prop_solver                    passive
% 11.78/1.98  --sup_prop_simpl_new                    true
% 11.78/1.98  --sup_prop_simpl_given                  true
% 11.78/1.98  --sup_fun_splitting                     false
% 11.78/1.98  --sup_smt_interval                      50000
% 11.78/1.98  
% 11.78/1.98  ------ Superposition Simplification Setup
% 11.78/1.98  
% 11.78/1.98  --sup_indices_passive                   []
% 11.78/1.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.78/1.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.78/1.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.78/1.98  --sup_full_triv                         [TrivRules;PropSubs]
% 11.78/1.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.78/1.98  --sup_full_bw                           [BwDemod]
% 11.78/1.98  --sup_immed_triv                        [TrivRules]
% 11.78/1.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.78/1.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.78/1.98  --sup_immed_bw_main                     []
% 11.78/1.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.78/1.98  --sup_input_triv                        [Unflattening;TrivRules]
% 11.78/1.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.78/1.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.78/1.98  
% 11.78/1.98  ------ Combination Options
% 11.78/1.98  
% 11.78/1.98  --comb_res_mult                         3
% 11.78/1.98  --comb_sup_mult                         2
% 11.78/1.98  --comb_inst_mult                        10
% 11.78/1.98  
% 11.78/1.98  ------ Debug Options
% 11.78/1.98  
% 11.78/1.98  --dbg_backtrace                         false
% 11.78/1.98  --dbg_dump_prop_clauses                 false
% 11.78/1.98  --dbg_dump_prop_clauses_file            -
% 11.78/1.98  --dbg_out_stat                          false
% 11.78/1.98  ------ Parsing...
% 11.78/1.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.78/1.98  
% 11.78/1.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 11.78/1.98  
% 11.78/1.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.78/1.98  
% 11.78/1.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.78/1.98  ------ Proving...
% 11.78/1.98  ------ Problem Properties 
% 11.78/1.98  
% 11.78/1.98  
% 11.78/1.98  clauses                                 13
% 11.78/1.98  conjectures                             2
% 11.78/1.98  EPR                                     1
% 11.78/1.98  Horn                                    13
% 11.78/1.98  unary                                   10
% 11.78/1.98  binary                                  3
% 11.78/1.98  lits                                    16
% 11.78/1.98  lits eq                                 10
% 11.78/1.98  fd_pure                                 0
% 11.78/1.98  fd_pseudo                               0
% 11.78/1.98  fd_cond                                 0
% 11.78/1.98  fd_pseudo_cond                          0
% 11.78/1.98  AC symbols                              0
% 11.78/1.98  
% 11.78/1.98  ------ Schedule dynamic 5 is on 
% 11.78/1.98  
% 11.78/1.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.78/1.98  
% 11.78/1.98  
% 11.78/1.98  ------ 
% 11.78/1.98  Current options:
% 11.78/1.98  ------ 
% 11.78/1.98  
% 11.78/1.98  ------ Input Options
% 11.78/1.98  
% 11.78/1.98  --out_options                           all
% 11.78/1.98  --tptp_safe_out                         true
% 11.78/1.98  --problem_path                          ""
% 11.78/1.98  --include_path                          ""
% 11.78/1.98  --clausifier                            res/vclausify_rel
% 11.78/1.98  --clausifier_options                    --mode clausify
% 11.78/1.98  --stdin                                 false
% 11.78/1.98  --stats_out                             all
% 11.78/1.98  
% 11.78/1.98  ------ General Options
% 11.78/1.98  
% 11.78/1.98  --fof                                   false
% 11.78/1.98  --time_out_real                         305.
% 11.78/1.98  --time_out_virtual                      -1.
% 11.78/1.98  --symbol_type_check                     false
% 11.78/1.98  --clausify_out                          false
% 11.78/1.98  --sig_cnt_out                           false
% 11.78/1.98  --trig_cnt_out                          false
% 11.78/1.98  --trig_cnt_out_tolerance                1.
% 11.78/1.98  --trig_cnt_out_sk_spl                   false
% 11.78/1.98  --abstr_cl_out                          false
% 11.78/1.98  
% 11.78/1.98  ------ Global Options
% 11.78/1.98  
% 11.78/1.98  --schedule                              default
% 11.78/1.98  --add_important_lit                     false
% 11.78/1.98  --prop_solver_per_cl                    1000
% 11.78/1.98  --min_unsat_core                        false
% 11.78/1.98  --soft_assumptions                      false
% 11.78/1.98  --soft_lemma_size                       3
% 11.78/1.98  --prop_impl_unit_size                   0
% 11.78/1.98  --prop_impl_unit                        []
% 11.78/1.98  --share_sel_clauses                     true
% 11.78/1.98  --reset_solvers                         false
% 11.78/1.98  --bc_imp_inh                            [conj_cone]
% 11.78/1.98  --conj_cone_tolerance                   3.
% 11.78/1.98  --extra_neg_conj                        none
% 11.78/1.98  --large_theory_mode                     true
% 11.78/1.98  --prolific_symb_bound                   200
% 11.78/1.98  --lt_threshold                          2000
% 11.78/1.98  --clause_weak_htbl                      true
% 11.78/1.98  --gc_record_bc_elim                     false
% 11.78/1.98  
% 11.78/1.98  ------ Preprocessing Options
% 11.78/1.98  
% 11.78/1.98  --preprocessing_flag                    true
% 11.78/1.98  --time_out_prep_mult                    0.1
% 11.78/1.98  --splitting_mode                        input
% 11.78/1.98  --splitting_grd                         true
% 11.78/1.98  --splitting_cvd                         false
% 11.78/1.98  --splitting_cvd_svl                     false
% 11.78/1.98  --splitting_nvd                         32
% 11.78/1.98  --sub_typing                            true
% 11.78/1.98  --prep_gs_sim                           true
% 11.78/1.98  --prep_unflatten                        true
% 11.78/1.98  --prep_res_sim                          true
% 11.78/1.98  --prep_upred                            true
% 11.78/1.98  --prep_sem_filter                       exhaustive
% 11.78/1.98  --prep_sem_filter_out                   false
% 11.78/1.98  --pred_elim                             true
% 11.78/1.98  --res_sim_input                         true
% 11.78/1.98  --eq_ax_congr_red                       true
% 11.78/1.98  --pure_diseq_elim                       true
% 11.78/1.98  --brand_transform                       false
% 11.78/1.98  --non_eq_to_eq                          false
% 11.78/1.98  --prep_def_merge                        true
% 11.78/1.98  --prep_def_merge_prop_impl              false
% 11.78/1.98  --prep_def_merge_mbd                    true
% 11.78/1.98  --prep_def_merge_tr_red                 false
% 11.78/1.98  --prep_def_merge_tr_cl                  false
% 11.78/1.98  --smt_preprocessing                     true
% 11.78/1.98  --smt_ac_axioms                         fast
% 11.78/1.98  --preprocessed_out                      false
% 11.78/1.98  --preprocessed_stats                    false
% 11.78/1.98  
% 11.78/1.98  ------ Abstraction refinement Options
% 11.78/1.98  
% 11.78/1.98  --abstr_ref                             []
% 11.78/1.98  --abstr_ref_prep                        false
% 11.78/1.98  --abstr_ref_until_sat                   false
% 11.78/1.98  --abstr_ref_sig_restrict                funpre
% 11.78/1.98  --abstr_ref_af_restrict_to_split_sk     false
% 11.78/1.98  --abstr_ref_under                       []
% 11.78/1.98  
% 11.78/1.98  ------ SAT Options
% 11.78/1.98  
% 11.78/1.98  --sat_mode                              false
% 11.78/1.98  --sat_fm_restart_options                ""
% 11.78/1.98  --sat_gr_def                            false
% 11.78/1.98  --sat_epr_types                         true
% 11.78/1.98  --sat_non_cyclic_types                  false
% 11.78/1.98  --sat_finite_models                     false
% 11.78/1.98  --sat_fm_lemmas                         false
% 11.78/1.98  --sat_fm_prep                           false
% 11.78/1.98  --sat_fm_uc_incr                        true
% 11.78/1.98  --sat_out_model                         small
% 11.78/1.98  --sat_out_clauses                       false
% 11.78/1.98  
% 11.78/1.98  ------ QBF Options
% 11.78/1.98  
% 11.78/1.98  --qbf_mode                              false
% 11.78/1.98  --qbf_elim_univ                         false
% 11.78/1.98  --qbf_dom_inst                          none
% 11.78/1.98  --qbf_dom_pre_inst                      false
% 11.78/1.98  --qbf_sk_in                             false
% 11.78/1.98  --qbf_pred_elim                         true
% 11.78/1.98  --qbf_split                             512
% 11.78/1.98  
% 11.78/1.98  ------ BMC1 Options
% 11.78/1.98  
% 11.78/1.98  --bmc1_incremental                      false
% 11.78/1.98  --bmc1_axioms                           reachable_all
% 11.78/1.98  --bmc1_min_bound                        0
% 11.78/1.98  --bmc1_max_bound                        -1
% 11.78/1.98  --bmc1_max_bound_default                -1
% 11.78/1.98  --bmc1_symbol_reachability              true
% 11.78/1.98  --bmc1_property_lemmas                  false
% 11.78/1.98  --bmc1_k_induction                      false
% 11.78/1.98  --bmc1_non_equiv_states                 false
% 11.78/1.98  --bmc1_deadlock                         false
% 11.78/1.98  --bmc1_ucm                              false
% 11.78/1.98  --bmc1_add_unsat_core                   none
% 11.78/1.98  --bmc1_unsat_core_children              false
% 11.78/1.98  --bmc1_unsat_core_extrapolate_axioms    false
% 11.78/1.98  --bmc1_out_stat                         full
% 11.78/1.98  --bmc1_ground_init                      false
% 11.78/1.98  --bmc1_pre_inst_next_state              false
% 11.78/1.98  --bmc1_pre_inst_state                   false
% 11.78/1.98  --bmc1_pre_inst_reach_state             false
% 11.78/1.98  --bmc1_out_unsat_core                   false
% 11.78/1.98  --bmc1_aig_witness_out                  false
% 11.78/1.98  --bmc1_verbose                          false
% 11.78/1.98  --bmc1_dump_clauses_tptp                false
% 11.78/1.98  --bmc1_dump_unsat_core_tptp             false
% 11.78/1.98  --bmc1_dump_file                        -
% 11.78/1.98  --bmc1_ucm_expand_uc_limit              128
% 11.78/1.98  --bmc1_ucm_n_expand_iterations          6
% 11.78/1.98  --bmc1_ucm_extend_mode                  1
% 11.78/1.98  --bmc1_ucm_init_mode                    2
% 11.78/1.98  --bmc1_ucm_cone_mode                    none
% 11.78/1.98  --bmc1_ucm_reduced_relation_type        0
% 11.78/1.98  --bmc1_ucm_relax_model                  4
% 11.78/1.98  --bmc1_ucm_full_tr_after_sat            true
% 11.78/1.98  --bmc1_ucm_expand_neg_assumptions       false
% 11.78/1.98  --bmc1_ucm_layered_model                none
% 11.78/1.98  --bmc1_ucm_max_lemma_size               10
% 11.78/1.98  
% 11.78/1.98  ------ AIG Options
% 11.78/1.98  
% 11.78/1.98  --aig_mode                              false
% 11.78/1.98  
% 11.78/1.98  ------ Instantiation Options
% 11.78/1.98  
% 11.78/1.98  --instantiation_flag                    true
% 11.78/1.98  --inst_sos_flag                         false
% 11.78/1.98  --inst_sos_phase                        true
% 11.78/1.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.78/1.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.78/1.98  --inst_lit_sel_side                     none
% 11.78/1.98  --inst_solver_per_active                1400
% 11.78/1.98  --inst_solver_calls_frac                1.
% 11.78/1.98  --inst_passive_queue_type               priority_queues
% 11.78/1.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.78/1.98  --inst_passive_queues_freq              [25;2]
% 11.78/1.98  --inst_dismatching                      true
% 11.78/1.98  --inst_eager_unprocessed_to_passive     true
% 11.78/1.98  --inst_prop_sim_given                   true
% 11.78/1.98  --inst_prop_sim_new                     false
% 11.78/1.98  --inst_subs_new                         false
% 11.78/1.98  --inst_eq_res_simp                      false
% 11.78/1.98  --inst_subs_given                       false
% 11.78/1.98  --inst_orphan_elimination               true
% 11.78/1.98  --inst_learning_loop_flag               true
% 11.78/1.98  --inst_learning_start                   3000
% 11.78/1.98  --inst_learning_factor                  2
% 11.78/1.98  --inst_start_prop_sim_after_learn       3
% 11.78/1.98  --inst_sel_renew                        solver
% 11.78/1.98  --inst_lit_activity_flag                true
% 11.78/1.98  --inst_restr_to_given                   false
% 11.78/1.98  --inst_activity_threshold               500
% 11.78/1.98  --inst_out_proof                        true
% 11.78/1.98  
% 11.78/1.98  ------ Resolution Options
% 11.78/1.98  
% 11.78/1.98  --resolution_flag                       false
% 11.78/1.98  --res_lit_sel                           adaptive
% 11.78/1.98  --res_lit_sel_side                      none
% 11.78/1.98  --res_ordering                          kbo
% 11.78/1.98  --res_to_prop_solver                    active
% 11.78/1.98  --res_prop_simpl_new                    false
% 11.78/1.98  --res_prop_simpl_given                  true
% 11.78/1.98  --res_passive_queue_type                priority_queues
% 11.78/1.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.78/1.98  --res_passive_queues_freq               [15;5]
% 11.78/1.98  --res_forward_subs                      full
% 11.78/1.98  --res_backward_subs                     full
% 11.78/1.98  --res_forward_subs_resolution           true
% 11.78/1.98  --res_backward_subs_resolution          true
% 11.78/1.98  --res_orphan_elimination                true
% 11.78/1.98  --res_time_limit                        2.
% 11.78/1.98  --res_out_proof                         true
% 11.78/1.98  
% 11.78/1.98  ------ Superposition Options
% 11.78/1.98  
% 11.78/1.98  --superposition_flag                    true
% 11.78/1.98  --sup_passive_queue_type                priority_queues
% 11.78/1.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.78/1.98  --sup_passive_queues_freq               [8;1;4]
% 11.78/1.98  --demod_completeness_check              fast
% 11.78/1.98  --demod_use_ground                      true
% 11.78/1.98  --sup_to_prop_solver                    passive
% 11.78/1.98  --sup_prop_simpl_new                    true
% 11.78/1.98  --sup_prop_simpl_given                  true
% 11.78/1.98  --sup_fun_splitting                     false
% 11.78/1.98  --sup_smt_interval                      50000
% 11.78/1.98  
% 11.78/1.98  ------ Superposition Simplification Setup
% 11.78/1.98  
% 11.78/1.98  --sup_indices_passive                   []
% 11.78/1.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.78/1.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.78/1.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.78/1.98  --sup_full_triv                         [TrivRules;PropSubs]
% 11.78/1.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.78/1.98  --sup_full_bw                           [BwDemod]
% 11.78/1.98  --sup_immed_triv                        [TrivRules]
% 11.78/1.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.78/1.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.78/1.98  --sup_immed_bw_main                     []
% 11.78/1.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.78/1.98  --sup_input_triv                        [Unflattening;TrivRules]
% 11.78/1.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.78/1.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.78/1.98  
% 11.78/1.98  ------ Combination Options
% 11.78/1.98  
% 11.78/1.98  --comb_res_mult                         3
% 11.78/1.98  --comb_sup_mult                         2
% 11.78/1.98  --comb_inst_mult                        10
% 11.78/1.98  
% 11.78/1.98  ------ Debug Options
% 11.78/1.98  
% 11.78/1.98  --dbg_backtrace                         false
% 11.78/1.98  --dbg_dump_prop_clauses                 false
% 11.78/1.98  --dbg_dump_prop_clauses_file            -
% 11.78/1.98  --dbg_out_stat                          false
% 11.78/1.98  
% 11.78/1.98  
% 11.78/1.98  
% 11.78/1.98  
% 11.78/1.98  ------ Proving...
% 11.78/1.98  
% 11.78/1.98  
% 11.78/1.98  % SZS status Theorem for theBenchmark.p
% 11.78/1.98  
% 11.78/1.98  % SZS output start CNFRefutation for theBenchmark.p
% 11.78/1.98  
% 11.78/1.98  fof(f1,axiom,(
% 11.78/1.98    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 11.78/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.78/1.98  
% 11.78/1.98  fof(f23,plain,(
% 11.78/1.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 11.78/1.98    inference(cnf_transformation,[],[f1])).
% 11.78/1.98  
% 11.78/1.98  fof(f12,conjecture,(
% 11.78/1.98    ! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 11.78/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.78/1.98  
% 11.78/1.98  fof(f13,negated_conjecture,(
% 11.78/1.98    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 11.78/1.98    inference(negated_conjecture,[],[f12])).
% 11.78/1.98  
% 11.78/1.98  fof(f19,plain,(
% 11.78/1.98    ? [X0,X1,X2,X3] : (X1 != X2 & (r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)))),
% 11.78/1.98    inference(ennf_transformation,[],[f13])).
% 11.78/1.98  
% 11.78/1.98  fof(f20,plain,(
% 11.78/1.98    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3))),
% 11.78/1.98    inference(flattening,[],[f19])).
% 11.78/1.98  
% 11.78/1.98  fof(f21,plain,(
% 11.78/1.98    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => (sK1 != sK2 & r1_xboole_0(sK3,sK1) & r1_xboole_0(sK2,sK0) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3))),
% 11.78/1.98    introduced(choice_axiom,[])).
% 11.78/1.98  
% 11.78/1.98  fof(f22,plain,(
% 11.78/1.98    sK1 != sK2 & r1_xboole_0(sK3,sK1) & r1_xboole_0(sK2,sK0) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 11.78/1.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f20,f21])).
% 11.78/1.98  
% 11.78/1.98  fof(f34,plain,(
% 11.78/1.98    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 11.78/1.98    inference(cnf_transformation,[],[f22])).
% 11.78/1.98  
% 11.78/1.98  fof(f11,axiom,(
% 11.78/1.98    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 11.78/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.78/1.98  
% 11.78/1.98  fof(f33,plain,(
% 11.78/1.98    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 11.78/1.98    inference(cnf_transformation,[],[f11])).
% 11.78/1.98  
% 11.78/1.98  fof(f8,axiom,(
% 11.78/1.98    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 11.78/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.78/1.98  
% 11.78/1.98  fof(f18,plain,(
% 11.78/1.98    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 11.78/1.98    inference(ennf_transformation,[],[f8])).
% 11.78/1.98  
% 11.78/1.98  fof(f30,plain,(
% 11.78/1.98    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 11.78/1.98    inference(cnf_transformation,[],[f18])).
% 11.78/1.98  
% 11.78/1.98  fof(f7,axiom,(
% 11.78/1.98    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 11.78/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.78/1.98  
% 11.78/1.98  fof(f29,plain,(
% 11.78/1.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 11.78/1.98    inference(cnf_transformation,[],[f7])).
% 11.78/1.98  
% 11.78/1.98  fof(f6,axiom,(
% 11.78/1.98    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 11.78/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.78/1.98  
% 11.78/1.98  fof(f28,plain,(
% 11.78/1.98    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 11.78/1.98    inference(cnf_transformation,[],[f6])).
% 11.78/1.98  
% 11.78/1.98  fof(f3,axiom,(
% 11.78/1.98    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 11.78/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.78/1.98  
% 11.78/1.98  fof(f14,plain,(
% 11.78/1.98    ! [X0,X1] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,X1) = k1_xboole_0)),
% 11.78/1.98    inference(unused_predicate_definition_removal,[],[f3])).
% 11.78/1.98  
% 11.78/1.98  fof(f15,plain,(
% 11.78/1.98    ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1))),
% 11.78/1.98    inference(ennf_transformation,[],[f14])).
% 11.78/1.98  
% 11.78/1.98  fof(f25,plain,(
% 11.78/1.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 11.78/1.98    inference(cnf_transformation,[],[f15])).
% 11.78/1.98  
% 11.78/1.98  fof(f9,axiom,(
% 11.78/1.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 11.78/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.78/1.98  
% 11.78/1.98  fof(f31,plain,(
% 11.78/1.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 11.78/1.98    inference(cnf_transformation,[],[f9])).
% 11.78/1.98  
% 11.78/1.98  fof(f39,plain,(
% 11.78/1.98    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 11.78/1.98    inference(definition_unfolding,[],[f25,f31])).
% 11.78/1.98  
% 11.78/1.98  fof(f36,plain,(
% 11.78/1.98    r1_xboole_0(sK3,sK1)),
% 11.78/1.98    inference(cnf_transformation,[],[f22])).
% 11.78/1.98  
% 11.78/1.98  fof(f10,axiom,(
% 11.78/1.98    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 11.78/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.78/1.98  
% 11.78/1.98  fof(f32,plain,(
% 11.78/1.98    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 11.78/1.98    inference(cnf_transformation,[],[f10])).
% 11.78/1.98  
% 11.78/1.98  fof(f40,plain,(
% 11.78/1.98    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 11.78/1.98    inference(definition_unfolding,[],[f32,f31])).
% 11.78/1.98  
% 11.78/1.98  fof(f5,axiom,(
% 11.78/1.98    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 11.78/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.78/1.98  
% 11.78/1.98  fof(f17,plain,(
% 11.78/1.98    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 11.78/1.98    inference(ennf_transformation,[],[f5])).
% 11.78/1.98  
% 11.78/1.98  fof(f27,plain,(
% 11.78/1.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 11.78/1.98    inference(cnf_transformation,[],[f17])).
% 11.78/1.98  
% 11.78/1.98  fof(f2,axiom,(
% 11.78/1.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 11.78/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.78/1.98  
% 11.78/1.98  fof(f24,plain,(
% 11.78/1.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 11.78/1.98    inference(cnf_transformation,[],[f2])).
% 11.78/1.98  
% 11.78/1.98  fof(f38,plain,(
% 11.78/1.98    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 11.78/1.98    inference(definition_unfolding,[],[f24,f31,f31])).
% 11.78/1.98  
% 11.78/1.98  fof(f35,plain,(
% 11.78/1.98    r1_xboole_0(sK2,sK0)),
% 11.78/1.98    inference(cnf_transformation,[],[f22])).
% 11.78/1.98  
% 11.78/1.98  fof(f37,plain,(
% 11.78/1.98    sK1 != sK2),
% 11.78/1.98    inference(cnf_transformation,[],[f22])).
% 11.78/1.98  
% 11.78/1.98  cnf(c_0,plain,
% 11.78/1.98      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 11.78/1.98      inference(cnf_transformation,[],[f23]) ).
% 11.78/1.98  
% 11.78/1.98  cnf(c_13,negated_conjecture,
% 11.78/1.98      ( k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
% 11.78/1.98      inference(cnf_transformation,[],[f34]) ).
% 11.78/1.98  
% 11.78/1.98  cnf(c_241,plain,
% 11.78/1.98      ( k2_xboole_0(sK1,sK0) = k2_xboole_0(sK2,sK3) ),
% 11.78/1.98      inference(demodulation,[status(thm)],[c_0,c_13]) ).
% 11.78/1.98  
% 11.78/1.98  cnf(c_9,plain,
% 11.78/1.98      ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
% 11.78/1.98      inference(cnf_transformation,[],[f33]) ).
% 11.78/1.98  
% 11.78/1.98  cnf(c_224,plain,
% 11.78/1.98      ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
% 11.78/1.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 11.78/1.98  
% 11.78/1.98  cnf(c_512,plain,
% 11.78/1.98      ( r1_tarski(X0,k2_xboole_0(X1,X0)) = iProver_top ),
% 11.78/1.98      inference(superposition,[status(thm)],[c_0,c_224]) ).
% 11.78/1.98  
% 11.78/1.98  cnf(c_1815,plain,
% 11.78/1.98      ( r1_tarski(sK3,k2_xboole_0(sK1,sK0)) = iProver_top ),
% 11.78/1.98      inference(superposition,[status(thm)],[c_241,c_512]) ).
% 11.78/1.98  
% 11.78/1.98  cnf(c_7,plain,
% 11.78/1.98      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
% 11.78/1.98      | r1_tarski(k4_xboole_0(X0,X1),X2) ),
% 11.78/1.98      inference(cnf_transformation,[],[f30]) ).
% 11.78/1.98  
% 11.78/1.98  cnf(c_225,plain,
% 11.78/1.98      ( r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
% 11.78/1.98      | r1_tarski(k4_xboole_0(X0,X1),X2) = iProver_top ),
% 11.78/1.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 11.78/1.98  
% 11.78/1.98  cnf(c_2110,plain,
% 11.78/1.98      ( r1_tarski(k4_xboole_0(sK3,sK1),sK0) = iProver_top ),
% 11.78/1.98      inference(superposition,[status(thm)],[c_1815,c_225]) ).
% 11.78/1.98  
% 11.78/1.98  cnf(c_6,plain,
% 11.78/1.98      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
% 11.78/1.98      inference(cnf_transformation,[],[f29]) ).
% 11.78/1.98  
% 11.78/1.98  cnf(c_5,plain,
% 11.78/1.98      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 11.78/1.98      inference(cnf_transformation,[],[f28]) ).
% 11.78/1.98  
% 11.78/1.98  cnf(c_659,plain,
% 11.78/1.98      ( k4_xboole_0(X0,k1_xboole_0) = k2_xboole_0(X0,k1_xboole_0) ),
% 11.78/1.98      inference(superposition,[status(thm)],[c_6,c_5]) ).
% 11.78/1.98  
% 11.78/1.98  cnf(c_661,plain,
% 11.78/1.98      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 11.78/1.98      inference(light_normalisation,[status(thm)],[c_659,c_5]) ).
% 11.78/1.98  
% 11.78/1.98  cnf(c_1052,plain,
% 11.78/1.98      ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
% 11.78/1.98      inference(superposition,[status(thm)],[c_661,c_0]) ).
% 11.78/1.98  
% 11.78/1.98  cnf(c_2,plain,
% 11.78/1.98      ( ~ r1_xboole_0(X0,X1)
% 11.78/1.98      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 11.78/1.98      inference(cnf_transformation,[],[f39]) ).
% 11.78/1.98  
% 11.78/1.98  cnf(c_11,negated_conjecture,
% 11.78/1.98      ( r1_xboole_0(sK3,sK1) ),
% 11.78/1.98      inference(cnf_transformation,[],[f36]) ).
% 11.78/1.98  
% 11.78/1.98  cnf(c_94,plain,
% 11.78/1.98      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
% 11.78/1.98      | sK3 != X0
% 11.78/1.98      | sK1 != X1 ),
% 11.78/1.98      inference(resolution_lifted,[status(thm)],[c_2,c_11]) ).
% 11.78/1.98  
% 11.78/1.98  cnf(c_95,plain,
% 11.78/1.98      ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)) = k1_xboole_0 ),
% 11.78/1.98      inference(unflattening,[status(thm)],[c_94]) ).
% 11.78/1.98  
% 11.78/1.98  cnf(c_8,plain,
% 11.78/1.98      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
% 11.78/1.98      inference(cnf_transformation,[],[f40]) ).
% 11.78/1.98  
% 11.78/1.98  cnf(c_836,plain,
% 11.78/1.98      ( k2_xboole_0(k1_xboole_0,k4_xboole_0(sK3,sK1)) = sK3 ),
% 11.78/1.98      inference(superposition,[status(thm)],[c_95,c_8]) ).
% 11.78/1.98  
% 11.78/1.98  cnf(c_1699,plain,
% 11.78/1.98      ( k4_xboole_0(sK3,sK1) = sK3 ),
% 11.78/1.98      inference(superposition,[status(thm)],[c_1052,c_836]) ).
% 11.78/1.98  
% 11.78/1.98  cnf(c_3379,plain,
% 11.78/1.98      ( r1_tarski(sK3,sK0) = iProver_top ),
% 11.78/1.98      inference(light_normalisation,[status(thm)],[c_2110,c_1699]) ).
% 11.78/1.98  
% 11.78/1.98  cnf(c_4,plain,
% 11.78/1.98      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 11.78/1.98      inference(cnf_transformation,[],[f27]) ).
% 11.78/1.98  
% 11.78/1.98  cnf(c_226,plain,
% 11.78/1.98      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 11.78/1.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 11.78/1.98  
% 11.78/1.98  cnf(c_3382,plain,
% 11.78/1.98      ( k2_xboole_0(sK3,sK0) = sK0 ),
% 11.78/1.98      inference(superposition,[status(thm)],[c_3379,c_226]) ).
% 11.78/1.98  
% 11.78/1.98  cnf(c_656,plain,
% 11.78/1.98      ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(X1,X0) ),
% 11.78/1.98      inference(superposition,[status(thm)],[c_0,c_6]) ).
% 11.78/1.98  
% 11.78/1.98  cnf(c_1,plain,
% 11.78/1.98      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 11.78/1.98      inference(cnf_transformation,[],[f38]) ).
% 11.78/1.98  
% 11.78/1.98  cnf(c_3053,plain,
% 11.78/1.98      ( k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
% 11.78/1.98      inference(superposition,[status(thm)],[c_656,c_1]) ).
% 11.78/1.98  
% 11.78/1.98  cnf(c_44216,plain,
% 11.78/1.98      ( k4_xboole_0(sK3,k4_xboole_0(sK3,k2_xboole_0(sK3,sK0))) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK3)) ),
% 11.78/1.98      inference(superposition,[status(thm)],[c_3382,c_3053]) ).
% 11.78/1.98  
% 11.78/1.98  cnf(c_44221,plain,
% 11.78/1.98      ( k4_xboole_0(sK0,sK0) = k4_xboole_0(sK3,sK0) ),
% 11.78/1.98      inference(superposition,[status(thm)],[c_3382,c_6]) ).
% 11.78/1.98  
% 11.78/1.98  cnf(c_1694,plain,
% 11.78/1.98      ( k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,X0) ),
% 11.78/1.98      inference(superposition,[status(thm)],[c_1052,c_6]) ).
% 11.78/1.98  
% 11.78/1.98  cnf(c_2810,plain,
% 11.78/1.98      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X0)) = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
% 11.78/1.98      inference(superposition,[status(thm)],[c_1694,c_1]) ).
% 11.78/1.98  
% 11.78/1.98  cnf(c_2813,plain,
% 11.78/1.98      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X0)) = k4_xboole_0(X0,X0) ),
% 11.78/1.98      inference(light_normalisation,[status(thm)],[c_2810,c_5]) ).
% 11.78/1.98  
% 11.78/1.98  cnf(c_834,plain,
% 11.78/1.98      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0)) = X1 ),
% 11.78/1.98      inference(superposition,[status(thm)],[c_1,c_8]) ).
% 11.78/1.98  
% 11.78/1.98  cnf(c_6649,plain,
% 11.78/1.98      ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(k4_xboole_0(X0,X0),k1_xboole_0)),k4_xboole_0(X0,X0)) = k1_xboole_0 ),
% 11.78/1.98      inference(superposition,[status(thm)],[c_2813,c_834]) ).
% 11.78/1.98  
% 11.78/1.98  cnf(c_846,plain,
% 11.78/1.98      ( k2_xboole_0(k4_xboole_0(X0,X0),X0) = X0 ),
% 11.78/1.98      inference(superposition,[status(thm)],[c_5,c_8]) ).
% 11.78/1.98  
% 11.78/1.98  cnf(c_6678,plain,
% 11.78/1.98      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 11.78/1.98      inference(demodulation,[status(thm)],[c_6649,c_5,c_846]) ).
% 11.78/1.98  
% 11.78/1.98  cnf(c_44250,plain,
% 11.78/1.98      ( k4_xboole_0(sK3,sK0) = k1_xboole_0 ),
% 11.78/1.98      inference(demodulation,[status(thm)],[c_44221,c_6678]) ).
% 11.78/1.98  
% 11.78/1.98  cnf(c_44265,plain,
% 11.78/1.98      ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK3)) = k4_xboole_0(sK3,k1_xboole_0) ),
% 11.78/1.98      inference(light_normalisation,
% 11.78/1.98                [status(thm)],
% 11.78/1.98                [c_44216,c_3382,c_44250]) ).
% 11.78/1.98  
% 11.78/1.98  cnf(c_12,negated_conjecture,
% 11.78/1.98      ( r1_xboole_0(sK2,sK0) ),
% 11.78/1.98      inference(cnf_transformation,[],[f35]) ).
% 11.78/1.98  
% 11.78/1.98  cnf(c_99,plain,
% 11.78/1.98      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
% 11.78/1.98      | sK0 != X1
% 11.78/1.98      | sK2 != X0 ),
% 11.78/1.98      inference(resolution_lifted,[status(thm)],[c_2,c_12]) ).
% 11.78/1.98  
% 11.78/1.98  cnf(c_100,plain,
% 11.78/1.98      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) = k1_xboole_0 ),
% 11.78/1.98      inference(unflattening,[status(thm)],[c_99]) ).
% 11.78/1.98  
% 11.78/1.98  cnf(c_837,plain,
% 11.78/1.98      ( k2_xboole_0(k1_xboole_0,k4_xboole_0(sK2,sK0)) = sK2 ),
% 11.78/1.98      inference(superposition,[status(thm)],[c_100,c_8]) ).
% 11.78/1.98  
% 11.78/1.98  cnf(c_1700,plain,
% 11.78/1.98      ( k4_xboole_0(sK2,sK0) = sK2 ),
% 11.78/1.98      inference(superposition,[status(thm)],[c_1052,c_837]) ).
% 11.78/1.98  
% 11.78/1.98  cnf(c_6657,plain,
% 11.78/1.98      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = X0 ),
% 11.78/1.98      inference(superposition,[status(thm)],[c_834,c_0]) ).
% 11.78/1.98  
% 11.78/1.98  cnf(c_24033,plain,
% 11.78/1.98      ( k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK2,sK2)) = sK0 ),
% 11.78/1.98      inference(superposition,[status(thm)],[c_1700,c_6657]) ).
% 11.78/1.98  
% 11.78/1.98  cnf(c_2450,plain,
% 11.78/1.98      ( k4_xboole_0(sK2,sK2) = k1_xboole_0 ),
% 11.78/1.98      inference(demodulation,[status(thm)],[c_1700,c_100]) ).
% 11.78/1.98  
% 11.78/1.98  cnf(c_24140,plain,
% 11.78/1.98      ( k2_xboole_0(k4_xboole_0(sK0,sK2),k1_xboole_0) = sK0 ),
% 11.78/1.98      inference(light_normalisation,[status(thm)],[c_24033,c_2450]) ).
% 11.78/1.98  
% 11.78/1.98  cnf(c_25116,plain,
% 11.78/1.98      ( k4_xboole_0(sK0,sK2) = sK0 ),
% 11.78/1.98      inference(superposition,[status(thm)],[c_24140,c_661]) ).
% 11.78/1.98  
% 11.78/1.98  cnf(c_633,plain,
% 11.78/1.98      ( r1_tarski(X0,k2_xboole_0(sK1,sK0)) != iProver_top
% 11.78/1.98      | r1_tarski(k4_xboole_0(X0,sK2),sK3) = iProver_top ),
% 11.78/1.98      inference(superposition,[status(thm)],[c_241,c_225]) ).
% 11.78/1.98  
% 11.78/1.98  cnf(c_1822,plain,
% 11.78/1.98      ( r1_tarski(k4_xboole_0(sK0,sK2),sK3) = iProver_top ),
% 11.78/1.98      inference(superposition,[status(thm)],[c_512,c_633]) ).
% 11.78/1.98  
% 11.78/1.98  cnf(c_3377,plain,
% 11.78/1.98      ( k2_xboole_0(k4_xboole_0(sK0,sK2),sK3) = sK3 ),
% 11.78/1.98      inference(superposition,[status(thm)],[c_1822,c_226]) ).
% 11.78/1.98  
% 11.78/1.98  cnf(c_12076,plain,
% 11.78/1.98      ( k4_xboole_0(k4_xboole_0(sK0,sK2),sK3) = k4_xboole_0(sK3,sK3) ),
% 11.78/1.98      inference(superposition,[status(thm)],[c_3377,c_6]) ).
% 11.78/1.98  
% 11.78/1.98  cnf(c_2210,plain,
% 11.78/1.98      ( k4_xboole_0(sK3,sK3) = k1_xboole_0 ),
% 11.78/1.98      inference(demodulation,[status(thm)],[c_1699,c_95]) ).
% 11.78/1.98  
% 11.78/1.98  cnf(c_12095,plain,
% 11.78/1.98      ( k4_xboole_0(k4_xboole_0(sK0,sK2),sK3) = k1_xboole_0 ),
% 11.78/1.98      inference(light_normalisation,[status(thm)],[c_12076,c_2210]) ).
% 11.78/1.98  
% 11.78/1.98  cnf(c_28685,plain,
% 11.78/1.98      ( k4_xboole_0(sK0,sK3) = k1_xboole_0 ),
% 11.78/1.98      inference(demodulation,[status(thm)],[c_25116,c_12095]) ).
% 11.78/1.98  
% 11.78/1.98  cnf(c_44267,plain,
% 11.78/1.98      ( k4_xboole_0(sK0,k1_xboole_0) = k4_xboole_0(sK3,k1_xboole_0) ),
% 11.78/1.98      inference(light_normalisation,[status(thm)],[c_44265,c_28685]) ).
% 11.78/1.98  
% 11.78/1.98  cnf(c_44268,plain,
% 11.78/1.98      ( sK0 = sK3 ),
% 11.78/1.98      inference(demodulation,[status(thm)],[c_44267,c_5]) ).
% 11.78/1.98  
% 11.78/1.98  cnf(c_44775,plain,
% 11.78/1.98      ( k4_xboole_0(sK2,sK3) = sK2 ),
% 11.78/1.98      inference(demodulation,[status(thm)],[c_44268,c_1700]) ).
% 11.78/1.98  
% 11.78/1.98  cnf(c_658,plain,
% 11.78/1.98      ( k4_xboole_0(k2_xboole_0(sK1,sK0),sK3) = k4_xboole_0(sK2,sK3) ),
% 11.78/1.98      inference(superposition,[status(thm)],[c_241,c_6]) ).
% 11.78/1.98  
% 11.78/1.98  cnf(c_44778,plain,
% 11.78/1.98      ( k4_xboole_0(k2_xboole_0(sK1,sK3),sK3) = k4_xboole_0(sK2,sK3) ),
% 11.78/1.98      inference(demodulation,[status(thm)],[c_44268,c_658]) ).
% 11.78/1.98  
% 11.78/1.98  cnf(c_821,plain,
% 11.78/1.98      ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) = k1_xboole_0 ),
% 11.78/1.98      inference(superposition,[status(thm)],[c_1,c_95]) ).
% 11.78/1.98  
% 11.78/1.98  cnf(c_1073,plain,
% 11.78/1.98      ( k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK3)) = sK1 ),
% 11.78/1.98      inference(superposition,[status(thm)],[c_821,c_8]) ).
% 11.78/1.98  
% 11.78/1.98  cnf(c_2767,plain,
% 11.78/1.98      ( k4_xboole_0(sK1,sK3) = sK1 ),
% 11.78/1.98      inference(superposition,[status(thm)],[c_1073,c_1052]) ).
% 11.78/1.98  
% 11.78/1.98  cnf(c_44786,plain,
% 11.78/1.98      ( k4_xboole_0(sK2,sK3) = sK1 ),
% 11.78/1.98      inference(demodulation,[status(thm)],[c_44778,c_6,c_2767]) ).
% 11.78/1.98  
% 11.78/1.98  cnf(c_44792,plain,
% 11.78/1.98      ( sK2 = sK1 ),
% 11.78/1.98      inference(light_normalisation,[status(thm)],[c_44775,c_44786]) ).
% 11.78/1.98  
% 11.78/1.98  cnf(c_141,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 11.78/1.98  
% 11.78/1.98  cnf(c_285,plain,
% 11.78/1.98      ( sK2 != X0 | sK1 != X0 | sK1 = sK2 ),
% 11.78/1.98      inference(instantiation,[status(thm)],[c_141]) ).
% 11.78/1.98  
% 11.78/1.98  cnf(c_286,plain,
% 11.78/1.98      ( sK2 != sK1 | sK1 = sK2 | sK1 != sK1 ),
% 11.78/1.98      inference(instantiation,[status(thm)],[c_285]) ).
% 11.78/1.98  
% 11.78/1.98  cnf(c_140,plain,( X0 = X0 ),theory(equality) ).
% 11.78/1.98  
% 11.78/1.98  cnf(c_148,plain,
% 11.78/1.98      ( sK1 = sK1 ),
% 11.78/1.98      inference(instantiation,[status(thm)],[c_140]) ).
% 11.78/1.98  
% 11.78/1.98  cnf(c_10,negated_conjecture,
% 11.78/1.98      ( sK1 != sK2 ),
% 11.78/1.98      inference(cnf_transformation,[],[f37]) ).
% 11.78/1.98  
% 11.78/1.98  cnf(contradiction,plain,
% 11.78/1.98      ( $false ),
% 11.78/1.98      inference(minisat,[status(thm)],[c_44792,c_286,c_148,c_10]) ).
% 11.78/1.98  
% 11.78/1.98  
% 11.78/1.98  % SZS output end CNFRefutation for theBenchmark.p
% 11.78/1.98  
% 11.78/1.98  ------                               Statistics
% 11.78/1.98  
% 11.78/1.98  ------ General
% 11.78/1.98  
% 11.78/1.98  abstr_ref_over_cycles:                  0
% 11.78/1.98  abstr_ref_under_cycles:                 0
% 11.78/1.98  gc_basic_clause_elim:                   0
% 11.78/1.98  forced_gc_time:                         0
% 11.78/1.98  parsing_time:                           0.01
% 11.78/1.98  unif_index_cands_time:                  0.
% 11.78/1.98  unif_index_add_time:                    0.
% 11.78/1.98  orderings_time:                         0.
% 11.78/1.98  out_proof_time:                         0.008
% 11.78/1.98  total_time:                             1.123
% 11.78/1.98  num_of_symbols:                         40
% 11.78/1.98  num_of_terms:                           41210
% 11.78/1.98  
% 11.78/1.98  ------ Preprocessing
% 11.78/1.98  
% 11.78/1.98  num_of_splits:                          0
% 11.78/1.98  num_of_split_atoms:                     0
% 11.78/1.98  num_of_reused_defs:                     0
% 11.78/1.98  num_eq_ax_congr_red:                    0
% 11.78/1.98  num_of_sem_filtered_clauses:            1
% 11.78/1.98  num_of_subtypes:                        0
% 11.78/1.98  monotx_restored_types:                  0
% 11.78/1.98  sat_num_of_epr_types:                   0
% 11.78/1.98  sat_num_of_non_cyclic_types:            0
% 11.78/1.98  sat_guarded_non_collapsed_types:        0
% 11.78/1.98  num_pure_diseq_elim:                    0
% 11.78/1.98  simp_replaced_by:                       0
% 11.78/1.98  res_preprocessed:                       64
% 11.78/1.98  prep_upred:                             0
% 11.78/1.98  prep_unflattend:                        4
% 11.78/1.98  smt_new_axioms:                         0
% 11.78/1.98  pred_elim_cands:                        1
% 11.78/1.98  pred_elim:                              1
% 11.78/1.98  pred_elim_cl:                           1
% 11.78/1.98  pred_elim_cycles:                       3
% 11.78/1.98  merged_defs:                            0
% 11.78/1.98  merged_defs_ncl:                        0
% 11.78/1.98  bin_hyper_res:                          0
% 11.78/1.98  prep_cycles:                            4
% 11.78/1.98  pred_elim_time:                         0.
% 11.78/1.98  splitting_time:                         0.
% 11.78/1.98  sem_filter_time:                        0.
% 11.78/1.98  monotx_time:                            0.001
% 11.78/1.98  subtype_inf_time:                       0.
% 11.78/1.98  
% 11.78/1.98  ------ Problem properties
% 11.78/1.98  
% 11.78/1.98  clauses:                                13
% 11.78/1.98  conjectures:                            2
% 11.78/1.98  epr:                                    1
% 11.78/1.98  horn:                                   13
% 11.78/1.98  ground:                                 4
% 11.78/1.98  unary:                                  10
% 11.78/1.98  binary:                                 3
% 11.78/1.98  lits:                                   16
% 11.78/1.98  lits_eq:                                10
% 11.78/1.98  fd_pure:                                0
% 11.78/1.98  fd_pseudo:                              0
% 11.78/1.98  fd_cond:                                0
% 11.78/1.98  fd_pseudo_cond:                         0
% 11.78/1.98  ac_symbols:                             0
% 11.78/1.98  
% 11.78/1.98  ------ Propositional Solver
% 11.78/1.98  
% 11.78/1.98  prop_solver_calls:                      30
% 11.78/1.98  prop_fast_solver_calls:                 535
% 11.78/1.98  smt_solver_calls:                       0
% 11.78/1.98  smt_fast_solver_calls:                  0
% 11.78/1.98  prop_num_of_clauses:                    16000
% 11.78/1.98  prop_preprocess_simplified:             26113
% 11.78/1.98  prop_fo_subsumed:                       1
% 11.78/1.98  prop_solver_time:                       0.
% 11.78/1.98  smt_solver_time:                        0.
% 11.78/1.98  smt_fast_solver_time:                   0.
% 11.78/1.98  prop_fast_solver_time:                  0.
% 11.78/1.98  prop_unsat_core_time:                   0.002
% 11.78/1.98  
% 11.78/1.98  ------ QBF
% 11.78/1.98  
% 11.78/1.98  qbf_q_res:                              0
% 11.78/1.98  qbf_num_tautologies:                    0
% 11.78/1.98  qbf_prep_cycles:                        0
% 11.78/1.98  
% 11.78/1.98  ------ BMC1
% 11.78/1.98  
% 11.78/1.98  bmc1_current_bound:                     -1
% 11.78/1.98  bmc1_last_solved_bound:                 -1
% 11.78/1.98  bmc1_unsat_core_size:                   -1
% 11.78/1.98  bmc1_unsat_core_parents_size:           -1
% 11.78/1.98  bmc1_merge_next_fun:                    0
% 11.78/1.98  bmc1_unsat_core_clauses_time:           0.
% 11.78/1.98  
% 11.78/1.98  ------ Instantiation
% 11.78/1.98  
% 11.78/1.98  inst_num_of_clauses:                    4789
% 11.78/1.98  inst_num_in_passive:                    1940
% 11.78/1.98  inst_num_in_active:                     1254
% 11.78/1.98  inst_num_in_unprocessed:                1597
% 11.78/1.98  inst_num_of_loops:                      1330
% 11.78/1.98  inst_num_of_learning_restarts:          0
% 11.78/1.98  inst_num_moves_active_passive:          69
% 11.78/1.98  inst_lit_activity:                      0
% 11.78/1.98  inst_lit_activity_moves:                0
% 11.78/1.98  inst_num_tautologies:                   0
% 11.78/1.98  inst_num_prop_implied:                  0
% 11.78/1.98  inst_num_existing_simplified:           0
% 11.78/1.98  inst_num_eq_res_simplified:             0
% 11.78/1.98  inst_num_child_elim:                    0
% 11.78/1.98  inst_num_of_dismatching_blockings:      6156
% 11.78/1.98  inst_num_of_non_proper_insts:           5585
% 11.78/1.98  inst_num_of_duplicates:                 0
% 11.78/1.98  inst_inst_num_from_inst_to_res:         0
% 11.78/1.98  inst_dismatching_checking_time:         0.
% 11.78/1.98  
% 11.78/1.98  ------ Resolution
% 11.78/1.98  
% 11.78/1.98  res_num_of_clauses:                     0
% 11.78/1.98  res_num_in_passive:                     0
% 11.78/1.98  res_num_in_active:                      0
% 11.78/1.98  res_num_of_loops:                       68
% 11.78/1.98  res_forward_subset_subsumed:            502
% 11.78/1.98  res_backward_subset_subsumed:           24
% 11.78/1.98  res_forward_subsumed:                   0
% 11.78/1.98  res_backward_subsumed:                  0
% 11.78/1.98  res_forward_subsumption_resolution:     0
% 11.78/1.98  res_backward_subsumption_resolution:    0
% 11.78/1.98  res_clause_to_clause_subsumption:       7096
% 11.78/1.98  res_orphan_elimination:                 0
% 11.78/1.98  res_tautology_del:                      184
% 11.78/1.98  res_num_eq_res_simplified:              0
% 11.78/1.98  res_num_sel_changes:                    0
% 11.78/1.98  res_moves_from_active_to_pass:          0
% 11.78/1.98  
% 11.78/1.98  ------ Superposition
% 11.78/1.98  
% 11.78/1.98  sup_time_total:                         0.
% 11.78/1.98  sup_time_generating:                    0.
% 11.78/1.98  sup_time_sim_full:                      0.
% 11.78/1.98  sup_time_sim_immed:                     0.
% 11.78/1.98  
% 11.78/1.98  sup_num_of_clauses:                     1076
% 11.78/1.98  sup_num_in_active:                      102
% 11.78/1.98  sup_num_in_passive:                     974
% 11.78/1.98  sup_num_of_loops:                       264
% 11.78/1.98  sup_fw_superposition:                   1491
% 11.78/1.98  sup_bw_superposition:                   2630
% 11.78/1.98  sup_immediate_simplified:               1964
% 11.78/1.98  sup_given_eliminated:                   15
% 11.78/1.98  comparisons_done:                       0
% 11.78/1.98  comparisons_avoided:                    0
% 11.78/1.98  
% 11.78/1.98  ------ Simplifications
% 11.78/1.98  
% 11.78/1.98  
% 11.78/1.98  sim_fw_subset_subsumed:                 74
% 11.78/1.98  sim_bw_subset_subsumed:                 0
% 11.78/1.98  sim_fw_subsumed:                        294
% 11.78/1.98  sim_bw_subsumed:                        13
% 11.78/1.98  sim_fw_subsumption_res:                 0
% 11.78/1.98  sim_bw_subsumption_res:                 0
% 11.78/1.98  sim_tautology_del:                      58
% 11.78/1.98  sim_eq_tautology_del:                   401
% 11.78/1.98  sim_eq_res_simp:                        0
% 11.78/1.98  sim_fw_demodulated:                     702
% 11.78/1.98  sim_bw_demodulated:                     227
% 11.78/1.98  sim_light_normalised:                   1188
% 11.78/1.98  sim_joinable_taut:                      0
% 11.78/1.98  sim_joinable_simp:                      0
% 11.78/1.98  sim_ac_normalised:                      0
% 11.78/1.98  sim_smt_subsumption:                    0
% 11.78/1.98  
%------------------------------------------------------------------------------
