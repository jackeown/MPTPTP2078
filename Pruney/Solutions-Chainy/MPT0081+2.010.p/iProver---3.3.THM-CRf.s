%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:24:04 EST 2020

% Result     : Theorem 3.71s
% Output     : CNFRefutation 3.71s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 539 expanded)
%              Number of clauses        :   62 ( 174 expanded)
%              Number of leaves         :   11 ( 137 expanded)
%              Depth                    :   22
%              Number of atoms          :  128 ( 773 expanded)
%              Number of equality atoms :   92 ( 484 expanded)
%              Maximal formula depth    :    8 (   2 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f32,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f20,f25])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f31,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f19,f25])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f33,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f24,f25])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f17,f25])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ~ ( r1_xboole_0(X0,X1)
        & ~ r1_xboole_0(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k3_xboole_0(X1,X2)) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
      & ~ r1_xboole_0(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f15,plain,
    ( ? [X0,X1,X2] :
        ( r1_xboole_0(X0,X1)
        & ~ r1_xboole_0(X0,k3_xboole_0(X1,X2)) )
   => ( r1_xboole_0(sK0,sK1)
      & ~ r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( r1_xboole_0(sK0,sK1)
    & ~ r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f15])).

fof(f28,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f34,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(definition_unfolding,[],[f26,f25])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X0))
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k4_xboole_0(X1,X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k4_xboole_0(X1,X0)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f18,f25])).

fof(f27,plain,(
    ~ r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f16])).

fof(f35,plain,(
    ~ r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
    inference(definition_unfolding,[],[f27,f25])).

cnf(c_3,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_2,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) = X0 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_7,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_486,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_2,c_7])).

cnf(c_6,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_1372,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X0,X1),X2)) = k4_xboole_0(k4_xboole_0(X0,X0),X2) ),
    inference(superposition,[status(thm)],[c_486,c_6])).

cnf(c_1398,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X0,X1),X2)) = k4_xboole_0(X0,X0) ),
    inference(demodulation,[status(thm)],[c_1372,c_6,c_486])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_59,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_1])).

cnf(c_9,negated_conjecture,
    ( r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_114,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
    | sK1 != X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_59,c_9])).

cnf(c_115,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_114])).

cnf(c_491,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k1_xboole_0)) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_115,c_7])).

cnf(c_507,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k1_xboole_0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_491,c_115])).

cnf(c_8,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_668,plain,
    ( k2_xboole_0(k4_xboole_0(sK0,X0),k1_xboole_0) = k4_xboole_0(sK0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_507,c_8])).

cnf(c_4939,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(k2_xboole_0(k2_xboole_0(sK0,X0),X1),k1_xboole_0)) = k2_xboole_0(k4_xboole_0(sK0,sK0),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1398,c_668])).

cnf(c_4947,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(k2_xboole_0(k2_xboole_0(sK0,X0),X1),k1_xboole_0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4939,c_507,c_668])).

cnf(c_426,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_3,c_2])).

cnf(c_891,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X0),X1)) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_426,c_6])).

cnf(c_536,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X0,X2))) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_2,c_8])).

cnf(c_898,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_426,c_8])).

cnf(c_8195,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_536,c_898])).

cnf(c_8213,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,k4_xboole_0(X0,X0))) = k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_891,c_8195])).

cnf(c_8346,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,X1)) = k4_xboole_0(k4_xboole_0(X0,X0),X0) ),
    inference(light_normalisation,[status(thm)],[c_8213,c_426])).

cnf(c_422,plain,
    ( k2_xboole_0(X0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_2,c_3])).

cnf(c_8347,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,X1)) = k4_xboole_0(X0,X0) ),
    inference(demodulation,[status(thm)],[c_8346,c_6,c_422])).

cnf(c_9816,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,sK0),k1_xboole_0) = k4_xboole_0(sK0,sK0) ),
    inference(superposition,[status(thm)],[c_4947,c_8347])).

cnf(c_10488,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,sK0),k2_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(k4_xboole_0(sK0,sK0),X0) ),
    inference(superposition,[status(thm)],[c_9816,c_6])).

cnf(c_10503,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,sK0),k2_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(sK0,sK0) ),
    inference(demodulation,[status(thm)],[c_10488,c_6,c_486])).

cnf(c_423,plain,
    ( k2_xboole_0(sK0,k1_xboole_0) = sK0 ),
    inference(superposition,[status(thm)],[c_115,c_3])).

cnf(c_617,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK0)) = sK0 ),
    inference(superposition,[status(thm)],[c_423,c_2])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,k4_xboole_0(X1,X0))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f22])).

cnf(c_357,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k4_xboole_0(X1,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_835,plain,
    ( k4_xboole_0(sK0,sK0) = k1_xboole_0
    | r1_tarski(k4_xboole_0(sK0,sK0),sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_617,c_357])).

cnf(c_4,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_358,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_10590,plain,
    ( k4_xboole_0(sK0,sK0) = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_835,c_358])).

cnf(c_11955,plain,
    ( k4_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_10503,c_10590])).

cnf(c_11978,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k2_xboole_0(k1_xboole_0,X0),X1)) = k2_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))) ),
    inference(superposition,[status(thm)],[c_11955,c_8])).

cnf(c_12040,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k2_xboole_0(k1_xboole_0,X0),X1)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_11978,c_3])).

cnf(c_12147,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3,c_12040])).

cnf(c_12960,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_12147,c_7])).

cnf(c_663,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,k1_xboole_0),X0)) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_507,c_6])).

cnf(c_752,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(k1_xboole_0,X0))) = k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,k1_xboole_0),X0)) ),
    inference(superposition,[status(thm)],[c_663,c_7])).

cnf(c_769,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(k1_xboole_0,X0))) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(light_normalisation,[status(thm)],[c_752,c_663])).

cnf(c_488,plain,
    ( k4_xboole_0(sK0,k1_xboole_0) = k4_xboole_0(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_115,c_7])).

cnf(c_636,plain,
    ( k2_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(sK0,k4_xboole_0(sK0,X0))) = k4_xboole_0(sK0,k4_xboole_0(sK1,X0)) ),
    inference(superposition,[status(thm)],[c_488,c_8])).

cnf(c_653,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(sK0,k4_xboole_0(sK1,X0)) ),
    inference(demodulation,[status(thm)],[c_636,c_8])).

cnf(c_0,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_57,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_0])).

cnf(c_10,negated_conjecture,
    ( ~ r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_119,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0
    | k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) != X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_57,c_10])).

cnf(c_120,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_119])).

cnf(c_2722,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK2)))) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_653,c_120])).

cnf(c_4248,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK2)) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_769,c_2722])).

cnf(c_13245,plain,
    ( k4_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_12960,c_4248])).

cnf(c_895,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0
    | r1_tarski(k4_xboole_0(X0,X0),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_426,c_357])).

cnf(c_921,plain,
    ( k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | r1_tarski(k4_xboole_0(k1_xboole_0,k1_xboole_0),k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_895])).

cnf(c_19,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_21,plain,
    ( r1_tarski(k4_xboole_0(k1_xboole_0,k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_13245,c_921,c_21])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:03:59 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 3.71/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.71/1.01  
% 3.71/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.71/1.01  
% 3.71/1.01  ------  iProver source info
% 3.71/1.01  
% 3.71/1.01  git: date: 2020-06-30 10:37:57 +0100
% 3.71/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.71/1.01  git: non_committed_changes: false
% 3.71/1.01  git: last_make_outside_of_git: false
% 3.71/1.01  
% 3.71/1.01  ------ 
% 3.71/1.01  ------ Parsing...
% 3.71/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.71/1.01  
% 3.71/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.71/1.01  
% 3.71/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.71/1.01  
% 3.71/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.71/1.01  ------ Proving...
% 3.71/1.01  ------ Problem Properties 
% 3.71/1.01  
% 3.71/1.01  
% 3.71/1.01  clauses                                 10
% 3.71/1.01  conjectures                             0
% 3.71/1.01  EPR                                     0
% 3.71/1.01  Horn                                    10
% 3.71/1.01  unary                                   9
% 3.71/1.01  binary                                  1
% 3.71/1.01  lits                                    11
% 3.71/1.01  lits eq                                 9
% 3.71/1.01  fd_pure                                 0
% 3.71/1.01  fd_pseudo                               0
% 3.71/1.01  fd_cond                                 1
% 3.71/1.01  fd_pseudo_cond                          0
% 3.71/1.01  AC symbols                              0
% 3.71/1.01  
% 3.71/1.01  ------ Input Options Time Limit: Unbounded
% 3.71/1.01  
% 3.71/1.01  
% 3.71/1.01  
% 3.71/1.01  
% 3.71/1.01  ------ Preprocessing...
% 3.71/1.01  
% 3.71/1.01  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 3.71/1.01  Current options:
% 3.71/1.01  ------ 
% 3.71/1.01  
% 3.71/1.01  
% 3.71/1.01  
% 3.71/1.01  
% 3.71/1.01  ------ Proving...
% 3.71/1.01  
% 3.71/1.01  
% 3.71/1.01  ------ Preprocessing...
% 3.71/1.01  
% 3.71/1.01  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.71/1.01  
% 3.71/1.01  ------ Proving...
% 3.71/1.01  
% 3.71/1.01  
% 3.71/1.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.71/1.01  
% 3.71/1.01  ------ Proving...
% 3.71/1.01  
% 3.71/1.01  
% 3.71/1.01  ------ Preprocessing...
% 3.71/1.01  
% 3.71/1.01  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.71/1.01  
% 3.71/1.01  ------ Proving...
% 3.71/1.01  
% 3.71/1.01  
% 3.71/1.01  ------ Preprocessing...
% 3.71/1.01  
% 3.71/1.01  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.71/1.01  
% 3.71/1.01  ------ Proving...
% 3.71/1.01  
% 3.71/1.01  
% 3.71/1.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.71/1.01  
% 3.71/1.01  ------ Proving...
% 3.71/1.01  
% 3.71/1.01  
% 3.71/1.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.71/1.01  
% 3.71/1.01  ------ Proving...
% 3.71/1.01  
% 3.71/1.01  
% 3.71/1.01  % SZS status Theorem for theBenchmark.p
% 3.71/1.01  
% 3.71/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 3.71/1.01  
% 3.71/1.01  fof(f3,axiom,(
% 3.71/1.01    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 3.71/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/1.01  
% 3.71/1.01  fof(f20,plain,(
% 3.71/1.01    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 3.71/1.01    inference(cnf_transformation,[],[f3])).
% 3.71/1.01  
% 3.71/1.01  fof(f8,axiom,(
% 3.71/1.01    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.71/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/1.01  
% 3.71/1.01  fof(f25,plain,(
% 3.71/1.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.71/1.01    inference(cnf_transformation,[],[f8])).
% 3.71/1.01  
% 3.71/1.01  fof(f32,plain,(
% 3.71/1.01    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0) )),
% 3.71/1.01    inference(definition_unfolding,[],[f20,f25])).
% 3.71/1.01  
% 3.71/1.01  fof(f2,axiom,(
% 3.71/1.01    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 3.71/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/1.01  
% 3.71/1.01  fof(f19,plain,(
% 3.71/1.01    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 3.71/1.01    inference(cnf_transformation,[],[f2])).
% 3.71/1.01  
% 3.71/1.01  fof(f31,plain,(
% 3.71/1.01    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) = X0) )),
% 3.71/1.01    inference(definition_unfolding,[],[f19,f25])).
% 3.71/1.01  
% 3.71/1.01  fof(f7,axiom,(
% 3.71/1.01    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.71/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/1.01  
% 3.71/1.01  fof(f24,plain,(
% 3.71/1.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.71/1.01    inference(cnf_transformation,[],[f7])).
% 3.71/1.01  
% 3.71/1.01  fof(f33,plain,(
% 3.71/1.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 3.71/1.01    inference(definition_unfolding,[],[f24,f25])).
% 3.71/1.01  
% 3.71/1.01  fof(f6,axiom,(
% 3.71/1.01    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 3.71/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/1.01  
% 3.71/1.01  fof(f23,plain,(
% 3.71/1.01    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 3.71/1.01    inference(cnf_transformation,[],[f6])).
% 3.71/1.01  
% 3.71/1.01  fof(f1,axiom,(
% 3.71/1.01    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 3.71/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/1.01  
% 3.71/1.01  fof(f14,plain,(
% 3.71/1.01    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 3.71/1.01    inference(nnf_transformation,[],[f1])).
% 3.71/1.01  
% 3.71/1.01  fof(f17,plain,(
% 3.71/1.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 3.71/1.01    inference(cnf_transformation,[],[f14])).
% 3.71/1.01  
% 3.71/1.01  fof(f30,plain,(
% 3.71/1.01    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 3.71/1.01    inference(definition_unfolding,[],[f17,f25])).
% 3.71/1.01  
% 3.71/1.01  fof(f10,conjecture,(
% 3.71/1.01    ! [X0,X1,X2] : ~(r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k3_xboole_0(X1,X2)))),
% 3.71/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/1.01  
% 3.71/1.01  fof(f11,negated_conjecture,(
% 3.71/1.01    ~! [X0,X1,X2] : ~(r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k3_xboole_0(X1,X2)))),
% 3.71/1.01    inference(negated_conjecture,[],[f10])).
% 3.71/1.01  
% 3.71/1.01  fof(f13,plain,(
% 3.71/1.01    ? [X0,X1,X2] : (r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k3_xboole_0(X1,X2)))),
% 3.71/1.01    inference(ennf_transformation,[],[f11])).
% 3.71/1.01  
% 3.71/1.01  fof(f15,plain,(
% 3.71/1.01    ? [X0,X1,X2] : (r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k3_xboole_0(X1,X2))) => (r1_xboole_0(sK0,sK1) & ~r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)))),
% 3.71/1.01    introduced(choice_axiom,[])).
% 3.71/1.01  
% 3.71/1.01  fof(f16,plain,(
% 3.71/1.01    r1_xboole_0(sK0,sK1) & ~r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))),
% 3.71/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f15])).
% 3.71/1.01  
% 3.71/1.01  fof(f28,plain,(
% 3.71/1.01    r1_xboole_0(sK0,sK1)),
% 3.71/1.01    inference(cnf_transformation,[],[f16])).
% 3.71/1.01  
% 3.71/1.01  fof(f9,axiom,(
% 3.71/1.01    ! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,X2))),
% 3.71/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/1.01  
% 3.71/1.01  fof(f26,plain,(
% 3.71/1.01    ( ! [X2,X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,X2))) )),
% 3.71/1.01    inference(cnf_transformation,[],[f9])).
% 3.71/1.01  
% 3.71/1.01  fof(f34,plain,(
% 3.71/1.01    ( ! [X2,X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(X1,X2))) )),
% 3.71/1.01    inference(definition_unfolding,[],[f26,f25])).
% 3.71/1.01  
% 3.71/1.01  fof(f5,axiom,(
% 3.71/1.01    ! [X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X0)) => k1_xboole_0 = X0)),
% 3.71/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/1.01  
% 3.71/1.01  fof(f12,plain,(
% 3.71/1.01    ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k4_xboole_0(X1,X0)))),
% 3.71/1.01    inference(ennf_transformation,[],[f5])).
% 3.71/1.01  
% 3.71/1.01  fof(f22,plain,(
% 3.71/1.01    ( ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k4_xboole_0(X1,X0))) )),
% 3.71/1.01    inference(cnf_transformation,[],[f12])).
% 3.71/1.01  
% 3.71/1.01  fof(f4,axiom,(
% 3.71/1.01    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 3.71/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/1.01  
% 3.71/1.01  fof(f21,plain,(
% 3.71/1.01    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 3.71/1.01    inference(cnf_transformation,[],[f4])).
% 3.71/1.01  
% 3.71/1.01  fof(f18,plain,(
% 3.71/1.01    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 3.71/1.01    inference(cnf_transformation,[],[f14])).
% 3.71/1.01  
% 3.71/1.01  fof(f29,plain,(
% 3.71/1.01    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.71/1.01    inference(definition_unfolding,[],[f18,f25])).
% 3.71/1.01  
% 3.71/1.01  fof(f27,plain,(
% 3.71/1.01    ~r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))),
% 3.71/1.01    inference(cnf_transformation,[],[f16])).
% 3.71/1.01  
% 3.71/1.01  fof(f35,plain,(
% 3.71/1.01    ~r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))),
% 3.71/1.01    inference(definition_unfolding,[],[f27,f25])).
% 3.71/1.01  
% 3.71/1.01  cnf(c_3,plain,
% 3.71/1.01      ( k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
% 3.71/1.01      inference(cnf_transformation,[],[f32]) ).
% 3.71/1.01  
% 3.71/1.01  cnf(c_2,plain,
% 3.71/1.01      ( k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) = X0 ),
% 3.71/1.01      inference(cnf_transformation,[],[f31]) ).
% 3.71/1.01  
% 3.71/1.01  cnf(c_7,plain,
% 3.71/1.01      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 3.71/1.01      inference(cnf_transformation,[],[f33]) ).
% 3.71/1.01  
% 3.71/1.01  cnf(c_486,plain,
% 3.71/1.01      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(X0,X0) ),
% 3.71/1.01      inference(superposition,[status(thm)],[c_2,c_7]) ).
% 3.71/1.01  
% 3.71/1.01  cnf(c_6,plain,
% 3.71/1.01      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 3.71/1.01      inference(cnf_transformation,[],[f23]) ).
% 3.71/1.01  
% 3.71/1.01  cnf(c_1372,plain,
% 3.71/1.01      ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X0,X1),X2)) = k4_xboole_0(k4_xboole_0(X0,X0),X2) ),
% 3.71/1.01      inference(superposition,[status(thm)],[c_486,c_6]) ).
% 3.71/1.01  
% 3.71/1.01  cnf(c_1398,plain,
% 3.71/1.01      ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X0,X1),X2)) = k4_xboole_0(X0,X0) ),
% 3.71/1.01      inference(demodulation,[status(thm)],[c_1372,c_6,c_486]) ).
% 3.71/1.01  
% 3.71/1.01  cnf(c_1,plain,
% 3.71/1.01      ( ~ r1_xboole_0(X0,X1)
% 3.71/1.01      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 3.71/1.01      inference(cnf_transformation,[],[f30]) ).
% 3.71/1.01  
% 3.71/1.01  cnf(c_59,plain,
% 3.71/1.01      ( ~ r1_xboole_0(X0,X1)
% 3.71/1.01      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 3.71/1.01      inference(prop_impl,[status(thm)],[c_1]) ).
% 3.71/1.01  
% 3.71/1.01  cnf(c_9,negated_conjecture,
% 3.71/1.01      ( r1_xboole_0(sK0,sK1) ),
% 3.71/1.01      inference(cnf_transformation,[],[f28]) ).
% 3.71/1.01  
% 3.71/1.01  cnf(c_114,plain,
% 3.71/1.01      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
% 3.71/1.01      | sK1 != X1
% 3.71/1.01      | sK0 != X0 ),
% 3.71/1.01      inference(resolution_lifted,[status(thm)],[c_59,c_9]) ).
% 3.71/1.01  
% 3.71/1.01  cnf(c_115,plain,
% 3.71/1.01      ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k1_xboole_0 ),
% 3.71/1.01      inference(unflattening,[status(thm)],[c_114]) ).
% 3.71/1.01  
% 3.71/1.01  cnf(c_491,plain,
% 3.71/1.01      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k1_xboole_0)) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
% 3.71/1.01      inference(superposition,[status(thm)],[c_115,c_7]) ).
% 3.71/1.01  
% 3.71/1.01  cnf(c_507,plain,
% 3.71/1.01      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k1_xboole_0)) = k1_xboole_0 ),
% 3.71/1.01      inference(light_normalisation,[status(thm)],[c_491,c_115]) ).
% 3.71/1.01  
% 3.71/1.01  cnf(c_8,plain,
% 3.71/1.01      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 3.71/1.01      inference(cnf_transformation,[],[f34]) ).
% 3.71/1.01  
% 3.71/1.01  cnf(c_668,plain,
% 3.71/1.01      ( k2_xboole_0(k4_xboole_0(sK0,X0),k1_xboole_0) = k4_xboole_0(sK0,k4_xboole_0(X0,k1_xboole_0)) ),
% 3.71/1.01      inference(superposition,[status(thm)],[c_507,c_8]) ).
% 3.71/1.01  
% 3.71/1.01  cnf(c_4939,plain,
% 3.71/1.01      ( k4_xboole_0(sK0,k4_xboole_0(k2_xboole_0(k2_xboole_0(sK0,X0),X1),k1_xboole_0)) = k2_xboole_0(k4_xboole_0(sK0,sK0),k1_xboole_0) ),
% 3.71/1.01      inference(superposition,[status(thm)],[c_1398,c_668]) ).
% 3.71/1.01  
% 3.71/1.01  cnf(c_4947,plain,
% 3.71/1.01      ( k4_xboole_0(sK0,k4_xboole_0(k2_xboole_0(k2_xboole_0(sK0,X0),X1),k1_xboole_0)) = k1_xboole_0 ),
% 3.71/1.01      inference(demodulation,[status(thm)],[c_4939,c_507,c_668]) ).
% 3.71/1.01  
% 3.71/1.01  cnf(c_426,plain,
% 3.71/1.01      ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
% 3.71/1.01      inference(superposition,[status(thm)],[c_3,c_2]) ).
% 3.71/1.01  
% 3.71/1.01  cnf(c_891,plain,
% 3.71/1.01      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X0),X1)) = k4_xboole_0(X0,X1) ),
% 3.71/1.01      inference(superposition,[status(thm)],[c_426,c_6]) ).
% 3.71/1.01  
% 3.71/1.01  cnf(c_536,plain,
% 3.71/1.01      ( k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X0,X2))) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 3.71/1.01      inference(superposition,[status(thm)],[c_2,c_8]) ).
% 3.71/1.01  
% 3.71/1.01  cnf(c_898,plain,
% 3.71/1.01      ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 3.71/1.01      inference(superposition,[status(thm)],[c_426,c_8]) ).
% 3.71/1.01  
% 3.71/1.01  cnf(c_8195,plain,
% 3.71/1.01      ( k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 3.71/1.01      inference(light_normalisation,[status(thm)],[c_536,c_898]) ).
% 3.71/1.01  
% 3.71/1.01  cnf(c_8213,plain,
% 3.71/1.01      ( k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,k4_xboole_0(X0,X0))) = k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,X1)) ),
% 3.71/1.01      inference(superposition,[status(thm)],[c_891,c_8195]) ).
% 3.71/1.01  
% 3.71/1.01  cnf(c_8346,plain,
% 3.71/1.01      ( k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,X1)) = k4_xboole_0(k4_xboole_0(X0,X0),X0) ),
% 3.71/1.01      inference(light_normalisation,[status(thm)],[c_8213,c_426]) ).
% 3.71/1.01  
% 3.71/1.01  cnf(c_422,plain,
% 3.71/1.01      ( k2_xboole_0(X0,X0) = X0 ),
% 3.71/1.01      inference(superposition,[status(thm)],[c_2,c_3]) ).
% 3.71/1.01  
% 3.71/1.01  cnf(c_8347,plain,
% 3.71/1.01      ( k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,X1)) = k4_xboole_0(X0,X0) ),
% 3.71/1.01      inference(demodulation,[status(thm)],[c_8346,c_6,c_422]) ).
% 3.71/1.01  
% 3.71/1.01  cnf(c_9816,plain,
% 3.71/1.01      ( k4_xboole_0(k4_xboole_0(sK0,sK0),k1_xboole_0) = k4_xboole_0(sK0,sK0) ),
% 3.71/1.01      inference(superposition,[status(thm)],[c_4947,c_8347]) ).
% 3.71/1.01  
% 3.71/1.01  cnf(c_10488,plain,
% 3.71/1.01      ( k4_xboole_0(k4_xboole_0(sK0,sK0),k2_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(k4_xboole_0(sK0,sK0),X0) ),
% 3.71/1.01      inference(superposition,[status(thm)],[c_9816,c_6]) ).
% 3.71/1.01  
% 3.71/1.01  cnf(c_10503,plain,
% 3.71/1.01      ( k4_xboole_0(k4_xboole_0(sK0,sK0),k2_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(sK0,sK0) ),
% 3.71/1.01      inference(demodulation,[status(thm)],[c_10488,c_6,c_486]) ).
% 3.71/1.01  
% 3.71/1.01  cnf(c_423,plain,
% 3.71/1.01      ( k2_xboole_0(sK0,k1_xboole_0) = sK0 ),
% 3.71/1.01      inference(superposition,[status(thm)],[c_115,c_3]) ).
% 3.71/1.01  
% 3.71/1.01  cnf(c_617,plain,
% 3.71/1.01      ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK0)) = sK0 ),
% 3.71/1.01      inference(superposition,[status(thm)],[c_423,c_2]) ).
% 3.71/1.01  
% 3.71/1.01  cnf(c_5,plain,
% 3.71/1.01      ( ~ r1_tarski(X0,k4_xboole_0(X1,X0)) | k1_xboole_0 = X0 ),
% 3.71/1.01      inference(cnf_transformation,[],[f22]) ).
% 3.71/1.01  
% 3.71/1.01  cnf(c_357,plain,
% 3.71/1.01      ( k1_xboole_0 = X0
% 3.71/1.01      | r1_tarski(X0,k4_xboole_0(X1,X0)) != iProver_top ),
% 3.71/1.01      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.71/1.01  
% 3.71/1.01  cnf(c_835,plain,
% 3.71/1.01      ( k4_xboole_0(sK0,sK0) = k1_xboole_0
% 3.71/1.01      | r1_tarski(k4_xboole_0(sK0,sK0),sK0) != iProver_top ),
% 3.71/1.01      inference(superposition,[status(thm)],[c_617,c_357]) ).
% 3.71/1.01  
% 3.71/1.01  cnf(c_4,plain,
% 3.71/1.01      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 3.71/1.01      inference(cnf_transformation,[],[f21]) ).
% 3.71/1.01  
% 3.71/1.01  cnf(c_358,plain,
% 3.71/1.01      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 3.71/1.01      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.71/1.01  
% 3.71/1.01  cnf(c_10590,plain,
% 3.71/1.01      ( k4_xboole_0(sK0,sK0) = k1_xboole_0 ),
% 3.71/1.01      inference(forward_subsumption_resolution,
% 3.71/1.01                [status(thm)],
% 3.71/1.01                [c_835,c_358]) ).
% 3.71/1.01  
% 3.71/1.01  cnf(c_11955,plain,
% 3.71/1.01      ( k4_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
% 3.71/1.01      inference(light_normalisation,[status(thm)],[c_10503,c_10590]) ).
% 3.71/1.01  
% 3.71/1.01  cnf(c_11978,plain,
% 3.71/1.01      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k2_xboole_0(k1_xboole_0,X0),X1)) = k2_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))) ),
% 3.71/1.01      inference(superposition,[status(thm)],[c_11955,c_8]) ).
% 3.71/1.01  
% 3.71/1.01  cnf(c_12040,plain,
% 3.71/1.01      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k2_xboole_0(k1_xboole_0,X0),X1)) = k1_xboole_0 ),
% 3.71/1.01      inference(demodulation,[status(thm)],[c_11978,c_3]) ).
% 3.71/1.01  
% 3.71/1.01  cnf(c_12147,plain,
% 3.71/1.01      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
% 3.71/1.01      inference(superposition,[status(thm)],[c_3,c_12040]) ).
% 3.71/1.01  
% 3.71/1.01  cnf(c_12960,plain,
% 3.71/1.01      ( k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 3.71/1.01      inference(superposition,[status(thm)],[c_12147,c_7]) ).
% 3.71/1.01  
% 3.71/1.01  cnf(c_663,plain,
% 3.71/1.01      ( k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,k1_xboole_0),X0)) = k4_xboole_0(k1_xboole_0,X0) ),
% 3.71/1.01      inference(superposition,[status(thm)],[c_507,c_6]) ).
% 3.71/1.01  
% 3.71/1.01  cnf(c_752,plain,
% 3.71/1.01      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(k1_xboole_0,X0))) = k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,k1_xboole_0),X0)) ),
% 3.71/1.01      inference(superposition,[status(thm)],[c_663,c_7]) ).
% 3.71/1.01  
% 3.71/1.01  cnf(c_769,plain,
% 3.71/1.01      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(k1_xboole_0,X0))) = k4_xboole_0(k1_xboole_0,X0) ),
% 3.71/1.01      inference(light_normalisation,[status(thm)],[c_752,c_663]) ).
% 3.71/1.01  
% 3.71/1.01  cnf(c_488,plain,
% 3.71/1.01      ( k4_xboole_0(sK0,k1_xboole_0) = k4_xboole_0(sK0,sK1) ),
% 3.71/1.01      inference(superposition,[status(thm)],[c_115,c_7]) ).
% 3.71/1.01  
% 3.71/1.01  cnf(c_636,plain,
% 3.71/1.01      ( k2_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(sK0,k4_xboole_0(sK0,X0))) = k4_xboole_0(sK0,k4_xboole_0(sK1,X0)) ),
% 3.71/1.01      inference(superposition,[status(thm)],[c_488,c_8]) ).
% 3.71/1.01  
% 3.71/1.01  cnf(c_653,plain,
% 3.71/1.01      ( k4_xboole_0(sK0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(sK0,k4_xboole_0(sK1,X0)) ),
% 3.71/1.01      inference(demodulation,[status(thm)],[c_636,c_8]) ).
% 3.71/1.01  
% 3.71/1.01  cnf(c_0,plain,
% 3.71/1.01      ( r1_xboole_0(X0,X1)
% 3.71/1.01      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
% 3.71/1.01      inference(cnf_transformation,[],[f29]) ).
% 3.71/1.01  
% 3.71/1.01  cnf(c_57,plain,
% 3.71/1.01      ( r1_xboole_0(X0,X1)
% 3.71/1.01      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
% 3.71/1.01      inference(prop_impl,[status(thm)],[c_0]) ).
% 3.71/1.01  
% 3.71/1.01  cnf(c_10,negated_conjecture,
% 3.71/1.01      ( ~ r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
% 3.71/1.01      inference(cnf_transformation,[],[f35]) ).
% 3.71/1.01  
% 3.71/1.01  cnf(c_119,plain,
% 3.71/1.01      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0
% 3.71/1.01      | k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) != X1
% 3.71/1.01      | sK0 != X0 ),
% 3.71/1.01      inference(resolution_lifted,[status(thm)],[c_57,c_10]) ).
% 3.71/1.01  
% 3.71/1.01  cnf(c_120,plain,
% 3.71/1.01      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) != k1_xboole_0 ),
% 3.71/1.01      inference(unflattening,[status(thm)],[c_119]) ).
% 3.71/1.01  
% 3.71/1.01  cnf(c_2722,plain,
% 3.71/1.01      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK2)))) != k1_xboole_0 ),
% 3.71/1.01      inference(demodulation,[status(thm)],[c_653,c_120]) ).
% 3.71/1.01  
% 3.71/1.01  cnf(c_4248,plain,
% 3.71/1.01      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK2)) != k1_xboole_0 ),
% 3.71/1.01      inference(demodulation,[status(thm)],[c_769,c_2722]) ).
% 3.71/1.01  
% 3.71/1.01  cnf(c_13245,plain,
% 3.71/1.01      ( k4_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
% 3.71/1.01      inference(demodulation,[status(thm)],[c_12960,c_4248]) ).
% 3.71/1.01  
% 3.71/1.01  cnf(c_895,plain,
% 3.71/1.01      ( k4_xboole_0(X0,X0) = k1_xboole_0
% 3.71/1.01      | r1_tarski(k4_xboole_0(X0,X0),X0) != iProver_top ),
% 3.71/1.01      inference(superposition,[status(thm)],[c_426,c_357]) ).
% 3.71/1.01  
% 3.71/1.01  cnf(c_921,plain,
% 3.71/1.01      ( k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0
% 3.71/1.01      | r1_tarski(k4_xboole_0(k1_xboole_0,k1_xboole_0),k1_xboole_0) != iProver_top ),
% 3.71/1.01      inference(instantiation,[status(thm)],[c_895]) ).
% 3.71/1.01  
% 3.71/1.01  cnf(c_19,plain,
% 3.71/1.01      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 3.71/1.01      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.71/1.01  
% 3.71/1.01  cnf(c_21,plain,
% 3.71/1.01      ( r1_tarski(k4_xboole_0(k1_xboole_0,k1_xboole_0),k1_xboole_0) = iProver_top ),
% 3.71/1.01      inference(instantiation,[status(thm)],[c_19]) ).
% 3.71/1.01  
% 3.71/1.01  cnf(contradiction,plain,
% 3.71/1.01      ( $false ),
% 3.71/1.01      inference(minisat,[status(thm)],[c_13245,c_921,c_21]) ).
% 3.71/1.01  
% 3.71/1.01  
% 3.71/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.71/1.01  
% 3.71/1.01  ------                               Statistics
% 3.71/1.01  
% 3.71/1.01  ------ Selected
% 3.71/1.01  
% 3.71/1.01  total_time:                             0.395
% 3.71/1.01  
%------------------------------------------------------------------------------
