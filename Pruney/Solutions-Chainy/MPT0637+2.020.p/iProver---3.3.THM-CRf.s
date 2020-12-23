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
% DateTime   : Thu Dec  3 11:49:59 EST 2020

% Result     : Theorem 3.27s
% Output     : CNFRefutation 3.27s
% Verified   : 
% Statistics : Number of formulae       :   99 (1729 expanded)
%              Number of clauses        :   52 ( 651 expanded)
%              Number of leaves         :   15 ( 375 expanded)
%              Depth                    :   19
%              Number of atoms          :  147 (2400 expanded)
%              Number of equality atoms :  105 (1491 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f49,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f34,f35])).

fof(f52,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f33,f49,f49])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f47,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k3_xboole_0(k2_relat_1(X1),X0) = k2_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k2_relat_1(X1),X0) = k2_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k2_relat_1(X1),X0) = k2_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f50,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f36,f49])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_enumset1(k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),X0)) = k2_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f39,f50])).

fof(f12,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k5_relat_1(X1,k6_relat_1(X0)) = k8_relat_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = k8_relat_1(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = k8_relat_1(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f51,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f32,f50])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k8_relat_1(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f38,f50])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f45,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f16,conjecture,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f16])).

fof(f29,plain,(
    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f17])).

fof(f30,plain,
    ( ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))
   => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f29,f30])).

fof(f48,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f31])).

fof(f55,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) ),
    inference(definition_unfolding,[],[f48,f50])).

cnf(c_1,plain,
    ( k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_12,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_350,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | k1_setfam_1(k2_enumset1(k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X0),X1)) = k2_relat_1(k8_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_356,plain,
    ( k1_setfam_1(k2_enumset1(k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X0),X1)) = k2_relat_1(k8_relat_1(X1,X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1391,plain,
    ( k1_setfam_1(k2_enumset1(k2_relat_1(k6_relat_1(X0)),k2_relat_1(k6_relat_1(X0)),k2_relat_1(k6_relat_1(X0)),X1)) = k2_relat_1(k8_relat_1(X1,k6_relat_1(X0))) ),
    inference(superposition,[status(thm)],[c_350,c_356])).

cnf(c_8,plain,
    ( k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1393,plain,
    ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k2_relat_1(k8_relat_1(X1,k6_relat_1(X0))) ),
    inference(light_normalisation,[status(thm)],[c_1391,c_8])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X1,X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_355,plain,
    ( k5_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X1,X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_832,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k8_relat_1(X1,k6_relat_1(X0)) ),
    inference(superposition,[status(thm)],[c_350,c_355])).

cnf(c_11,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_351,plain,
    ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_827,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(superposition,[status(thm)],[c_350,c_351])).

cnf(c_1180,plain,
    ( k8_relat_1(X0,k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(light_normalisation,[status(thm)],[c_832,c_827])).

cnf(c_1394,plain,
    ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k2_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
    inference(demodulation,[status(thm)],[c_1393,c_1180])).

cnf(c_1434,plain,
    ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(superposition,[status(thm)],[c_1,c_1394])).

cnf(c_1684,plain,
    ( k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k2_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
    inference(superposition,[status(thm)],[c_1434,c_1394])).

cnf(c_0,plain,
    ( r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_359,plain,
    ( r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_581,plain,
    ( r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_359])).

cnf(c_1408,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1394,c_581])).

cnf(c_6,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k8_relat_1(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_354,plain,
    ( k8_relat_1(X0,X1) = X1
    | r1_tarski(k2_relat_1(X1),X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1187,plain,
    ( k8_relat_1(X0,k6_relat_1(X1)) = k6_relat_1(X1)
    | r1_tarski(X1,X0) != iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8,c_354])).

cnf(c_1188,plain,
    ( k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X1)
    | r1_tarski(X1,X0) != iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1187,c_1180])).

cnf(c_4390,plain,
    ( k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X1)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1188,c_350])).

cnf(c_4392,plain,
    ( k7_relat_1(k6_relat_1(X0),k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
    inference(superposition,[status(thm)],[c_1408,c_4390])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) = k7_relat_1(k7_relat_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_357,plain,
    ( k7_relat_1(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) = k7_relat_1(k7_relat_1(X0,X1),X2)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1533,plain,
    ( k7_relat_1(X0,k2_relat_1(k7_relat_1(k6_relat_1(X1),X2))) = k7_relat_1(k7_relat_1(X0,X2),X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_357,c_1394])).

cnf(c_1540,plain,
    ( k7_relat_1(k6_relat_1(X0),k2_relat_1(k7_relat_1(k6_relat_1(X1),X2))) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X2),X1) ),
    inference(superposition,[status(thm)],[c_350,c_1533])).

cnf(c_7099,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0) = k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
    inference(superposition,[status(thm)],[c_4392,c_1540])).

cnf(c_10,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_352,plain,
    ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_761,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(k2_relat_1(k6_relat_1(X0)))) = k6_relat_1(X0) ),
    inference(superposition,[status(thm)],[c_350,c_352])).

cnf(c_762,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X0)) = k6_relat_1(X0) ),
    inference(light_normalisation,[status(thm)],[c_761,c_8])).

cnf(c_926,plain,
    ( k7_relat_1(k6_relat_1(X0),X0) = k6_relat_1(X0) ),
    inference(superposition,[status(thm)],[c_827,c_762])).

cnf(c_2365,plain,
    ( k7_relat_1(k6_relat_1(X0),k2_relat_1(k7_relat_1(k6_relat_1(X1),X2))) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) ),
    inference(superposition,[status(thm)],[c_1684,c_1540])).

cnf(c_3409,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X2),X1) ),
    inference(superposition,[status(thm)],[c_2365,c_1540])).

cnf(c_3482,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(superposition,[status(thm)],[c_926,c_3409])).

cnf(c_7104,plain,
    ( k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(light_normalisation,[status(thm)],[c_7099,c_3482])).

cnf(c_7335,plain,
    ( k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(superposition,[status(thm)],[c_1684,c_7104])).

cnf(c_7700,plain,
    ( k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(superposition,[status(thm)],[c_7335,c_7104])).

cnf(c_13,negated_conjecture,
    ( k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_580,plain,
    ( k6_relat_1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK0))) != k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) ),
    inference(demodulation,[status(thm)],[c_1,c_13])).

cnf(c_923,plain,
    ( k6_relat_1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK0))) != k7_relat_1(k6_relat_1(sK0),sK1) ),
    inference(demodulation,[status(thm)],[c_827,c_580])).

cnf(c_1410,plain,
    ( k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(sK0),sK1))) != k7_relat_1(k6_relat_1(sK0),sK1) ),
    inference(demodulation,[status(thm)],[c_1394,c_923])).

cnf(c_1863,plain,
    ( k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(sK1),sK0))) != k7_relat_1(k6_relat_1(sK0),sK1) ),
    inference(demodulation,[status(thm)],[c_1684,c_1410])).

cnf(c_7211,plain,
    ( k7_relat_1(k6_relat_1(sK1),sK0) != k7_relat_1(k6_relat_1(sK0),sK1) ),
    inference(demodulation,[status(thm)],[c_7104,c_1863])).

cnf(c_7813,plain,
    ( k7_relat_1(k6_relat_1(sK1),sK0) != k7_relat_1(k6_relat_1(sK1),sK0) ),
    inference(demodulation,[status(thm)],[c_7700,c_7211])).

cnf(c_8000,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_7813])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:29:44 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 3.27/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.27/0.99  
% 3.27/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.27/0.99  
% 3.27/0.99  ------  iProver source info
% 3.27/0.99  
% 3.27/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.27/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.27/0.99  git: non_committed_changes: false
% 3.27/0.99  git: last_make_outside_of_git: false
% 3.27/0.99  
% 3.27/0.99  ------ 
% 3.27/0.99  
% 3.27/0.99  ------ Input Options
% 3.27/0.99  
% 3.27/0.99  --out_options                           all
% 3.27/0.99  --tptp_safe_out                         true
% 3.27/0.99  --problem_path                          ""
% 3.27/0.99  --include_path                          ""
% 3.27/0.99  --clausifier                            res/vclausify_rel
% 3.27/0.99  --clausifier_options                    --mode clausify
% 3.27/0.99  --stdin                                 false
% 3.27/0.99  --stats_out                             all
% 3.27/0.99  
% 3.27/0.99  ------ General Options
% 3.27/0.99  
% 3.27/0.99  --fof                                   false
% 3.27/0.99  --time_out_real                         305.
% 3.27/0.99  --time_out_virtual                      -1.
% 3.27/0.99  --symbol_type_check                     false
% 3.27/0.99  --clausify_out                          false
% 3.27/0.99  --sig_cnt_out                           false
% 3.27/0.99  --trig_cnt_out                          false
% 3.27/0.99  --trig_cnt_out_tolerance                1.
% 3.27/0.99  --trig_cnt_out_sk_spl                   false
% 3.27/0.99  --abstr_cl_out                          false
% 3.27/0.99  
% 3.27/0.99  ------ Global Options
% 3.27/0.99  
% 3.27/0.99  --schedule                              default
% 3.27/0.99  --add_important_lit                     false
% 3.27/0.99  --prop_solver_per_cl                    1000
% 3.27/0.99  --min_unsat_core                        false
% 3.27/0.99  --soft_assumptions                      false
% 3.27/0.99  --soft_lemma_size                       3
% 3.27/0.99  --prop_impl_unit_size                   0
% 3.27/0.99  --prop_impl_unit                        []
% 3.27/0.99  --share_sel_clauses                     true
% 3.27/0.99  --reset_solvers                         false
% 3.27/0.99  --bc_imp_inh                            [conj_cone]
% 3.27/0.99  --conj_cone_tolerance                   3.
% 3.27/0.99  --extra_neg_conj                        none
% 3.27/0.99  --large_theory_mode                     true
% 3.27/0.99  --prolific_symb_bound                   200
% 3.27/0.99  --lt_threshold                          2000
% 3.27/0.99  --clause_weak_htbl                      true
% 3.27/0.99  --gc_record_bc_elim                     false
% 3.27/0.99  
% 3.27/0.99  ------ Preprocessing Options
% 3.27/0.99  
% 3.27/0.99  --preprocessing_flag                    true
% 3.27/0.99  --time_out_prep_mult                    0.1
% 3.27/0.99  --splitting_mode                        input
% 3.27/0.99  --splitting_grd                         true
% 3.27/0.99  --splitting_cvd                         false
% 3.27/0.99  --splitting_cvd_svl                     false
% 3.27/0.99  --splitting_nvd                         32
% 3.27/0.99  --sub_typing                            true
% 3.27/0.99  --prep_gs_sim                           true
% 3.27/0.99  --prep_unflatten                        true
% 3.27/0.99  --prep_res_sim                          true
% 3.27/0.99  --prep_upred                            true
% 3.27/0.99  --prep_sem_filter                       exhaustive
% 3.27/0.99  --prep_sem_filter_out                   false
% 3.27/0.99  --pred_elim                             true
% 3.27/0.99  --res_sim_input                         true
% 3.27/0.99  --eq_ax_congr_red                       true
% 3.27/0.99  --pure_diseq_elim                       true
% 3.27/0.99  --brand_transform                       false
% 3.27/0.99  --non_eq_to_eq                          false
% 3.27/0.99  --prep_def_merge                        true
% 3.27/0.99  --prep_def_merge_prop_impl              false
% 3.27/0.99  --prep_def_merge_mbd                    true
% 3.27/0.99  --prep_def_merge_tr_red                 false
% 3.27/0.99  --prep_def_merge_tr_cl                  false
% 3.27/0.99  --smt_preprocessing                     true
% 3.27/0.99  --smt_ac_axioms                         fast
% 3.27/0.99  --preprocessed_out                      false
% 3.27/0.99  --preprocessed_stats                    false
% 3.27/0.99  
% 3.27/0.99  ------ Abstraction refinement Options
% 3.27/0.99  
% 3.27/0.99  --abstr_ref                             []
% 3.27/0.99  --abstr_ref_prep                        false
% 3.27/0.99  --abstr_ref_until_sat                   false
% 3.27/0.99  --abstr_ref_sig_restrict                funpre
% 3.27/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.27/0.99  --abstr_ref_under                       []
% 3.27/0.99  
% 3.27/0.99  ------ SAT Options
% 3.27/0.99  
% 3.27/0.99  --sat_mode                              false
% 3.27/0.99  --sat_fm_restart_options                ""
% 3.27/0.99  --sat_gr_def                            false
% 3.27/0.99  --sat_epr_types                         true
% 3.27/0.99  --sat_non_cyclic_types                  false
% 3.27/0.99  --sat_finite_models                     false
% 3.27/0.99  --sat_fm_lemmas                         false
% 3.27/0.99  --sat_fm_prep                           false
% 3.27/0.99  --sat_fm_uc_incr                        true
% 3.27/0.99  --sat_out_model                         small
% 3.27/0.99  --sat_out_clauses                       false
% 3.27/0.99  
% 3.27/0.99  ------ QBF Options
% 3.27/0.99  
% 3.27/0.99  --qbf_mode                              false
% 3.27/0.99  --qbf_elim_univ                         false
% 3.27/0.99  --qbf_dom_inst                          none
% 3.27/0.99  --qbf_dom_pre_inst                      false
% 3.27/0.99  --qbf_sk_in                             false
% 3.27/0.99  --qbf_pred_elim                         true
% 3.27/0.99  --qbf_split                             512
% 3.27/0.99  
% 3.27/0.99  ------ BMC1 Options
% 3.27/0.99  
% 3.27/0.99  --bmc1_incremental                      false
% 3.27/0.99  --bmc1_axioms                           reachable_all
% 3.27/0.99  --bmc1_min_bound                        0
% 3.27/0.99  --bmc1_max_bound                        -1
% 3.27/0.99  --bmc1_max_bound_default                -1
% 3.27/0.99  --bmc1_symbol_reachability              true
% 3.27/0.99  --bmc1_property_lemmas                  false
% 3.27/0.99  --bmc1_k_induction                      false
% 3.27/0.99  --bmc1_non_equiv_states                 false
% 3.27/0.99  --bmc1_deadlock                         false
% 3.27/0.99  --bmc1_ucm                              false
% 3.27/0.99  --bmc1_add_unsat_core                   none
% 3.27/0.99  --bmc1_unsat_core_children              false
% 3.27/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.27/0.99  --bmc1_out_stat                         full
% 3.27/0.99  --bmc1_ground_init                      false
% 3.27/0.99  --bmc1_pre_inst_next_state              false
% 3.27/0.99  --bmc1_pre_inst_state                   false
% 3.27/0.99  --bmc1_pre_inst_reach_state             false
% 3.27/0.99  --bmc1_out_unsat_core                   false
% 3.27/0.99  --bmc1_aig_witness_out                  false
% 3.27/0.99  --bmc1_verbose                          false
% 3.27/0.99  --bmc1_dump_clauses_tptp                false
% 3.27/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.27/0.99  --bmc1_dump_file                        -
% 3.27/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.27/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.27/0.99  --bmc1_ucm_extend_mode                  1
% 3.27/0.99  --bmc1_ucm_init_mode                    2
% 3.27/0.99  --bmc1_ucm_cone_mode                    none
% 3.27/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.27/0.99  --bmc1_ucm_relax_model                  4
% 3.27/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.27/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.27/0.99  --bmc1_ucm_layered_model                none
% 3.27/0.99  --bmc1_ucm_max_lemma_size               10
% 3.27/0.99  
% 3.27/0.99  ------ AIG Options
% 3.27/0.99  
% 3.27/0.99  --aig_mode                              false
% 3.27/0.99  
% 3.27/0.99  ------ Instantiation Options
% 3.27/0.99  
% 3.27/0.99  --instantiation_flag                    true
% 3.27/0.99  --inst_sos_flag                         false
% 3.27/0.99  --inst_sos_phase                        true
% 3.27/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.27/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.27/0.99  --inst_lit_sel_side                     num_symb
% 3.27/0.99  --inst_solver_per_active                1400
% 3.27/0.99  --inst_solver_calls_frac                1.
% 3.27/0.99  --inst_passive_queue_type               priority_queues
% 3.27/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.27/0.99  --inst_passive_queues_freq              [25;2]
% 3.27/0.99  --inst_dismatching                      true
% 3.27/0.99  --inst_eager_unprocessed_to_passive     true
% 3.27/0.99  --inst_prop_sim_given                   true
% 3.27/0.99  --inst_prop_sim_new                     false
% 3.27/0.99  --inst_subs_new                         false
% 3.27/0.99  --inst_eq_res_simp                      false
% 3.27/0.99  --inst_subs_given                       false
% 3.27/0.99  --inst_orphan_elimination               true
% 3.27/0.99  --inst_learning_loop_flag               true
% 3.27/0.99  --inst_learning_start                   3000
% 3.27/0.99  --inst_learning_factor                  2
% 3.27/0.99  --inst_start_prop_sim_after_learn       3
% 3.27/0.99  --inst_sel_renew                        solver
% 3.27/0.99  --inst_lit_activity_flag                true
% 3.27/0.99  --inst_restr_to_given                   false
% 3.27/0.99  --inst_activity_threshold               500
% 3.27/0.99  --inst_out_proof                        true
% 3.27/0.99  
% 3.27/0.99  ------ Resolution Options
% 3.27/0.99  
% 3.27/0.99  --resolution_flag                       true
% 3.27/0.99  --res_lit_sel                           adaptive
% 3.27/0.99  --res_lit_sel_side                      none
% 3.27/0.99  --res_ordering                          kbo
% 3.27/0.99  --res_to_prop_solver                    active
% 3.27/0.99  --res_prop_simpl_new                    false
% 3.27/0.99  --res_prop_simpl_given                  true
% 3.27/0.99  --res_passive_queue_type                priority_queues
% 3.27/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.27/0.99  --res_passive_queues_freq               [15;5]
% 3.27/0.99  --res_forward_subs                      full
% 3.27/0.99  --res_backward_subs                     full
% 3.27/0.99  --res_forward_subs_resolution           true
% 3.27/0.99  --res_backward_subs_resolution          true
% 3.27/0.99  --res_orphan_elimination                true
% 3.27/0.99  --res_time_limit                        2.
% 3.27/0.99  --res_out_proof                         true
% 3.27/0.99  
% 3.27/0.99  ------ Superposition Options
% 3.27/0.99  
% 3.27/0.99  --superposition_flag                    true
% 3.27/0.99  --sup_passive_queue_type                priority_queues
% 3.27/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.27/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.27/0.99  --demod_completeness_check              fast
% 3.27/0.99  --demod_use_ground                      true
% 3.27/0.99  --sup_to_prop_solver                    passive
% 3.27/0.99  --sup_prop_simpl_new                    true
% 3.27/0.99  --sup_prop_simpl_given                  true
% 3.27/0.99  --sup_fun_splitting                     false
% 3.27/0.99  --sup_smt_interval                      50000
% 3.27/0.99  
% 3.27/0.99  ------ Superposition Simplification Setup
% 3.27/0.99  
% 3.27/0.99  --sup_indices_passive                   []
% 3.27/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.27/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.27/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.27/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.27/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.27/0.99  --sup_full_bw                           [BwDemod]
% 3.27/0.99  --sup_immed_triv                        [TrivRules]
% 3.27/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.27/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.27/0.99  --sup_immed_bw_main                     []
% 3.27/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.27/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.27/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.27/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.27/0.99  
% 3.27/0.99  ------ Combination Options
% 3.27/0.99  
% 3.27/0.99  --comb_res_mult                         3
% 3.27/0.99  --comb_sup_mult                         2
% 3.27/0.99  --comb_inst_mult                        10
% 3.27/0.99  
% 3.27/0.99  ------ Debug Options
% 3.27/0.99  
% 3.27/0.99  --dbg_backtrace                         false
% 3.27/0.99  --dbg_dump_prop_clauses                 false
% 3.27/0.99  --dbg_dump_prop_clauses_file            -
% 3.27/0.99  --dbg_out_stat                          false
% 3.27/0.99  ------ Parsing...
% 3.27/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.27/0.99  
% 3.27/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.27/0.99  
% 3.27/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.27/0.99  
% 3.27/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.27/0.99  ------ Proving...
% 3.27/0.99  ------ Problem Properties 
% 3.27/0.99  
% 3.27/0.99  
% 3.27/0.99  clauses                                 14
% 3.27/0.99  conjectures                             1
% 3.27/0.99  EPR                                     0
% 3.27/0.99  Horn                                    14
% 3.27/0.99  unary                                   6
% 3.27/0.99  binary                                  5
% 3.27/0.99  lits                                    26
% 3.27/0.99  lits eq                                 11
% 3.27/0.99  fd_pure                                 0
% 3.27/0.99  fd_pseudo                               0
% 3.27/0.99  fd_cond                                 0
% 3.27/0.99  fd_pseudo_cond                          0
% 3.27/0.99  AC symbols                              0
% 3.27/0.99  
% 3.27/0.99  ------ Schedule dynamic 5 is on 
% 3.27/0.99  
% 3.27/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.27/0.99  
% 3.27/0.99  
% 3.27/0.99  ------ 
% 3.27/0.99  Current options:
% 3.27/0.99  ------ 
% 3.27/0.99  
% 3.27/0.99  ------ Input Options
% 3.27/0.99  
% 3.27/0.99  --out_options                           all
% 3.27/0.99  --tptp_safe_out                         true
% 3.27/0.99  --problem_path                          ""
% 3.27/0.99  --include_path                          ""
% 3.27/0.99  --clausifier                            res/vclausify_rel
% 3.27/0.99  --clausifier_options                    --mode clausify
% 3.27/0.99  --stdin                                 false
% 3.27/0.99  --stats_out                             all
% 3.27/0.99  
% 3.27/0.99  ------ General Options
% 3.27/0.99  
% 3.27/0.99  --fof                                   false
% 3.27/0.99  --time_out_real                         305.
% 3.27/0.99  --time_out_virtual                      -1.
% 3.27/0.99  --symbol_type_check                     false
% 3.27/0.99  --clausify_out                          false
% 3.27/0.99  --sig_cnt_out                           false
% 3.27/0.99  --trig_cnt_out                          false
% 3.27/0.99  --trig_cnt_out_tolerance                1.
% 3.27/0.99  --trig_cnt_out_sk_spl                   false
% 3.27/0.99  --abstr_cl_out                          false
% 3.27/0.99  
% 3.27/0.99  ------ Global Options
% 3.27/0.99  
% 3.27/0.99  --schedule                              default
% 3.27/0.99  --add_important_lit                     false
% 3.27/0.99  --prop_solver_per_cl                    1000
% 3.27/0.99  --min_unsat_core                        false
% 3.27/0.99  --soft_assumptions                      false
% 3.27/0.99  --soft_lemma_size                       3
% 3.27/0.99  --prop_impl_unit_size                   0
% 3.27/0.99  --prop_impl_unit                        []
% 3.27/0.99  --share_sel_clauses                     true
% 3.27/0.99  --reset_solvers                         false
% 3.27/0.99  --bc_imp_inh                            [conj_cone]
% 3.27/0.99  --conj_cone_tolerance                   3.
% 3.27/0.99  --extra_neg_conj                        none
% 3.27/0.99  --large_theory_mode                     true
% 3.27/0.99  --prolific_symb_bound                   200
% 3.27/0.99  --lt_threshold                          2000
% 3.27/0.99  --clause_weak_htbl                      true
% 3.27/0.99  --gc_record_bc_elim                     false
% 3.27/0.99  
% 3.27/0.99  ------ Preprocessing Options
% 3.27/0.99  
% 3.27/0.99  --preprocessing_flag                    true
% 3.27/0.99  --time_out_prep_mult                    0.1
% 3.27/0.99  --splitting_mode                        input
% 3.27/0.99  --splitting_grd                         true
% 3.27/0.99  --splitting_cvd                         false
% 3.27/0.99  --splitting_cvd_svl                     false
% 3.27/0.99  --splitting_nvd                         32
% 3.27/0.99  --sub_typing                            true
% 3.27/0.99  --prep_gs_sim                           true
% 3.27/0.99  --prep_unflatten                        true
% 3.27/0.99  --prep_res_sim                          true
% 3.27/0.99  --prep_upred                            true
% 3.27/0.99  --prep_sem_filter                       exhaustive
% 3.27/0.99  --prep_sem_filter_out                   false
% 3.27/0.99  --pred_elim                             true
% 3.27/0.99  --res_sim_input                         true
% 3.27/0.99  --eq_ax_congr_red                       true
% 3.27/0.99  --pure_diseq_elim                       true
% 3.27/0.99  --brand_transform                       false
% 3.27/0.99  --non_eq_to_eq                          false
% 3.27/0.99  --prep_def_merge                        true
% 3.27/0.99  --prep_def_merge_prop_impl              false
% 3.27/0.99  --prep_def_merge_mbd                    true
% 3.27/0.99  --prep_def_merge_tr_red                 false
% 3.27/0.99  --prep_def_merge_tr_cl                  false
% 3.27/0.99  --smt_preprocessing                     true
% 3.27/0.99  --smt_ac_axioms                         fast
% 3.27/0.99  --preprocessed_out                      false
% 3.27/0.99  --preprocessed_stats                    false
% 3.27/0.99  
% 3.27/0.99  ------ Abstraction refinement Options
% 3.27/0.99  
% 3.27/0.99  --abstr_ref                             []
% 3.27/0.99  --abstr_ref_prep                        false
% 3.27/0.99  --abstr_ref_until_sat                   false
% 3.27/0.99  --abstr_ref_sig_restrict                funpre
% 3.27/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.27/0.99  --abstr_ref_under                       []
% 3.27/0.99  
% 3.27/0.99  ------ SAT Options
% 3.27/0.99  
% 3.27/0.99  --sat_mode                              false
% 3.27/0.99  --sat_fm_restart_options                ""
% 3.27/0.99  --sat_gr_def                            false
% 3.27/0.99  --sat_epr_types                         true
% 3.27/0.99  --sat_non_cyclic_types                  false
% 3.27/0.99  --sat_finite_models                     false
% 3.27/0.99  --sat_fm_lemmas                         false
% 3.27/0.99  --sat_fm_prep                           false
% 3.27/0.99  --sat_fm_uc_incr                        true
% 3.27/0.99  --sat_out_model                         small
% 3.27/0.99  --sat_out_clauses                       false
% 3.27/0.99  
% 3.27/0.99  ------ QBF Options
% 3.27/0.99  
% 3.27/0.99  --qbf_mode                              false
% 3.27/0.99  --qbf_elim_univ                         false
% 3.27/0.99  --qbf_dom_inst                          none
% 3.27/0.99  --qbf_dom_pre_inst                      false
% 3.27/0.99  --qbf_sk_in                             false
% 3.27/0.99  --qbf_pred_elim                         true
% 3.27/0.99  --qbf_split                             512
% 3.27/0.99  
% 3.27/0.99  ------ BMC1 Options
% 3.27/0.99  
% 3.27/0.99  --bmc1_incremental                      false
% 3.27/0.99  --bmc1_axioms                           reachable_all
% 3.27/0.99  --bmc1_min_bound                        0
% 3.27/0.99  --bmc1_max_bound                        -1
% 3.27/0.99  --bmc1_max_bound_default                -1
% 3.27/0.99  --bmc1_symbol_reachability              true
% 3.27/0.99  --bmc1_property_lemmas                  false
% 3.27/0.99  --bmc1_k_induction                      false
% 3.27/0.99  --bmc1_non_equiv_states                 false
% 3.27/0.99  --bmc1_deadlock                         false
% 3.27/0.99  --bmc1_ucm                              false
% 3.27/0.99  --bmc1_add_unsat_core                   none
% 3.27/0.99  --bmc1_unsat_core_children              false
% 3.27/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.27/0.99  --bmc1_out_stat                         full
% 3.27/0.99  --bmc1_ground_init                      false
% 3.27/0.99  --bmc1_pre_inst_next_state              false
% 3.27/0.99  --bmc1_pre_inst_state                   false
% 3.27/0.99  --bmc1_pre_inst_reach_state             false
% 3.27/0.99  --bmc1_out_unsat_core                   false
% 3.27/0.99  --bmc1_aig_witness_out                  false
% 3.27/0.99  --bmc1_verbose                          false
% 3.27/0.99  --bmc1_dump_clauses_tptp                false
% 3.27/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.27/0.99  --bmc1_dump_file                        -
% 3.27/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.27/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.27/0.99  --bmc1_ucm_extend_mode                  1
% 3.27/0.99  --bmc1_ucm_init_mode                    2
% 3.27/0.99  --bmc1_ucm_cone_mode                    none
% 3.27/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.27/0.99  --bmc1_ucm_relax_model                  4
% 3.27/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.27/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.27/0.99  --bmc1_ucm_layered_model                none
% 3.27/0.99  --bmc1_ucm_max_lemma_size               10
% 3.27/0.99  
% 3.27/0.99  ------ AIG Options
% 3.27/0.99  
% 3.27/0.99  --aig_mode                              false
% 3.27/0.99  
% 3.27/0.99  ------ Instantiation Options
% 3.27/0.99  
% 3.27/0.99  --instantiation_flag                    true
% 3.27/0.99  --inst_sos_flag                         false
% 3.27/0.99  --inst_sos_phase                        true
% 3.27/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.27/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.27/0.99  --inst_lit_sel_side                     none
% 3.27/0.99  --inst_solver_per_active                1400
% 3.27/0.99  --inst_solver_calls_frac                1.
% 3.27/0.99  --inst_passive_queue_type               priority_queues
% 3.27/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.27/0.99  --inst_passive_queues_freq              [25;2]
% 3.27/0.99  --inst_dismatching                      true
% 3.27/0.99  --inst_eager_unprocessed_to_passive     true
% 3.27/0.99  --inst_prop_sim_given                   true
% 3.27/0.99  --inst_prop_sim_new                     false
% 3.27/0.99  --inst_subs_new                         false
% 3.27/0.99  --inst_eq_res_simp                      false
% 3.27/0.99  --inst_subs_given                       false
% 3.27/0.99  --inst_orphan_elimination               true
% 3.27/0.99  --inst_learning_loop_flag               true
% 3.27/0.99  --inst_learning_start                   3000
% 3.27/0.99  --inst_learning_factor                  2
% 3.27/0.99  --inst_start_prop_sim_after_learn       3
% 3.27/0.99  --inst_sel_renew                        solver
% 3.27/0.99  --inst_lit_activity_flag                true
% 3.27/0.99  --inst_restr_to_given                   false
% 3.27/0.99  --inst_activity_threshold               500
% 3.27/0.99  --inst_out_proof                        true
% 3.27/0.99  
% 3.27/0.99  ------ Resolution Options
% 3.27/0.99  
% 3.27/0.99  --resolution_flag                       false
% 3.27/0.99  --res_lit_sel                           adaptive
% 3.27/0.99  --res_lit_sel_side                      none
% 3.27/0.99  --res_ordering                          kbo
% 3.27/0.99  --res_to_prop_solver                    active
% 3.27/0.99  --res_prop_simpl_new                    false
% 3.27/0.99  --res_prop_simpl_given                  true
% 3.27/0.99  --res_passive_queue_type                priority_queues
% 3.27/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.27/0.99  --res_passive_queues_freq               [15;5]
% 3.27/0.99  --res_forward_subs                      full
% 3.27/0.99  --res_backward_subs                     full
% 3.27/0.99  --res_forward_subs_resolution           true
% 3.27/0.99  --res_backward_subs_resolution          true
% 3.27/0.99  --res_orphan_elimination                true
% 3.27/0.99  --res_time_limit                        2.
% 3.27/0.99  --res_out_proof                         true
% 3.27/0.99  
% 3.27/0.99  ------ Superposition Options
% 3.27/0.99  
% 3.27/0.99  --superposition_flag                    true
% 3.27/0.99  --sup_passive_queue_type                priority_queues
% 3.27/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.27/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.27/0.99  --demod_completeness_check              fast
% 3.27/0.99  --demod_use_ground                      true
% 3.27/0.99  --sup_to_prop_solver                    passive
% 3.27/0.99  --sup_prop_simpl_new                    true
% 3.27/0.99  --sup_prop_simpl_given                  true
% 3.27/0.99  --sup_fun_splitting                     false
% 3.27/0.99  --sup_smt_interval                      50000
% 3.27/0.99  
% 3.27/0.99  ------ Superposition Simplification Setup
% 3.27/0.99  
% 3.27/0.99  --sup_indices_passive                   []
% 3.27/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.27/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.27/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.27/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.27/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.27/0.99  --sup_full_bw                           [BwDemod]
% 3.27/0.99  --sup_immed_triv                        [TrivRules]
% 3.27/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.27/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.27/0.99  --sup_immed_bw_main                     []
% 3.27/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.27/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.27/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.27/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.27/0.99  
% 3.27/0.99  ------ Combination Options
% 3.27/0.99  
% 3.27/0.99  --comb_res_mult                         3
% 3.27/0.99  --comb_sup_mult                         2
% 3.27/0.99  --comb_inst_mult                        10
% 3.27/0.99  
% 3.27/0.99  ------ Debug Options
% 3.27/0.99  
% 3.27/0.99  --dbg_backtrace                         false
% 3.27/0.99  --dbg_dump_prop_clauses                 false
% 3.27/0.99  --dbg_dump_prop_clauses_file            -
% 3.27/0.99  --dbg_out_stat                          false
% 3.27/0.99  
% 3.27/0.99  
% 3.27/0.99  
% 3.27/0.99  
% 3.27/0.99  ------ Proving...
% 3.27/0.99  
% 3.27/0.99  
% 3.27/0.99  % SZS status Theorem for theBenchmark.p
% 3.27/0.99  
% 3.27/0.99   Resolution empty clause
% 3.27/0.99  
% 3.27/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.27/0.99  
% 3.27/0.99  fof(f2,axiom,(
% 3.27/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 3.27/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.27/0.99  
% 3.27/0.99  fof(f33,plain,(
% 3.27/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 3.27/0.99    inference(cnf_transformation,[],[f2])).
% 3.27/0.99  
% 3.27/0.99  fof(f3,axiom,(
% 3.27/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.27/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.27/0.99  
% 3.27/0.99  fof(f34,plain,(
% 3.27/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.27/0.99    inference(cnf_transformation,[],[f3])).
% 3.27/0.99  
% 3.27/0.99  fof(f4,axiom,(
% 3.27/0.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.27/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.27/0.99  
% 3.27/0.99  fof(f35,plain,(
% 3.27/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.27/0.99    inference(cnf_transformation,[],[f4])).
% 3.27/0.99  
% 3.27/0.99  fof(f49,plain,(
% 3.27/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 3.27/0.99    inference(definition_unfolding,[],[f34,f35])).
% 3.27/0.99  
% 3.27/0.99  fof(f52,plain,(
% 3.27/0.99    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0)) )),
% 3.27/0.99    inference(definition_unfolding,[],[f33,f49,f49])).
% 3.27/0.99  
% 3.27/0.99  fof(f15,axiom,(
% 3.27/0.99    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 3.27/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.27/0.99  
% 3.27/0.99  fof(f18,plain,(
% 3.27/0.99    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 3.27/0.99    inference(pure_predicate_removal,[],[f15])).
% 3.27/0.99  
% 3.27/0.99  fof(f47,plain,(
% 3.27/0.99    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 3.27/0.99    inference(cnf_transformation,[],[f18])).
% 3.27/0.99  
% 3.27/0.99  fof(f8,axiom,(
% 3.27/0.99    ! [X0,X1] : (v1_relat_1(X1) => k3_xboole_0(k2_relat_1(X1),X0) = k2_relat_1(k8_relat_1(X0,X1)))),
% 3.27/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.27/0.99  
% 3.27/0.99  fof(f22,plain,(
% 3.27/0.99    ! [X0,X1] : (k3_xboole_0(k2_relat_1(X1),X0) = k2_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1))),
% 3.27/0.99    inference(ennf_transformation,[],[f8])).
% 3.27/0.99  
% 3.27/0.99  fof(f39,plain,(
% 3.27/0.99    ( ! [X0,X1] : (k3_xboole_0(k2_relat_1(X1),X0) = k2_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1)) )),
% 3.27/0.99    inference(cnf_transformation,[],[f22])).
% 3.27/0.99  
% 3.27/0.99  fof(f5,axiom,(
% 3.27/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.27/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.27/0.99  
% 3.27/0.99  fof(f36,plain,(
% 3.27/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.27/0.99    inference(cnf_transformation,[],[f5])).
% 3.27/0.99  
% 3.27/0.99  fof(f50,plain,(
% 3.27/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 3.27/0.99    inference(definition_unfolding,[],[f36,f49])).
% 3.27/0.99  
% 3.27/0.99  fof(f54,plain,(
% 3.27/0.99    ( ! [X0,X1] : (k1_setfam_1(k2_enumset1(k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),X0)) = k2_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1)) )),
% 3.27/0.99    inference(definition_unfolding,[],[f39,f50])).
% 3.27/0.99  
% 3.27/0.99  fof(f12,axiom,(
% 3.27/0.99    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 3.27/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.27/0.99  
% 3.27/0.99  fof(f44,plain,(
% 3.27/0.99    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 3.27/0.99    inference(cnf_transformation,[],[f12])).
% 3.27/0.99  
% 3.27/0.99  fof(f9,axiom,(
% 3.27/0.99    ! [X0,X1] : (v1_relat_1(X1) => k5_relat_1(X1,k6_relat_1(X0)) = k8_relat_1(X0,X1))),
% 3.27/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.27/0.99  
% 3.27/0.99  fof(f23,plain,(
% 3.27/0.99    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = k8_relat_1(X0,X1) | ~v1_relat_1(X1))),
% 3.27/0.99    inference(ennf_transformation,[],[f9])).
% 3.27/0.99  
% 3.27/0.99  fof(f40,plain,(
% 3.27/0.99    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = k8_relat_1(X0,X1) | ~v1_relat_1(X1)) )),
% 3.27/0.99    inference(cnf_transformation,[],[f23])).
% 3.27/0.99  
% 3.27/0.99  fof(f14,axiom,(
% 3.27/0.99    ! [X0,X1] : (v1_relat_1(X1) => k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0))),
% 3.27/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.27/0.99  
% 3.27/0.99  fof(f28,plain,(
% 3.27/0.99    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.27/0.99    inference(ennf_transformation,[],[f14])).
% 3.27/0.99  
% 3.27/0.99  fof(f46,plain,(
% 3.27/0.99    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.27/0.99    inference(cnf_transformation,[],[f28])).
% 3.27/0.99  
% 3.27/0.99  fof(f1,axiom,(
% 3.27/0.99    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 3.27/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.27/0.99  
% 3.27/0.99  fof(f32,plain,(
% 3.27/0.99    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 3.27/0.99    inference(cnf_transformation,[],[f1])).
% 3.27/0.99  
% 3.27/0.99  fof(f51,plain,(
% 3.27/0.99    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0)) )),
% 3.27/0.99    inference(definition_unfolding,[],[f32,f50])).
% 3.27/0.99  
% 3.27/0.99  fof(f10,axiom,(
% 3.27/0.99    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k8_relat_1(X0,X1) = X1))),
% 3.27/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.27/0.99  
% 3.27/0.99  fof(f24,plain,(
% 3.27/0.99    ! [X0,X1] : ((k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.27/0.99    inference(ennf_transformation,[],[f10])).
% 3.27/0.99  
% 3.27/0.99  fof(f25,plain,(
% 3.27/0.99    ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 3.27/0.99    inference(flattening,[],[f24])).
% 3.27/0.99  
% 3.27/0.99  fof(f41,plain,(
% 3.27/0.99    ( ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 3.27/0.99    inference(cnf_transformation,[],[f25])).
% 3.27/0.99  
% 3.27/0.99  fof(f7,axiom,(
% 3.27/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1))),
% 3.27/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.27/0.99  
% 3.27/0.99  fof(f21,plain,(
% 3.27/0.99    ! [X0,X1,X2] : (k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2))),
% 3.27/0.99    inference(ennf_transformation,[],[f7])).
% 3.27/0.99  
% 3.27/0.99  fof(f38,plain,(
% 3.27/0.99    ( ! [X2,X0,X1] : (k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 3.27/0.99    inference(cnf_transformation,[],[f21])).
% 3.27/0.99  
% 3.27/0.99  fof(f53,plain,(
% 3.27/0.99    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) | ~v1_relat_1(X2)) )),
% 3.27/0.99    inference(definition_unfolding,[],[f38,f50])).
% 3.27/0.99  
% 3.27/0.99  fof(f13,axiom,(
% 3.27/0.99    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 3.27/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.27/0.99  
% 3.27/0.99  fof(f27,plain,(
% 3.27/0.99    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 3.27/0.99    inference(ennf_transformation,[],[f13])).
% 3.27/0.99  
% 3.27/0.99  fof(f45,plain,(
% 3.27/0.99    ( ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 3.27/0.99    inference(cnf_transformation,[],[f27])).
% 3.27/0.99  
% 3.27/0.99  fof(f16,conjecture,(
% 3.27/0.99    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 3.27/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.27/0.99  
% 3.27/0.99  fof(f17,negated_conjecture,(
% 3.27/0.99    ~! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 3.27/0.99    inference(negated_conjecture,[],[f16])).
% 3.27/0.99  
% 3.27/0.99  fof(f29,plain,(
% 3.27/0.99    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))),
% 3.27/0.99    inference(ennf_transformation,[],[f17])).
% 3.27/0.99  
% 3.27/0.99  fof(f30,plain,(
% 3.27/0.99    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 3.27/0.99    introduced(choice_axiom,[])).
% 3.27/0.99  
% 3.27/0.99  fof(f31,plain,(
% 3.27/0.99    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 3.27/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f29,f30])).
% 3.27/0.99  
% 3.27/0.99  fof(f48,plain,(
% 3.27/0.99    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 3.27/0.99    inference(cnf_transformation,[],[f31])).
% 3.27/0.99  
% 3.27/0.99  fof(f55,plain,(
% 3.27/0.99    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)))),
% 3.27/0.99    inference(definition_unfolding,[],[f48,f50])).
% 3.27/0.99  
% 3.27/0.99  cnf(c_1,plain,
% 3.27/0.99      ( k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
% 3.27/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_12,plain,
% 3.27/0.99      ( v1_relat_1(k6_relat_1(X0)) ),
% 3.27/0.99      inference(cnf_transformation,[],[f47]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_350,plain,
% 3.27/0.99      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 3.27/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_4,plain,
% 3.27/0.99      ( ~ v1_relat_1(X0)
% 3.27/0.99      | k1_setfam_1(k2_enumset1(k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X0),X1)) = k2_relat_1(k8_relat_1(X1,X0)) ),
% 3.27/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_356,plain,
% 3.27/0.99      ( k1_setfam_1(k2_enumset1(k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X0),X1)) = k2_relat_1(k8_relat_1(X1,X0))
% 3.27/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.27/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_1391,plain,
% 3.27/0.99      ( k1_setfam_1(k2_enumset1(k2_relat_1(k6_relat_1(X0)),k2_relat_1(k6_relat_1(X0)),k2_relat_1(k6_relat_1(X0)),X1)) = k2_relat_1(k8_relat_1(X1,k6_relat_1(X0))) ),
% 3.27/0.99      inference(superposition,[status(thm)],[c_350,c_356]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_8,plain,
% 3.27/0.99      ( k2_relat_1(k6_relat_1(X0)) = X0 ),
% 3.27/0.99      inference(cnf_transformation,[],[f44]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_1393,plain,
% 3.27/0.99      ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k2_relat_1(k8_relat_1(X1,k6_relat_1(X0))) ),
% 3.27/0.99      inference(light_normalisation,[status(thm)],[c_1391,c_8]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_5,plain,
% 3.27/0.99      ( ~ v1_relat_1(X0) | k5_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X1,X0) ),
% 3.27/0.99      inference(cnf_transformation,[],[f40]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_355,plain,
% 3.27/0.99      ( k5_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X1,X0)
% 3.27/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.27/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_832,plain,
% 3.27/0.99      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k8_relat_1(X1,k6_relat_1(X0)) ),
% 3.27/0.99      inference(superposition,[status(thm)],[c_350,c_355]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_11,plain,
% 3.27/0.99      ( ~ v1_relat_1(X0) | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
% 3.27/0.99      inference(cnf_transformation,[],[f46]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_351,plain,
% 3.27/0.99      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
% 3.27/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.27/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_827,plain,
% 3.27/0.99      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
% 3.27/0.99      inference(superposition,[status(thm)],[c_350,c_351]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_1180,plain,
% 3.27/0.99      ( k8_relat_1(X0,k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X0),X1) ),
% 3.27/0.99      inference(light_normalisation,[status(thm)],[c_832,c_827]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_1394,plain,
% 3.27/0.99      ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k2_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
% 3.27/0.99      inference(demodulation,[status(thm)],[c_1393,c_1180]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_1434,plain,
% 3.27/0.99      ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
% 3.27/0.99      inference(superposition,[status(thm)],[c_1,c_1394]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_1684,plain,
% 3.27/0.99      ( k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k2_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
% 3.27/0.99      inference(superposition,[status(thm)],[c_1434,c_1394]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_0,plain,
% 3.27/0.99      ( r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0) ),
% 3.27/0.99      inference(cnf_transformation,[],[f51]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_359,plain,
% 3.27/0.99      ( r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0) = iProver_top ),
% 3.27/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_581,plain,
% 3.27/0.99      ( r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X1) = iProver_top ),
% 3.27/0.99      inference(superposition,[status(thm)],[c_1,c_359]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_1408,plain,
% 3.27/0.99      ( r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X0) = iProver_top ),
% 3.27/0.99      inference(demodulation,[status(thm)],[c_1394,c_581]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_6,plain,
% 3.27/0.99      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 3.27/0.99      | ~ v1_relat_1(X0)
% 3.27/0.99      | k8_relat_1(X1,X0) = X0 ),
% 3.27/0.99      inference(cnf_transformation,[],[f41]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_354,plain,
% 3.27/0.99      ( k8_relat_1(X0,X1) = X1
% 3.27/0.99      | r1_tarski(k2_relat_1(X1),X0) != iProver_top
% 3.27/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.27/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_1187,plain,
% 3.27/0.99      ( k8_relat_1(X0,k6_relat_1(X1)) = k6_relat_1(X1)
% 3.27/0.99      | r1_tarski(X1,X0) != iProver_top
% 3.27/0.99      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 3.27/0.99      inference(superposition,[status(thm)],[c_8,c_354]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_1188,plain,
% 3.27/0.99      ( k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X1)
% 3.27/0.99      | r1_tarski(X1,X0) != iProver_top
% 3.27/0.99      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 3.27/0.99      inference(demodulation,[status(thm)],[c_1187,c_1180]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_4390,plain,
% 3.27/0.99      ( k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X1)
% 3.27/0.99      | r1_tarski(X1,X0) != iProver_top ),
% 3.27/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_1188,c_350]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_4392,plain,
% 3.27/0.99      ( k7_relat_1(k6_relat_1(X0),k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
% 3.27/0.99      inference(superposition,[status(thm)],[c_1408,c_4390]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_3,plain,
% 3.27/0.99      ( ~ v1_relat_1(X0)
% 3.27/0.99      | k7_relat_1(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) = k7_relat_1(k7_relat_1(X0,X1),X2) ),
% 3.27/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_357,plain,
% 3.27/0.99      ( k7_relat_1(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) = k7_relat_1(k7_relat_1(X0,X1),X2)
% 3.27/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.27/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_1533,plain,
% 3.27/0.99      ( k7_relat_1(X0,k2_relat_1(k7_relat_1(k6_relat_1(X1),X2))) = k7_relat_1(k7_relat_1(X0,X2),X1)
% 3.27/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.27/0.99      inference(demodulation,[status(thm)],[c_357,c_1394]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_1540,plain,
% 3.27/0.99      ( k7_relat_1(k6_relat_1(X0),k2_relat_1(k7_relat_1(k6_relat_1(X1),X2))) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X2),X1) ),
% 3.27/0.99      inference(superposition,[status(thm)],[c_350,c_1533]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_7099,plain,
% 3.27/0.99      ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0) = k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
% 3.27/0.99      inference(superposition,[status(thm)],[c_4392,c_1540]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_10,plain,
% 3.27/0.99      ( ~ v1_relat_1(X0) | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ),
% 3.27/0.99      inference(cnf_transformation,[],[f45]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_352,plain,
% 3.27/0.99      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
% 3.27/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.27/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_761,plain,
% 3.27/0.99      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(k2_relat_1(k6_relat_1(X0)))) = k6_relat_1(X0) ),
% 3.27/0.99      inference(superposition,[status(thm)],[c_350,c_352]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_762,plain,
% 3.27/0.99      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X0)) = k6_relat_1(X0) ),
% 3.27/0.99      inference(light_normalisation,[status(thm)],[c_761,c_8]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_926,plain,
% 3.27/0.99      ( k7_relat_1(k6_relat_1(X0),X0) = k6_relat_1(X0) ),
% 3.27/0.99      inference(superposition,[status(thm)],[c_827,c_762]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_2365,plain,
% 3.27/0.99      ( k7_relat_1(k6_relat_1(X0),k2_relat_1(k7_relat_1(k6_relat_1(X1),X2))) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) ),
% 3.27/0.99      inference(superposition,[status(thm)],[c_1684,c_1540]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_3409,plain,
% 3.27/0.99      ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X2),X1) ),
% 3.27/0.99      inference(superposition,[status(thm)],[c_2365,c_1540]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_3482,plain,
% 3.27/0.99      ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0) = k7_relat_1(k6_relat_1(X0),X1) ),
% 3.27/0.99      inference(superposition,[status(thm)],[c_926,c_3409]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_7104,plain,
% 3.27/0.99      ( k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k7_relat_1(k6_relat_1(X0),X1) ),
% 3.27/0.99      inference(light_normalisation,[status(thm)],[c_7099,c_3482]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_7335,plain,
% 3.27/0.99      ( k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k7_relat_1(k6_relat_1(X1),X0) ),
% 3.27/0.99      inference(superposition,[status(thm)],[c_1684,c_7104]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_7700,plain,
% 3.27/0.99      ( k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X1),X0) ),
% 3.27/0.99      inference(superposition,[status(thm)],[c_7335,c_7104]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_13,negated_conjecture,
% 3.27/0.99      ( k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) ),
% 3.27/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_580,plain,
% 3.27/0.99      ( k6_relat_1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK0))) != k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) ),
% 3.27/0.99      inference(demodulation,[status(thm)],[c_1,c_13]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_923,plain,
% 3.27/0.99      ( k6_relat_1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK0))) != k7_relat_1(k6_relat_1(sK0),sK1) ),
% 3.27/0.99      inference(demodulation,[status(thm)],[c_827,c_580]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_1410,plain,
% 3.27/0.99      ( k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(sK0),sK1))) != k7_relat_1(k6_relat_1(sK0),sK1) ),
% 3.27/0.99      inference(demodulation,[status(thm)],[c_1394,c_923]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_1863,plain,
% 3.27/0.99      ( k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(sK1),sK0))) != k7_relat_1(k6_relat_1(sK0),sK1) ),
% 3.27/0.99      inference(demodulation,[status(thm)],[c_1684,c_1410]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_7211,plain,
% 3.27/0.99      ( k7_relat_1(k6_relat_1(sK1),sK0) != k7_relat_1(k6_relat_1(sK0),sK1) ),
% 3.27/0.99      inference(demodulation,[status(thm)],[c_7104,c_1863]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_7813,plain,
% 3.27/0.99      ( k7_relat_1(k6_relat_1(sK1),sK0) != k7_relat_1(k6_relat_1(sK1),sK0) ),
% 3.27/0.99      inference(demodulation,[status(thm)],[c_7700,c_7211]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_8000,plain,
% 3.27/0.99      ( $false ),
% 3.27/0.99      inference(equality_resolution_simp,[status(thm)],[c_7813]) ).
% 3.27/0.99  
% 3.27/0.99  
% 3.27/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.27/0.99  
% 3.27/0.99  ------                               Statistics
% 3.27/0.99  
% 3.27/0.99  ------ General
% 3.27/0.99  
% 3.27/0.99  abstr_ref_over_cycles:                  0
% 3.27/0.99  abstr_ref_under_cycles:                 0
% 3.27/0.99  gc_basic_clause_elim:                   0
% 3.27/0.99  forced_gc_time:                         0
% 3.27/0.99  parsing_time:                           0.008
% 3.27/0.99  unif_index_cands_time:                  0.
% 3.27/0.99  unif_index_add_time:                    0.
% 3.27/0.99  orderings_time:                         0.
% 3.27/0.99  out_proof_time:                         0.006
% 3.27/0.99  total_time:                             0.255
% 3.27/0.99  num_of_symbols:                         43
% 3.27/0.99  num_of_terms:                           12267
% 3.27/0.99  
% 3.27/0.99  ------ Preprocessing
% 3.27/0.99  
% 3.27/0.99  num_of_splits:                          0
% 3.27/0.99  num_of_split_atoms:                     0
% 3.27/0.99  num_of_reused_defs:                     0
% 3.27/0.99  num_eq_ax_congr_red:                    6
% 3.27/0.99  num_of_sem_filtered_clauses:            1
% 3.27/0.99  num_of_subtypes:                        0
% 3.27/0.99  monotx_restored_types:                  0
% 3.27/0.99  sat_num_of_epr_types:                   0
% 3.27/0.99  sat_num_of_non_cyclic_types:            0
% 3.27/0.99  sat_guarded_non_collapsed_types:        0
% 3.27/0.99  num_pure_diseq_elim:                    0
% 3.27/0.99  simp_replaced_by:                       0
% 3.27/0.99  res_preprocessed:                       65
% 3.27/0.99  prep_upred:                             0
% 3.27/0.99  prep_unflattend:                        1
% 3.27/0.99  smt_new_axioms:                         0
% 3.27/0.99  pred_elim_cands:                        2
% 3.27/0.99  pred_elim:                              0
% 3.27/0.99  pred_elim_cl:                           0
% 3.27/0.99  pred_elim_cycles:                       1
% 3.27/0.99  merged_defs:                            0
% 3.27/0.99  merged_defs_ncl:                        0
% 3.27/0.99  bin_hyper_res:                          0
% 3.27/0.99  prep_cycles:                            3
% 3.27/0.99  pred_elim_time:                         0.
% 3.27/0.99  splitting_time:                         0.
% 3.27/0.99  sem_filter_time:                        0.
% 3.27/0.99  monotx_time:                            0.
% 3.27/0.99  subtype_inf_time:                       0.
% 3.27/0.99  
% 3.27/0.99  ------ Problem properties
% 3.27/0.99  
% 3.27/0.99  clauses:                                14
% 3.27/0.99  conjectures:                            1
% 3.27/0.99  epr:                                    0
% 3.27/0.99  horn:                                   14
% 3.27/0.99  ground:                                 1
% 3.27/0.99  unary:                                  6
% 3.27/0.99  binary:                                 5
% 3.27/0.99  lits:                                   26
% 3.27/0.99  lits_eq:                                11
% 3.27/0.99  fd_pure:                                0
% 3.27/0.99  fd_pseudo:                              0
% 3.27/0.99  fd_cond:                                0
% 3.27/0.99  fd_pseudo_cond:                         0
% 3.27/0.99  ac_symbols:                             0
% 3.27/0.99  
% 3.27/0.99  ------ Propositional Solver
% 3.27/0.99  
% 3.27/0.99  prop_solver_calls:                      25
% 3.27/0.99  prop_fast_solver_calls:                 386
% 3.27/0.99  smt_solver_calls:                       0
% 3.27/0.99  smt_fast_solver_calls:                  0
% 3.27/0.99  prop_num_of_clauses:                    3831
% 3.27/0.99  prop_preprocess_simplified:             8057
% 3.27/0.99  prop_fo_subsumed:                       1
% 3.27/0.99  prop_solver_time:                       0.
% 3.27/0.99  smt_solver_time:                        0.
% 3.27/0.99  smt_fast_solver_time:                   0.
% 3.27/0.99  prop_fast_solver_time:                  0.
% 3.27/0.99  prop_unsat_core_time:                   0.
% 3.27/0.99  
% 3.27/0.99  ------ QBF
% 3.27/0.99  
% 3.27/0.99  qbf_q_res:                              0
% 3.27/0.99  qbf_num_tautologies:                    0
% 3.27/0.99  qbf_prep_cycles:                        0
% 3.27/0.99  
% 3.27/0.99  ------ BMC1
% 3.27/0.99  
% 3.27/0.99  bmc1_current_bound:                     -1
% 3.27/0.99  bmc1_last_solved_bound:                 -1
% 3.27/0.99  bmc1_unsat_core_size:                   -1
% 3.27/0.99  bmc1_unsat_core_parents_size:           -1
% 3.27/0.99  bmc1_merge_next_fun:                    0
% 3.27/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.27/0.99  
% 3.27/0.99  ------ Instantiation
% 3.27/0.99  
% 3.27/0.99  inst_num_of_clauses:                    1194
% 3.27/0.99  inst_num_in_passive:                    627
% 3.27/0.99  inst_num_in_active:                     362
% 3.27/0.99  inst_num_in_unprocessed:                205
% 3.27/0.99  inst_num_of_loops:                      370
% 3.27/0.99  inst_num_of_learning_restarts:          0
% 3.27/0.99  inst_num_moves_active_passive:          6
% 3.27/0.99  inst_lit_activity:                      0
% 3.27/0.99  inst_lit_activity_moves:                0
% 3.27/0.99  inst_num_tautologies:                   0
% 3.27/0.99  inst_num_prop_implied:                  0
% 3.27/0.99  inst_num_existing_simplified:           0
% 3.27/0.99  inst_num_eq_res_simplified:             0
% 3.27/0.99  inst_num_child_elim:                    0
% 3.27/0.99  inst_num_of_dismatching_blockings:      312
% 3.27/0.99  inst_num_of_non_proper_insts:           706
% 3.27/0.99  inst_num_of_duplicates:                 0
% 3.27/0.99  inst_inst_num_from_inst_to_res:         0
% 3.27/0.99  inst_dismatching_checking_time:         0.
% 3.27/0.99  
% 3.27/0.99  ------ Resolution
% 3.27/0.99  
% 3.27/0.99  res_num_of_clauses:                     0
% 3.27/0.99  res_num_in_passive:                     0
% 3.27/0.99  res_num_in_active:                      0
% 3.27/0.99  res_num_of_loops:                       68
% 3.27/0.99  res_forward_subset_subsumed:            97
% 3.27/0.99  res_backward_subset_subsumed:           0
% 3.27/0.99  res_forward_subsumed:                   0
% 3.27/0.99  res_backward_subsumed:                  0
% 3.27/0.99  res_forward_subsumption_resolution:     0
% 3.27/0.99  res_backward_subsumption_resolution:    0
% 3.27/0.99  res_clause_to_clause_subsumption:       836
% 3.27/0.99  res_orphan_elimination:                 0
% 3.27/0.99  res_tautology_del:                      88
% 3.27/0.99  res_num_eq_res_simplified:              0
% 3.27/0.99  res_num_sel_changes:                    0
% 3.27/0.99  res_moves_from_active_to_pass:          0
% 3.27/0.99  
% 3.27/0.99  ------ Superposition
% 3.27/0.99  
% 3.27/0.99  sup_time_total:                         0.
% 3.27/0.99  sup_time_generating:                    0.
% 3.27/0.99  sup_time_sim_full:                      0.
% 3.27/0.99  sup_time_sim_immed:                     0.
% 3.27/0.99  
% 3.27/0.99  sup_num_of_clauses:                     252
% 3.27/0.99  sup_num_in_active:                      59
% 3.27/0.99  sup_num_in_passive:                     193
% 3.27/0.99  sup_num_of_loops:                       72
% 3.27/0.99  sup_fw_superposition:                   251
% 3.27/0.99  sup_bw_superposition:                   329
% 3.27/0.99  sup_immediate_simplified:               205
% 3.27/0.99  sup_given_eliminated:                   2
% 3.27/0.99  comparisons_done:                       0
% 3.27/0.99  comparisons_avoided:                    0
% 3.27/0.99  
% 3.27/0.99  ------ Simplifications
% 3.27/0.99  
% 3.27/0.99  
% 3.27/0.99  sim_fw_subset_subsumed:                 1
% 3.27/0.99  sim_bw_subset_subsumed:                 5
% 3.27/0.99  sim_fw_subsumed:                        13
% 3.27/0.99  sim_bw_subsumed:                        0
% 3.27/0.99  sim_fw_subsumption_res:                 2
% 3.27/0.99  sim_bw_subsumption_res:                 0
% 3.27/0.99  sim_tautology_del:                      3
% 3.27/0.99  sim_eq_tautology_del:                   26
% 3.27/0.99  sim_eq_res_simp:                        0
% 3.27/0.99  sim_fw_demodulated:                     72
% 3.27/0.99  sim_bw_demodulated:                     19
% 3.27/0.99  sim_light_normalised:                   139
% 3.27/0.99  sim_joinable_taut:                      0
% 3.27/0.99  sim_joinable_simp:                      0
% 3.27/0.99  sim_ac_normalised:                      0
% 3.27/0.99  sim_smt_subsumption:                    0
% 3.27/0.99  
%------------------------------------------------------------------------------
