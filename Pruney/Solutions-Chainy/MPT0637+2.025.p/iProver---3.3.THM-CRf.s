%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:49:59 EST 2020

% Result     : Theorem 6.89s
% Output     : CNFRefutation 6.89s
% Verified   : 
% Statistics : Number of formulae       :  122 (1560 expanded)
%              Number of clauses        :   66 ( 479 expanded)
%              Number of leaves         :   17 ( 404 expanded)
%              Depth                    :   20
%              Number of atoms          :  197 (2025 expanded)
%              Number of equality atoms :  136 (1484 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    3 (   2 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f48,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f33,f34])).

fof(f49,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f35,f48])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X0)) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f44,f49])).

fof(f11,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f50,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f31,f49])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0)) = k8_relat_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0)) = k8_relat_1(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0)) = k8_relat_1(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_enumset1(X1,X1,X1,k2_zfmisc_1(k1_relat_1(X1),X0))) = k8_relat_1(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f40,f49])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f51,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f32,f48,f48])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f37,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f37,f49])).

fof(f42,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f38,f49])).

fof(f16,conjecture,(
    ! [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
    inference(negated_conjecture,[],[f16])).

fof(f28,plain,(
    ? [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) != k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
    inference(ennf_transformation,[],[f17])).

fof(f29,plain,
    ( ? [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) != k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))
   => k6_relat_1(k3_xboole_0(sK0,sK1)) != k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    k6_relat_1(k3_xboole_0(sK0,sK1)) != k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f28,f29])).

fof(f47,plain,(
    k6_relat_1(k3_xboole_0(sK0,sK1)) != k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f30])).

fof(f56,plain,(
    k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) != k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) ),
    inference(definition_unfolding,[],[f47,f49])).

cnf(c_2,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_382,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_10,plain,
    ( ~ v1_relat_1(X0)
    | k1_setfam_1(k2_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_376,plain,
    ( k1_setfam_1(k2_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_791,plain,
    ( k1_setfam_1(k2_enumset1(k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(superposition,[status(thm)],[c_382,c_376])).

cnf(c_8,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_792,plain,
    ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(light_normalisation,[status(thm)],[c_791,c_8])).

cnf(c_0,plain,
    ( r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_383,plain,
    ( r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_796,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_792,c_383])).

cnf(c_12,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_374,plain,
    ( k7_relat_1(X0,X1) = X0
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1462,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0) = k7_relat_1(k6_relat_1(X0),X1)
    | v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_796,c_374])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | k1_setfam_1(k2_enumset1(X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),X1))) = k8_relat_1(X1,X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_378,plain,
    ( k1_setfam_1(k2_enumset1(X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),X1))) = k8_relat_1(X1,X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1,plain,
    ( k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_816,plain,
    ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
    inference(superposition,[status(thm)],[c_1,c_792])).

cnf(c_1493,plain,
    ( k1_relat_1(k7_relat_1(k6_relat_1(k2_zfmisc_1(k1_relat_1(X0),X1)),X0)) = k8_relat_1(X1,X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_378,c_816])).

cnf(c_1499,plain,
    ( k1_relat_1(k7_relat_1(k6_relat_1(k2_zfmisc_1(k1_relat_1(k6_relat_1(X0)),X1)),k6_relat_1(X0))) = k8_relat_1(X1,k6_relat_1(X0)) ),
    inference(superposition,[status(thm)],[c_382,c_1493])).

cnf(c_1511,plain,
    ( k1_relat_1(k7_relat_1(k6_relat_1(k2_zfmisc_1(X0,X1)),k6_relat_1(X0))) = k8_relat_1(X1,k6_relat_1(X0)) ),
    inference(light_normalisation,[status(thm)],[c_1499,c_8])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X1,X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_379,plain,
    ( k5_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X1,X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_925,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k8_relat_1(X1,k6_relat_1(X0)) ),
    inference(superposition,[status(thm)],[c_382,c_379])).

cnf(c_11,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_375,plain,
    ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_735,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(superposition,[status(thm)],[c_382,c_375])).

cnf(c_1132,plain,
    ( k8_relat_1(X0,k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(light_normalisation,[status(thm)],[c_925,c_735])).

cnf(c_1512,plain,
    ( k1_relat_1(k7_relat_1(k6_relat_1(k2_zfmisc_1(X0,X1)),k6_relat_1(X0))) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(demodulation,[status(thm)],[c_1511,c_1132])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_381,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1170,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X1),X0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_381,c_816])).

cnf(c_1691,plain,
    ( v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1512,c_1170])).

cnf(c_2113,plain,
    ( v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1691,c_382])).

cnf(c_15383,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1462,c_2113])).

cnf(c_585,plain,
    ( r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_383])).

cnf(c_795,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_792,c_585])).

cnf(c_7,plain,
    ( k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_9,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_relat_1(X1)) = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_377,plain,
    ( k5_relat_1(X0,k6_relat_1(X1)) = X0
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1424,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k6_relat_1(X0)
    | r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_377])).

cnf(c_1425,plain,
    ( k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X1)
    | r1_tarski(X1,X0) != iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1424,c_735])).

cnf(c_10141,plain,
    ( k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X1)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1425,c_382])).

cnf(c_10143,plain,
    ( k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(k6_relat_1(X1),X0))) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X1),X0))) ),
    inference(superposition,[status(thm)],[c_795,c_10141])).

cnf(c_876,plain,
    ( k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
    inference(superposition,[status(thm)],[c_816,c_792])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) = k7_relat_1(k7_relat_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_380,plain,
    ( k7_relat_1(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) = k7_relat_1(k7_relat_1(X0,X1),X2)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1611,plain,
    ( k7_relat_1(X0,k1_relat_1(k7_relat_1(k6_relat_1(X1),X2))) = k7_relat_1(k7_relat_1(X0,X2),X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_380,c_816])).

cnf(c_1617,plain,
    ( k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(k6_relat_1(X1),X2))) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X2),X1) ),
    inference(superposition,[status(thm)],[c_382,c_1611])).

cnf(c_2838,plain,
    ( k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(k6_relat_1(X1),X2))) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) ),
    inference(superposition,[status(thm)],[c_876,c_1617])).

cnf(c_12068,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X1),X0))) ),
    inference(superposition,[status(thm)],[c_10143,c_2838])).

cnf(c_15386,plain,
    ( k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(demodulation,[status(thm)],[c_15383,c_12068])).

cnf(c_13,negated_conjecture,
    ( k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) != k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_798,plain,
    ( k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(sK0),sK1))) != k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) ),
    inference(demodulation,[status(thm)],[c_792,c_13])).

cnf(c_1064,plain,
    ( k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(sK0),sK1))) != k7_relat_1(k6_relat_1(sK0),sK1) ),
    inference(demodulation,[status(thm)],[c_735,c_798])).

cnf(c_17168,plain,
    ( k7_relat_1(k6_relat_1(sK1),sK0) != k7_relat_1(k6_relat_1(sK0),sK1) ),
    inference(demodulation,[status(thm)],[c_15386,c_1064])).

cnf(c_1463,plain,
    ( k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X0)
    | r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8,c_374])).

cnf(c_40,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1636,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1463,c_40])).

cnf(c_1637,plain,
    ( k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X0)
    | r1_tarski(X0,X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_1636])).

cnf(c_1644,plain,
    ( k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X1) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
    inference(superposition,[status(thm)],[c_795,c_1637])).

cnf(c_3359,plain,
    ( k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X0) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X1),X0))) ),
    inference(superposition,[status(thm)],[c_876,c_1644])).

cnf(c_17178,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X1) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
    inference(demodulation,[status(thm)],[c_15386,c_3359])).

cnf(c_1461,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X1) = k7_relat_1(k6_relat_1(X0),X1)
    | v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_795,c_374])).

cnf(c_12303,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X1) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1461,c_2113])).

cnf(c_17202,plain,
    ( k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(light_normalisation,[status(thm)],[c_17178,c_12303,c_15386])).

cnf(c_17216,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_17168,c_17202])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:20:41 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 6.89/1.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.89/1.50  
% 6.89/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 6.89/1.50  
% 6.89/1.50  ------  iProver source info
% 6.89/1.50  
% 6.89/1.50  git: date: 2020-06-30 10:37:57 +0100
% 6.89/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 6.89/1.50  git: non_committed_changes: false
% 6.89/1.50  git: last_make_outside_of_git: false
% 6.89/1.50  
% 6.89/1.50  ------ 
% 6.89/1.50  
% 6.89/1.50  ------ Input Options
% 6.89/1.50  
% 6.89/1.50  --out_options                           all
% 6.89/1.50  --tptp_safe_out                         true
% 6.89/1.50  --problem_path                          ""
% 6.89/1.50  --include_path                          ""
% 6.89/1.50  --clausifier                            res/vclausify_rel
% 6.89/1.50  --clausifier_options                    --mode clausify
% 6.89/1.50  --stdin                                 false
% 6.89/1.50  --stats_out                             all
% 6.89/1.50  
% 6.89/1.50  ------ General Options
% 6.89/1.50  
% 6.89/1.50  --fof                                   false
% 6.89/1.50  --time_out_real                         305.
% 6.89/1.50  --time_out_virtual                      -1.
% 6.89/1.50  --symbol_type_check                     false
% 6.89/1.50  --clausify_out                          false
% 6.89/1.50  --sig_cnt_out                           false
% 6.89/1.50  --trig_cnt_out                          false
% 6.89/1.50  --trig_cnt_out_tolerance                1.
% 6.89/1.50  --trig_cnt_out_sk_spl                   false
% 6.89/1.50  --abstr_cl_out                          false
% 6.89/1.50  
% 6.89/1.50  ------ Global Options
% 6.89/1.50  
% 6.89/1.50  --schedule                              default
% 6.89/1.50  --add_important_lit                     false
% 6.89/1.50  --prop_solver_per_cl                    1000
% 6.89/1.50  --min_unsat_core                        false
% 6.89/1.50  --soft_assumptions                      false
% 6.89/1.50  --soft_lemma_size                       3
% 6.89/1.50  --prop_impl_unit_size                   0
% 6.89/1.50  --prop_impl_unit                        []
% 6.89/1.50  --share_sel_clauses                     true
% 6.89/1.50  --reset_solvers                         false
% 6.89/1.50  --bc_imp_inh                            [conj_cone]
% 6.89/1.50  --conj_cone_tolerance                   3.
% 6.89/1.50  --extra_neg_conj                        none
% 6.89/1.50  --large_theory_mode                     true
% 6.89/1.50  --prolific_symb_bound                   200
% 6.89/1.50  --lt_threshold                          2000
% 6.89/1.50  --clause_weak_htbl                      true
% 6.89/1.50  --gc_record_bc_elim                     false
% 6.89/1.50  
% 6.89/1.50  ------ Preprocessing Options
% 6.89/1.50  
% 6.89/1.50  --preprocessing_flag                    true
% 6.89/1.50  --time_out_prep_mult                    0.1
% 6.89/1.50  --splitting_mode                        input
% 6.89/1.50  --splitting_grd                         true
% 6.89/1.50  --splitting_cvd                         false
% 6.89/1.50  --splitting_cvd_svl                     false
% 6.89/1.50  --splitting_nvd                         32
% 6.89/1.50  --sub_typing                            true
% 6.89/1.50  --prep_gs_sim                           true
% 6.89/1.50  --prep_unflatten                        true
% 6.89/1.50  --prep_res_sim                          true
% 6.89/1.50  --prep_upred                            true
% 6.89/1.50  --prep_sem_filter                       exhaustive
% 6.89/1.50  --prep_sem_filter_out                   false
% 6.89/1.50  --pred_elim                             true
% 6.89/1.50  --res_sim_input                         true
% 6.89/1.50  --eq_ax_congr_red                       true
% 6.89/1.50  --pure_diseq_elim                       true
% 6.89/1.50  --brand_transform                       false
% 6.89/1.50  --non_eq_to_eq                          false
% 6.89/1.50  --prep_def_merge                        true
% 6.89/1.50  --prep_def_merge_prop_impl              false
% 6.89/1.50  --prep_def_merge_mbd                    true
% 6.89/1.50  --prep_def_merge_tr_red                 false
% 6.89/1.50  --prep_def_merge_tr_cl                  false
% 6.89/1.50  --smt_preprocessing                     true
% 6.89/1.50  --smt_ac_axioms                         fast
% 6.89/1.50  --preprocessed_out                      false
% 6.89/1.50  --preprocessed_stats                    false
% 6.89/1.50  
% 6.89/1.50  ------ Abstraction refinement Options
% 6.89/1.50  
% 6.89/1.50  --abstr_ref                             []
% 6.89/1.50  --abstr_ref_prep                        false
% 6.89/1.50  --abstr_ref_until_sat                   false
% 6.89/1.50  --abstr_ref_sig_restrict                funpre
% 6.89/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 6.89/1.50  --abstr_ref_under                       []
% 6.89/1.50  
% 6.89/1.50  ------ SAT Options
% 6.89/1.50  
% 6.89/1.50  --sat_mode                              false
% 6.89/1.50  --sat_fm_restart_options                ""
% 6.89/1.50  --sat_gr_def                            false
% 6.89/1.50  --sat_epr_types                         true
% 6.89/1.50  --sat_non_cyclic_types                  false
% 6.89/1.50  --sat_finite_models                     false
% 6.89/1.50  --sat_fm_lemmas                         false
% 6.89/1.50  --sat_fm_prep                           false
% 6.89/1.50  --sat_fm_uc_incr                        true
% 6.89/1.50  --sat_out_model                         small
% 6.89/1.50  --sat_out_clauses                       false
% 6.89/1.50  
% 6.89/1.50  ------ QBF Options
% 6.89/1.50  
% 6.89/1.50  --qbf_mode                              false
% 6.89/1.50  --qbf_elim_univ                         false
% 6.89/1.50  --qbf_dom_inst                          none
% 6.89/1.50  --qbf_dom_pre_inst                      false
% 6.89/1.50  --qbf_sk_in                             false
% 6.89/1.50  --qbf_pred_elim                         true
% 6.89/1.50  --qbf_split                             512
% 6.89/1.50  
% 6.89/1.50  ------ BMC1 Options
% 6.89/1.50  
% 6.89/1.50  --bmc1_incremental                      false
% 6.89/1.50  --bmc1_axioms                           reachable_all
% 6.89/1.50  --bmc1_min_bound                        0
% 6.89/1.50  --bmc1_max_bound                        -1
% 6.89/1.50  --bmc1_max_bound_default                -1
% 6.89/1.50  --bmc1_symbol_reachability              true
% 6.89/1.50  --bmc1_property_lemmas                  false
% 6.89/1.50  --bmc1_k_induction                      false
% 6.89/1.50  --bmc1_non_equiv_states                 false
% 6.89/1.50  --bmc1_deadlock                         false
% 6.89/1.50  --bmc1_ucm                              false
% 6.89/1.50  --bmc1_add_unsat_core                   none
% 6.89/1.50  --bmc1_unsat_core_children              false
% 6.89/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 6.89/1.50  --bmc1_out_stat                         full
% 6.89/1.50  --bmc1_ground_init                      false
% 6.89/1.50  --bmc1_pre_inst_next_state              false
% 6.89/1.50  --bmc1_pre_inst_state                   false
% 6.89/1.50  --bmc1_pre_inst_reach_state             false
% 6.89/1.50  --bmc1_out_unsat_core                   false
% 6.89/1.50  --bmc1_aig_witness_out                  false
% 6.89/1.50  --bmc1_verbose                          false
% 6.89/1.50  --bmc1_dump_clauses_tptp                false
% 6.89/1.50  --bmc1_dump_unsat_core_tptp             false
% 6.89/1.50  --bmc1_dump_file                        -
% 6.89/1.50  --bmc1_ucm_expand_uc_limit              128
% 6.89/1.50  --bmc1_ucm_n_expand_iterations          6
% 6.89/1.50  --bmc1_ucm_extend_mode                  1
% 6.89/1.50  --bmc1_ucm_init_mode                    2
% 6.89/1.50  --bmc1_ucm_cone_mode                    none
% 6.89/1.50  --bmc1_ucm_reduced_relation_type        0
% 6.89/1.50  --bmc1_ucm_relax_model                  4
% 6.89/1.50  --bmc1_ucm_full_tr_after_sat            true
% 6.89/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 6.89/1.50  --bmc1_ucm_layered_model                none
% 6.89/1.50  --bmc1_ucm_max_lemma_size               10
% 6.89/1.50  
% 6.89/1.50  ------ AIG Options
% 6.89/1.50  
% 6.89/1.50  --aig_mode                              false
% 6.89/1.50  
% 6.89/1.50  ------ Instantiation Options
% 6.89/1.50  
% 6.89/1.50  --instantiation_flag                    true
% 6.89/1.50  --inst_sos_flag                         false
% 6.89/1.50  --inst_sos_phase                        true
% 6.89/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.89/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.89/1.50  --inst_lit_sel_side                     num_symb
% 6.89/1.50  --inst_solver_per_active                1400
% 6.89/1.50  --inst_solver_calls_frac                1.
% 6.89/1.50  --inst_passive_queue_type               priority_queues
% 6.89/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.89/1.50  --inst_passive_queues_freq              [25;2]
% 6.89/1.50  --inst_dismatching                      true
% 6.89/1.50  --inst_eager_unprocessed_to_passive     true
% 6.89/1.50  --inst_prop_sim_given                   true
% 6.89/1.50  --inst_prop_sim_new                     false
% 6.89/1.50  --inst_subs_new                         false
% 6.89/1.50  --inst_eq_res_simp                      false
% 6.89/1.50  --inst_subs_given                       false
% 6.89/1.50  --inst_orphan_elimination               true
% 6.89/1.50  --inst_learning_loop_flag               true
% 6.89/1.50  --inst_learning_start                   3000
% 6.89/1.50  --inst_learning_factor                  2
% 6.89/1.50  --inst_start_prop_sim_after_learn       3
% 6.89/1.50  --inst_sel_renew                        solver
% 6.89/1.50  --inst_lit_activity_flag                true
% 6.89/1.50  --inst_restr_to_given                   false
% 6.89/1.50  --inst_activity_threshold               500
% 6.89/1.50  --inst_out_proof                        true
% 6.89/1.50  
% 6.89/1.50  ------ Resolution Options
% 6.89/1.50  
% 6.89/1.50  --resolution_flag                       true
% 6.89/1.50  --res_lit_sel                           adaptive
% 6.89/1.50  --res_lit_sel_side                      none
% 6.89/1.50  --res_ordering                          kbo
% 6.89/1.50  --res_to_prop_solver                    active
% 6.89/1.50  --res_prop_simpl_new                    false
% 6.89/1.50  --res_prop_simpl_given                  true
% 6.89/1.50  --res_passive_queue_type                priority_queues
% 6.89/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.89/1.50  --res_passive_queues_freq               [15;5]
% 6.89/1.50  --res_forward_subs                      full
% 6.89/1.50  --res_backward_subs                     full
% 6.89/1.50  --res_forward_subs_resolution           true
% 6.89/1.50  --res_backward_subs_resolution          true
% 6.89/1.50  --res_orphan_elimination                true
% 6.89/1.50  --res_time_limit                        2.
% 6.89/1.50  --res_out_proof                         true
% 6.89/1.50  
% 6.89/1.50  ------ Superposition Options
% 6.89/1.50  
% 6.89/1.50  --superposition_flag                    true
% 6.89/1.50  --sup_passive_queue_type                priority_queues
% 6.89/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.89/1.50  --sup_passive_queues_freq               [8;1;4]
% 6.89/1.50  --demod_completeness_check              fast
% 6.89/1.50  --demod_use_ground                      true
% 6.89/1.50  --sup_to_prop_solver                    passive
% 6.89/1.50  --sup_prop_simpl_new                    true
% 6.89/1.50  --sup_prop_simpl_given                  true
% 6.89/1.50  --sup_fun_splitting                     false
% 6.89/1.50  --sup_smt_interval                      50000
% 6.89/1.50  
% 6.89/1.50  ------ Superposition Simplification Setup
% 6.89/1.50  
% 6.89/1.50  --sup_indices_passive                   []
% 6.89/1.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.89/1.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.89/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.89/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 6.89/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.89/1.50  --sup_full_bw                           [BwDemod]
% 6.89/1.50  --sup_immed_triv                        [TrivRules]
% 6.89/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.89/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.89/1.50  --sup_immed_bw_main                     []
% 6.89/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.89/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 6.89/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.89/1.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.89/1.50  
% 6.89/1.50  ------ Combination Options
% 6.89/1.50  
% 6.89/1.50  --comb_res_mult                         3
% 6.89/1.50  --comb_sup_mult                         2
% 6.89/1.50  --comb_inst_mult                        10
% 6.89/1.50  
% 6.89/1.50  ------ Debug Options
% 6.89/1.50  
% 6.89/1.50  --dbg_backtrace                         false
% 6.89/1.50  --dbg_dump_prop_clauses                 false
% 6.89/1.50  --dbg_dump_prop_clauses_file            -
% 6.89/1.50  --dbg_out_stat                          false
% 6.89/1.50  ------ Parsing...
% 6.89/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 6.89/1.50  
% 6.89/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 6.89/1.50  
% 6.89/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 6.89/1.50  
% 6.89/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 6.89/1.50  ------ Proving...
% 6.89/1.50  ------ Problem Properties 
% 6.89/1.50  
% 6.89/1.50  
% 6.89/1.50  clauses                                 14
% 6.89/1.50  conjectures                             1
% 6.89/1.50  EPR                                     0
% 6.89/1.50  Horn                                    14
% 6.89/1.50  unary                                   6
% 6.89/1.50  binary                                  6
% 6.89/1.50  lits                                    24
% 6.89/1.50  lits eq                                 11
% 6.89/1.50  fd_pure                                 0
% 6.89/1.50  fd_pseudo                               0
% 6.89/1.50  fd_cond                                 0
% 6.89/1.50  fd_pseudo_cond                          0
% 6.89/1.50  AC symbols                              0
% 6.89/1.50  
% 6.89/1.50  ------ Schedule dynamic 5 is on 
% 6.89/1.50  
% 6.89/1.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 6.89/1.50  
% 6.89/1.50  
% 6.89/1.50  ------ 
% 6.89/1.50  Current options:
% 6.89/1.50  ------ 
% 6.89/1.50  
% 6.89/1.50  ------ Input Options
% 6.89/1.50  
% 6.89/1.50  --out_options                           all
% 6.89/1.50  --tptp_safe_out                         true
% 6.89/1.50  --problem_path                          ""
% 6.89/1.50  --include_path                          ""
% 6.89/1.50  --clausifier                            res/vclausify_rel
% 6.89/1.50  --clausifier_options                    --mode clausify
% 6.89/1.50  --stdin                                 false
% 6.89/1.50  --stats_out                             all
% 6.89/1.50  
% 6.89/1.50  ------ General Options
% 6.89/1.50  
% 6.89/1.50  --fof                                   false
% 6.89/1.50  --time_out_real                         305.
% 6.89/1.50  --time_out_virtual                      -1.
% 6.89/1.50  --symbol_type_check                     false
% 6.89/1.50  --clausify_out                          false
% 6.89/1.50  --sig_cnt_out                           false
% 6.89/1.50  --trig_cnt_out                          false
% 6.89/1.50  --trig_cnt_out_tolerance                1.
% 6.89/1.50  --trig_cnt_out_sk_spl                   false
% 6.89/1.50  --abstr_cl_out                          false
% 6.89/1.50  
% 6.89/1.50  ------ Global Options
% 6.89/1.50  
% 6.89/1.50  --schedule                              default
% 6.89/1.50  --add_important_lit                     false
% 6.89/1.50  --prop_solver_per_cl                    1000
% 6.89/1.50  --min_unsat_core                        false
% 6.89/1.50  --soft_assumptions                      false
% 6.89/1.50  --soft_lemma_size                       3
% 6.89/1.50  --prop_impl_unit_size                   0
% 6.89/1.50  --prop_impl_unit                        []
% 6.89/1.50  --share_sel_clauses                     true
% 6.89/1.50  --reset_solvers                         false
% 6.89/1.50  --bc_imp_inh                            [conj_cone]
% 6.89/1.50  --conj_cone_tolerance                   3.
% 6.89/1.50  --extra_neg_conj                        none
% 6.89/1.50  --large_theory_mode                     true
% 6.89/1.50  --prolific_symb_bound                   200
% 6.89/1.50  --lt_threshold                          2000
% 6.89/1.50  --clause_weak_htbl                      true
% 6.89/1.50  --gc_record_bc_elim                     false
% 6.89/1.50  
% 6.89/1.50  ------ Preprocessing Options
% 6.89/1.50  
% 6.89/1.50  --preprocessing_flag                    true
% 6.89/1.50  --time_out_prep_mult                    0.1
% 6.89/1.50  --splitting_mode                        input
% 6.89/1.50  --splitting_grd                         true
% 6.89/1.50  --splitting_cvd                         false
% 6.89/1.50  --splitting_cvd_svl                     false
% 6.89/1.50  --splitting_nvd                         32
% 6.89/1.50  --sub_typing                            true
% 6.89/1.50  --prep_gs_sim                           true
% 6.89/1.50  --prep_unflatten                        true
% 6.89/1.50  --prep_res_sim                          true
% 6.89/1.50  --prep_upred                            true
% 6.89/1.50  --prep_sem_filter                       exhaustive
% 6.89/1.50  --prep_sem_filter_out                   false
% 6.89/1.50  --pred_elim                             true
% 6.89/1.50  --res_sim_input                         true
% 6.89/1.50  --eq_ax_congr_red                       true
% 6.89/1.50  --pure_diseq_elim                       true
% 6.89/1.50  --brand_transform                       false
% 6.89/1.50  --non_eq_to_eq                          false
% 6.89/1.50  --prep_def_merge                        true
% 6.89/1.50  --prep_def_merge_prop_impl              false
% 6.89/1.50  --prep_def_merge_mbd                    true
% 6.89/1.50  --prep_def_merge_tr_red                 false
% 6.89/1.50  --prep_def_merge_tr_cl                  false
% 6.89/1.50  --smt_preprocessing                     true
% 6.89/1.50  --smt_ac_axioms                         fast
% 6.89/1.50  --preprocessed_out                      false
% 6.89/1.50  --preprocessed_stats                    false
% 6.89/1.50  
% 6.89/1.50  ------ Abstraction refinement Options
% 6.89/1.50  
% 6.89/1.50  --abstr_ref                             []
% 6.89/1.50  --abstr_ref_prep                        false
% 6.89/1.50  --abstr_ref_until_sat                   false
% 6.89/1.50  --abstr_ref_sig_restrict                funpre
% 6.89/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 6.89/1.50  --abstr_ref_under                       []
% 6.89/1.50  
% 6.89/1.50  ------ SAT Options
% 6.89/1.50  
% 6.89/1.50  --sat_mode                              false
% 6.89/1.50  --sat_fm_restart_options                ""
% 6.89/1.50  --sat_gr_def                            false
% 6.89/1.50  --sat_epr_types                         true
% 6.89/1.50  --sat_non_cyclic_types                  false
% 6.89/1.50  --sat_finite_models                     false
% 6.89/1.50  --sat_fm_lemmas                         false
% 6.89/1.50  --sat_fm_prep                           false
% 6.89/1.50  --sat_fm_uc_incr                        true
% 6.89/1.50  --sat_out_model                         small
% 6.89/1.50  --sat_out_clauses                       false
% 6.89/1.50  
% 6.89/1.50  ------ QBF Options
% 6.89/1.50  
% 6.89/1.50  --qbf_mode                              false
% 6.89/1.50  --qbf_elim_univ                         false
% 6.89/1.50  --qbf_dom_inst                          none
% 6.89/1.50  --qbf_dom_pre_inst                      false
% 6.89/1.50  --qbf_sk_in                             false
% 6.89/1.50  --qbf_pred_elim                         true
% 6.89/1.50  --qbf_split                             512
% 6.89/1.50  
% 6.89/1.50  ------ BMC1 Options
% 6.89/1.50  
% 6.89/1.50  --bmc1_incremental                      false
% 6.89/1.50  --bmc1_axioms                           reachable_all
% 6.89/1.50  --bmc1_min_bound                        0
% 6.89/1.50  --bmc1_max_bound                        -1
% 6.89/1.50  --bmc1_max_bound_default                -1
% 6.89/1.50  --bmc1_symbol_reachability              true
% 6.89/1.50  --bmc1_property_lemmas                  false
% 6.89/1.50  --bmc1_k_induction                      false
% 6.89/1.50  --bmc1_non_equiv_states                 false
% 6.89/1.50  --bmc1_deadlock                         false
% 6.89/1.50  --bmc1_ucm                              false
% 6.89/1.50  --bmc1_add_unsat_core                   none
% 6.89/1.50  --bmc1_unsat_core_children              false
% 6.89/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 6.89/1.50  --bmc1_out_stat                         full
% 6.89/1.50  --bmc1_ground_init                      false
% 6.89/1.50  --bmc1_pre_inst_next_state              false
% 6.89/1.50  --bmc1_pre_inst_state                   false
% 6.89/1.50  --bmc1_pre_inst_reach_state             false
% 6.89/1.50  --bmc1_out_unsat_core                   false
% 6.89/1.50  --bmc1_aig_witness_out                  false
% 6.89/1.50  --bmc1_verbose                          false
% 6.89/1.50  --bmc1_dump_clauses_tptp                false
% 6.89/1.50  --bmc1_dump_unsat_core_tptp             false
% 6.89/1.50  --bmc1_dump_file                        -
% 6.89/1.50  --bmc1_ucm_expand_uc_limit              128
% 6.89/1.50  --bmc1_ucm_n_expand_iterations          6
% 6.89/1.50  --bmc1_ucm_extend_mode                  1
% 6.89/1.50  --bmc1_ucm_init_mode                    2
% 6.89/1.50  --bmc1_ucm_cone_mode                    none
% 6.89/1.50  --bmc1_ucm_reduced_relation_type        0
% 6.89/1.50  --bmc1_ucm_relax_model                  4
% 6.89/1.50  --bmc1_ucm_full_tr_after_sat            true
% 6.89/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 6.89/1.50  --bmc1_ucm_layered_model                none
% 6.89/1.50  --bmc1_ucm_max_lemma_size               10
% 6.89/1.50  
% 6.89/1.50  ------ AIG Options
% 6.89/1.50  
% 6.89/1.50  --aig_mode                              false
% 6.89/1.50  
% 6.89/1.50  ------ Instantiation Options
% 6.89/1.50  
% 6.89/1.50  --instantiation_flag                    true
% 6.89/1.50  --inst_sos_flag                         false
% 6.89/1.50  --inst_sos_phase                        true
% 6.89/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.89/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.89/1.50  --inst_lit_sel_side                     none
% 6.89/1.50  --inst_solver_per_active                1400
% 6.89/1.50  --inst_solver_calls_frac                1.
% 6.89/1.50  --inst_passive_queue_type               priority_queues
% 6.89/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.89/1.50  --inst_passive_queues_freq              [25;2]
% 6.89/1.50  --inst_dismatching                      true
% 6.89/1.50  --inst_eager_unprocessed_to_passive     true
% 6.89/1.50  --inst_prop_sim_given                   true
% 6.89/1.50  --inst_prop_sim_new                     false
% 6.89/1.50  --inst_subs_new                         false
% 6.89/1.50  --inst_eq_res_simp                      false
% 6.89/1.50  --inst_subs_given                       false
% 6.89/1.50  --inst_orphan_elimination               true
% 6.89/1.50  --inst_learning_loop_flag               true
% 6.89/1.50  --inst_learning_start                   3000
% 6.89/1.50  --inst_learning_factor                  2
% 6.89/1.50  --inst_start_prop_sim_after_learn       3
% 6.89/1.50  --inst_sel_renew                        solver
% 6.89/1.50  --inst_lit_activity_flag                true
% 6.89/1.50  --inst_restr_to_given                   false
% 6.89/1.50  --inst_activity_threshold               500
% 6.89/1.50  --inst_out_proof                        true
% 6.89/1.50  
% 6.89/1.50  ------ Resolution Options
% 6.89/1.50  
% 6.89/1.50  --resolution_flag                       false
% 6.89/1.50  --res_lit_sel                           adaptive
% 6.89/1.50  --res_lit_sel_side                      none
% 6.89/1.50  --res_ordering                          kbo
% 6.89/1.50  --res_to_prop_solver                    active
% 6.89/1.50  --res_prop_simpl_new                    false
% 6.89/1.50  --res_prop_simpl_given                  true
% 6.89/1.50  --res_passive_queue_type                priority_queues
% 6.89/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.89/1.50  --res_passive_queues_freq               [15;5]
% 6.89/1.50  --res_forward_subs                      full
% 6.89/1.50  --res_backward_subs                     full
% 6.89/1.50  --res_forward_subs_resolution           true
% 6.89/1.50  --res_backward_subs_resolution          true
% 6.89/1.50  --res_orphan_elimination                true
% 6.89/1.50  --res_time_limit                        2.
% 6.89/1.50  --res_out_proof                         true
% 6.89/1.50  
% 6.89/1.50  ------ Superposition Options
% 6.89/1.50  
% 6.89/1.50  --superposition_flag                    true
% 6.89/1.50  --sup_passive_queue_type                priority_queues
% 6.89/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.89/1.50  --sup_passive_queues_freq               [8;1;4]
% 6.89/1.50  --demod_completeness_check              fast
% 6.89/1.50  --demod_use_ground                      true
% 6.89/1.50  --sup_to_prop_solver                    passive
% 6.89/1.50  --sup_prop_simpl_new                    true
% 6.89/1.50  --sup_prop_simpl_given                  true
% 6.89/1.50  --sup_fun_splitting                     false
% 6.89/1.50  --sup_smt_interval                      50000
% 6.89/1.50  
% 6.89/1.50  ------ Superposition Simplification Setup
% 6.89/1.50  
% 6.89/1.50  --sup_indices_passive                   []
% 6.89/1.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.89/1.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.89/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.89/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 6.89/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.89/1.50  --sup_full_bw                           [BwDemod]
% 6.89/1.50  --sup_immed_triv                        [TrivRules]
% 6.89/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.89/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.89/1.50  --sup_immed_bw_main                     []
% 6.89/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.89/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 6.89/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.89/1.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.89/1.50  
% 6.89/1.50  ------ Combination Options
% 6.89/1.50  
% 6.89/1.50  --comb_res_mult                         3
% 6.89/1.50  --comb_sup_mult                         2
% 6.89/1.50  --comb_inst_mult                        10
% 6.89/1.50  
% 6.89/1.50  ------ Debug Options
% 6.89/1.50  
% 6.89/1.50  --dbg_backtrace                         false
% 6.89/1.50  --dbg_dump_prop_clauses                 false
% 6.89/1.50  --dbg_dump_prop_clauses_file            -
% 6.89/1.50  --dbg_out_stat                          false
% 6.89/1.50  
% 6.89/1.50  
% 6.89/1.50  
% 6.89/1.50  
% 6.89/1.50  ------ Proving...
% 6.89/1.50  
% 6.89/1.50  
% 6.89/1.50  % SZS status Theorem for theBenchmark.p
% 6.89/1.50  
% 6.89/1.50   Resolution empty clause
% 6.89/1.50  
% 6.89/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 6.89/1.50  
% 6.89/1.50  fof(f6,axiom,(
% 6.89/1.50    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 6.89/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.89/1.50  
% 6.89/1.50  fof(f36,plain,(
% 6.89/1.50    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 6.89/1.50    inference(cnf_transformation,[],[f6])).
% 6.89/1.50  
% 6.89/1.50  fof(f13,axiom,(
% 6.89/1.50    ! [X0,X1] : (v1_relat_1(X1) => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)))),
% 6.89/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.89/1.50  
% 6.89/1.50  fof(f24,plain,(
% 6.89/1.50    ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 6.89/1.50    inference(ennf_transformation,[],[f13])).
% 6.89/1.50  
% 6.89/1.50  fof(f44,plain,(
% 6.89/1.50    ( ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 6.89/1.50    inference(cnf_transformation,[],[f24])).
% 6.89/1.50  
% 6.89/1.50  fof(f5,axiom,(
% 6.89/1.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 6.89/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.89/1.50  
% 6.89/1.50  fof(f35,plain,(
% 6.89/1.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 6.89/1.50    inference(cnf_transformation,[],[f5])).
% 6.89/1.50  
% 6.89/1.50  fof(f3,axiom,(
% 6.89/1.50    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 6.89/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.89/1.50  
% 6.89/1.50  fof(f33,plain,(
% 6.89/1.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 6.89/1.50    inference(cnf_transformation,[],[f3])).
% 6.89/1.50  
% 6.89/1.50  fof(f4,axiom,(
% 6.89/1.50    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 6.89/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.89/1.50  
% 6.89/1.50  fof(f34,plain,(
% 6.89/1.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 6.89/1.50    inference(cnf_transformation,[],[f4])).
% 6.89/1.50  
% 6.89/1.50  fof(f48,plain,(
% 6.89/1.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 6.89/1.50    inference(definition_unfolding,[],[f33,f34])).
% 6.89/1.50  
% 6.89/1.50  fof(f49,plain,(
% 6.89/1.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 6.89/1.50    inference(definition_unfolding,[],[f35,f48])).
% 6.89/1.50  
% 6.89/1.50  fof(f55,plain,(
% 6.89/1.50    ( ! [X0,X1] : (k1_setfam_1(k2_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X0)) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 6.89/1.50    inference(definition_unfolding,[],[f44,f49])).
% 6.89/1.50  
% 6.89/1.50  fof(f11,axiom,(
% 6.89/1.50    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 6.89/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.89/1.50  
% 6.89/1.50  fof(f41,plain,(
% 6.89/1.50    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 6.89/1.50    inference(cnf_transformation,[],[f11])).
% 6.89/1.50  
% 6.89/1.50  fof(f1,axiom,(
% 6.89/1.50    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 6.89/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.89/1.50  
% 6.89/1.50  fof(f31,plain,(
% 6.89/1.50    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 6.89/1.50    inference(cnf_transformation,[],[f1])).
% 6.89/1.50  
% 6.89/1.50  fof(f50,plain,(
% 6.89/1.50    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0)) )),
% 6.89/1.50    inference(definition_unfolding,[],[f31,f49])).
% 6.89/1.50  
% 6.89/1.50  fof(f15,axiom,(
% 6.89/1.50    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 6.89/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.89/1.50  
% 6.89/1.50  fof(f26,plain,(
% 6.89/1.50    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 6.89/1.50    inference(ennf_transformation,[],[f15])).
% 6.89/1.50  
% 6.89/1.50  fof(f27,plain,(
% 6.89/1.50    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 6.89/1.50    inference(flattening,[],[f26])).
% 6.89/1.50  
% 6.89/1.50  fof(f46,plain,(
% 6.89/1.50    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 6.89/1.50    inference(cnf_transformation,[],[f27])).
% 6.89/1.50  
% 6.89/1.50  fof(f10,axiom,(
% 6.89/1.50    ! [X0,X1] : (v1_relat_1(X1) => k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0)) = k8_relat_1(X0,X1))),
% 6.89/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.89/1.50  
% 6.89/1.50  fof(f21,plain,(
% 6.89/1.50    ! [X0,X1] : (k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0)) = k8_relat_1(X0,X1) | ~v1_relat_1(X1))),
% 6.89/1.50    inference(ennf_transformation,[],[f10])).
% 6.89/1.50  
% 6.89/1.50  fof(f40,plain,(
% 6.89/1.50    ( ! [X0,X1] : (k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0)) = k8_relat_1(X0,X1) | ~v1_relat_1(X1)) )),
% 6.89/1.50    inference(cnf_transformation,[],[f21])).
% 6.89/1.50  
% 6.89/1.50  fof(f54,plain,(
% 6.89/1.50    ( ! [X0,X1] : (k1_setfam_1(k2_enumset1(X1,X1,X1,k2_zfmisc_1(k1_relat_1(X1),X0))) = k8_relat_1(X0,X1) | ~v1_relat_1(X1)) )),
% 6.89/1.50    inference(definition_unfolding,[],[f40,f49])).
% 6.89/1.50  
% 6.89/1.50  fof(f2,axiom,(
% 6.89/1.50    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 6.89/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.89/1.50  
% 6.89/1.50  fof(f32,plain,(
% 6.89/1.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 6.89/1.50    inference(cnf_transformation,[],[f2])).
% 6.89/1.50  
% 6.89/1.50  fof(f51,plain,(
% 6.89/1.50    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0)) )),
% 6.89/1.50    inference(definition_unfolding,[],[f32,f48,f48])).
% 6.89/1.50  
% 6.89/1.50  fof(f9,axiom,(
% 6.89/1.50    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 6.89/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.89/1.50  
% 6.89/1.50  fof(f20,plain,(
% 6.89/1.50    ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 6.89/1.50    inference(ennf_transformation,[],[f9])).
% 6.89/1.50  
% 6.89/1.50  fof(f39,plain,(
% 6.89/1.50    ( ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1)) )),
% 6.89/1.50    inference(cnf_transformation,[],[f20])).
% 6.89/1.50  
% 6.89/1.50  fof(f14,axiom,(
% 6.89/1.50    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 6.89/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.89/1.50  
% 6.89/1.50  fof(f25,plain,(
% 6.89/1.50    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 6.89/1.50    inference(ennf_transformation,[],[f14])).
% 6.89/1.50  
% 6.89/1.50  fof(f45,plain,(
% 6.89/1.50    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 6.89/1.50    inference(cnf_transformation,[],[f25])).
% 6.89/1.50  
% 6.89/1.50  fof(f7,axiom,(
% 6.89/1.50    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k3_xboole_0(X0,X1)))),
% 6.89/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.89/1.50  
% 6.89/1.50  fof(f18,plain,(
% 6.89/1.50    ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 6.89/1.50    inference(ennf_transformation,[],[f7])).
% 6.89/1.50  
% 6.89/1.50  fof(f37,plain,(
% 6.89/1.50    ( ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0)) )),
% 6.89/1.50    inference(cnf_transformation,[],[f18])).
% 6.89/1.50  
% 6.89/1.50  fof(f52,plain,(
% 6.89/1.50    ( ! [X0,X1] : (v1_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) | ~v1_relat_1(X0)) )),
% 6.89/1.50    inference(definition_unfolding,[],[f37,f49])).
% 6.89/1.50  
% 6.89/1.50  fof(f42,plain,(
% 6.89/1.50    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 6.89/1.50    inference(cnf_transformation,[],[f11])).
% 6.89/1.50  
% 6.89/1.50  fof(f12,axiom,(
% 6.89/1.50    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 6.89/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.89/1.50  
% 6.89/1.50  fof(f22,plain,(
% 6.89/1.50    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 6.89/1.50    inference(ennf_transformation,[],[f12])).
% 6.89/1.50  
% 6.89/1.50  fof(f23,plain,(
% 6.89/1.50    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 6.89/1.50    inference(flattening,[],[f22])).
% 6.89/1.50  
% 6.89/1.50  fof(f43,plain,(
% 6.89/1.50    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 6.89/1.50    inference(cnf_transformation,[],[f23])).
% 6.89/1.50  
% 6.89/1.50  fof(f8,axiom,(
% 6.89/1.50    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1))),
% 6.89/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.89/1.50  
% 6.89/1.50  fof(f19,plain,(
% 6.89/1.50    ! [X0,X1,X2] : (k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2))),
% 6.89/1.50    inference(ennf_transformation,[],[f8])).
% 6.89/1.50  
% 6.89/1.50  fof(f38,plain,(
% 6.89/1.50    ( ! [X2,X0,X1] : (k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 6.89/1.50    inference(cnf_transformation,[],[f19])).
% 6.89/1.50  
% 6.89/1.50  fof(f53,plain,(
% 6.89/1.50    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) | ~v1_relat_1(X2)) )),
% 6.89/1.50    inference(definition_unfolding,[],[f38,f49])).
% 6.89/1.50  
% 6.89/1.50  fof(f16,conjecture,(
% 6.89/1.50    ! [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))),
% 6.89/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.89/1.50  
% 6.89/1.50  fof(f17,negated_conjecture,(
% 6.89/1.50    ~! [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))),
% 6.89/1.50    inference(negated_conjecture,[],[f16])).
% 6.89/1.50  
% 6.89/1.50  fof(f28,plain,(
% 6.89/1.50    ? [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) != k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))),
% 6.89/1.50    inference(ennf_transformation,[],[f17])).
% 6.89/1.50  
% 6.89/1.50  fof(f29,plain,(
% 6.89/1.50    ? [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) != k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) => k6_relat_1(k3_xboole_0(sK0,sK1)) != k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0))),
% 6.89/1.50    introduced(choice_axiom,[])).
% 6.89/1.50  
% 6.89/1.50  fof(f30,plain,(
% 6.89/1.50    k6_relat_1(k3_xboole_0(sK0,sK1)) != k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0))),
% 6.89/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f28,f29])).
% 6.89/1.50  
% 6.89/1.50  fof(f47,plain,(
% 6.89/1.50    k6_relat_1(k3_xboole_0(sK0,sK1)) != k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0))),
% 6.89/1.50    inference(cnf_transformation,[],[f30])).
% 6.89/1.50  
% 6.89/1.50  fof(f56,plain,(
% 6.89/1.50    k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) != k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0))),
% 6.89/1.50    inference(definition_unfolding,[],[f47,f49])).
% 6.89/1.50  
% 6.89/1.50  cnf(c_2,plain,
% 6.89/1.50      ( v1_relat_1(k6_relat_1(X0)) ),
% 6.89/1.50      inference(cnf_transformation,[],[f36]) ).
% 6.89/1.50  
% 6.89/1.50  cnf(c_382,plain,
% 6.89/1.50      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 6.89/1.50      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 6.89/1.50  
% 6.89/1.50  cnf(c_10,plain,
% 6.89/1.50      ( ~ v1_relat_1(X0)
% 6.89/1.50      | k1_setfam_1(k2_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1)) ),
% 6.89/1.50      inference(cnf_transformation,[],[f55]) ).
% 6.89/1.50  
% 6.89/1.50  cnf(c_376,plain,
% 6.89/1.50      ( k1_setfam_1(k2_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1))
% 6.89/1.50      | v1_relat_1(X0) != iProver_top ),
% 6.89/1.50      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 6.89/1.50  
% 6.89/1.50  cnf(c_791,plain,
% 6.89/1.50      ( k1_setfam_1(k2_enumset1(k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
% 6.89/1.50      inference(superposition,[status(thm)],[c_382,c_376]) ).
% 6.89/1.50  
% 6.89/1.50  cnf(c_8,plain,
% 6.89/1.50      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 6.89/1.50      inference(cnf_transformation,[],[f41]) ).
% 6.89/1.50  
% 6.89/1.50  cnf(c_792,plain,
% 6.89/1.50      ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
% 6.89/1.50      inference(light_normalisation,[status(thm)],[c_791,c_8]) ).
% 6.89/1.50  
% 6.89/1.50  cnf(c_0,plain,
% 6.89/1.50      ( r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0) ),
% 6.89/1.50      inference(cnf_transformation,[],[f50]) ).
% 6.89/1.50  
% 6.89/1.50  cnf(c_383,plain,
% 6.89/1.50      ( r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0) = iProver_top ),
% 6.89/1.50      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 6.89/1.50  
% 6.89/1.50  cnf(c_796,plain,
% 6.89/1.50      ( r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X0) = iProver_top ),
% 6.89/1.50      inference(demodulation,[status(thm)],[c_792,c_383]) ).
% 6.89/1.50  
% 6.89/1.50  cnf(c_12,plain,
% 6.89/1.50      ( ~ r1_tarski(k1_relat_1(X0),X1)
% 6.89/1.50      | ~ v1_relat_1(X0)
% 6.89/1.50      | k7_relat_1(X0,X1) = X0 ),
% 6.89/1.50      inference(cnf_transformation,[],[f46]) ).
% 6.89/1.50  
% 6.89/1.50  cnf(c_374,plain,
% 6.89/1.50      ( k7_relat_1(X0,X1) = X0
% 6.89/1.50      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 6.89/1.50      | v1_relat_1(X0) != iProver_top ),
% 6.89/1.50      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 6.89/1.50  
% 6.89/1.50  cnf(c_1462,plain,
% 6.89/1.50      ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0) = k7_relat_1(k6_relat_1(X0),X1)
% 6.89/1.50      | v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) != iProver_top ),
% 6.89/1.50      inference(superposition,[status(thm)],[c_796,c_374]) ).
% 6.89/1.50  
% 6.89/1.50  cnf(c_6,plain,
% 6.89/1.50      ( ~ v1_relat_1(X0)
% 6.89/1.50      | k1_setfam_1(k2_enumset1(X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),X1))) = k8_relat_1(X1,X0) ),
% 6.89/1.50      inference(cnf_transformation,[],[f54]) ).
% 6.89/1.50  
% 6.89/1.50  cnf(c_378,plain,
% 6.89/1.50      ( k1_setfam_1(k2_enumset1(X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),X1))) = k8_relat_1(X1,X0)
% 6.89/1.50      | v1_relat_1(X0) != iProver_top ),
% 6.89/1.50      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 6.89/1.50  
% 6.89/1.50  cnf(c_1,plain,
% 6.89/1.50      ( k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
% 6.89/1.50      inference(cnf_transformation,[],[f51]) ).
% 6.89/1.50  
% 6.89/1.50  cnf(c_816,plain,
% 6.89/1.50      ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
% 6.89/1.50      inference(superposition,[status(thm)],[c_1,c_792]) ).
% 6.89/1.50  
% 6.89/1.50  cnf(c_1493,plain,
% 6.89/1.50      ( k1_relat_1(k7_relat_1(k6_relat_1(k2_zfmisc_1(k1_relat_1(X0),X1)),X0)) = k8_relat_1(X1,X0)
% 6.89/1.50      | v1_relat_1(X0) != iProver_top ),
% 6.89/1.50      inference(demodulation,[status(thm)],[c_378,c_816]) ).
% 6.89/1.50  
% 6.89/1.50  cnf(c_1499,plain,
% 6.89/1.50      ( k1_relat_1(k7_relat_1(k6_relat_1(k2_zfmisc_1(k1_relat_1(k6_relat_1(X0)),X1)),k6_relat_1(X0))) = k8_relat_1(X1,k6_relat_1(X0)) ),
% 6.89/1.50      inference(superposition,[status(thm)],[c_382,c_1493]) ).
% 6.89/1.50  
% 6.89/1.50  cnf(c_1511,plain,
% 6.89/1.50      ( k1_relat_1(k7_relat_1(k6_relat_1(k2_zfmisc_1(X0,X1)),k6_relat_1(X0))) = k8_relat_1(X1,k6_relat_1(X0)) ),
% 6.89/1.50      inference(light_normalisation,[status(thm)],[c_1499,c_8]) ).
% 6.89/1.50  
% 6.89/1.50  cnf(c_5,plain,
% 6.89/1.50      ( ~ v1_relat_1(X0) | k5_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X1,X0) ),
% 6.89/1.50      inference(cnf_transformation,[],[f39]) ).
% 6.89/1.50  
% 6.89/1.50  cnf(c_379,plain,
% 6.89/1.50      ( k5_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X1,X0)
% 6.89/1.50      | v1_relat_1(X0) != iProver_top ),
% 6.89/1.50      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 6.89/1.50  
% 6.89/1.50  cnf(c_925,plain,
% 6.89/1.50      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k8_relat_1(X1,k6_relat_1(X0)) ),
% 6.89/1.50      inference(superposition,[status(thm)],[c_382,c_379]) ).
% 6.89/1.50  
% 6.89/1.50  cnf(c_11,plain,
% 6.89/1.50      ( ~ v1_relat_1(X0) | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
% 6.89/1.50      inference(cnf_transformation,[],[f45]) ).
% 6.89/1.50  
% 6.89/1.50  cnf(c_375,plain,
% 6.89/1.50      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
% 6.89/1.50      | v1_relat_1(X1) != iProver_top ),
% 6.89/1.50      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 6.89/1.50  
% 6.89/1.50  cnf(c_735,plain,
% 6.89/1.50      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
% 6.89/1.50      inference(superposition,[status(thm)],[c_382,c_375]) ).
% 6.89/1.50  
% 6.89/1.50  cnf(c_1132,plain,
% 6.89/1.50      ( k8_relat_1(X0,k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X0),X1) ),
% 6.89/1.50      inference(light_normalisation,[status(thm)],[c_925,c_735]) ).
% 6.89/1.50  
% 6.89/1.50  cnf(c_1512,plain,
% 6.89/1.50      ( k1_relat_1(k7_relat_1(k6_relat_1(k2_zfmisc_1(X0,X1)),k6_relat_1(X0))) = k7_relat_1(k6_relat_1(X1),X0) ),
% 6.89/1.50      inference(demodulation,[status(thm)],[c_1511,c_1132]) ).
% 6.89/1.50  
% 6.89/1.50  cnf(c_3,plain,
% 6.89/1.50      ( ~ v1_relat_1(X0) | v1_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) ),
% 6.89/1.50      inference(cnf_transformation,[],[f52]) ).
% 6.89/1.50  
% 6.89/1.50  cnf(c_381,plain,
% 6.89/1.50      ( v1_relat_1(X0) != iProver_top
% 6.89/1.50      | v1_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) = iProver_top ),
% 6.89/1.50      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 6.89/1.50  
% 6.89/1.50  cnf(c_1170,plain,
% 6.89/1.50      ( v1_relat_1(X0) != iProver_top
% 6.89/1.50      | v1_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X1),X0))) = iProver_top ),
% 6.89/1.50      inference(light_normalisation,[status(thm)],[c_381,c_816]) ).
% 6.89/1.50  
% 6.89/1.50  cnf(c_1691,plain,
% 6.89/1.50      ( v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = iProver_top
% 6.89/1.50      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 6.89/1.50      inference(superposition,[status(thm)],[c_1512,c_1170]) ).
% 6.89/1.50  
% 6.89/1.50  cnf(c_2113,plain,
% 6.89/1.50      ( v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = iProver_top ),
% 6.89/1.50      inference(forward_subsumption_resolution,[status(thm)],[c_1691,c_382]) ).
% 6.89/1.50  
% 6.89/1.50  cnf(c_15383,plain,
% 6.89/1.50      ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0) = k7_relat_1(k6_relat_1(X0),X1) ),
% 6.89/1.50      inference(global_propositional_subsumption,[status(thm)],[c_1462,c_2113]) ).
% 6.89/1.50  
% 6.89/1.50  cnf(c_585,plain,
% 6.89/1.50      ( r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X1) = iProver_top ),
% 6.89/1.50      inference(superposition,[status(thm)],[c_1,c_383]) ).
% 6.89/1.50  
% 6.89/1.50  cnf(c_795,plain,
% 6.89/1.50      ( r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X1) = iProver_top ),
% 6.89/1.50      inference(demodulation,[status(thm)],[c_792,c_585]) ).
% 6.89/1.50  
% 6.89/1.50  cnf(c_7,plain,
% 6.89/1.50      ( k2_relat_1(k6_relat_1(X0)) = X0 ),
% 6.89/1.50      inference(cnf_transformation,[],[f42]) ).
% 6.89/1.50  
% 6.89/1.50  cnf(c_9,plain,
% 6.89/1.50      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 6.89/1.50      | ~ v1_relat_1(X0)
% 6.89/1.50      | k5_relat_1(X0,k6_relat_1(X1)) = X0 ),
% 6.89/1.50      inference(cnf_transformation,[],[f43]) ).
% 6.89/1.50  
% 6.89/1.50  cnf(c_377,plain,
% 6.89/1.50      ( k5_relat_1(X0,k6_relat_1(X1)) = X0
% 6.89/1.50      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 6.89/1.50      | v1_relat_1(X0) != iProver_top ),
% 6.89/1.50      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 6.89/1.50  
% 6.89/1.50  cnf(c_1424,plain,
% 6.89/1.50      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k6_relat_1(X0)
% 6.89/1.50      | r1_tarski(X0,X1) != iProver_top
% 6.89/1.50      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 6.89/1.50      inference(superposition,[status(thm)],[c_7,c_377]) ).
% 6.89/1.50  
% 6.89/1.50  cnf(c_1425,plain,
% 6.89/1.50      ( k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X1)
% 6.89/1.50      | r1_tarski(X1,X0) != iProver_top
% 6.89/1.50      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 6.89/1.50      inference(demodulation,[status(thm)],[c_1424,c_735]) ).
% 6.89/1.50  
% 6.89/1.50  cnf(c_10141,plain,
% 6.89/1.50      ( k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X1)
% 6.89/1.50      | r1_tarski(X1,X0) != iProver_top ),
% 6.89/1.50      inference(forward_subsumption_resolution,[status(thm)],[c_1425,c_382]) ).
% 6.89/1.50  
% 6.89/1.50  cnf(c_10143,plain,
% 6.89/1.50      ( k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(k6_relat_1(X1),X0))) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X1),X0))) ),
% 6.89/1.50      inference(superposition,[status(thm)],[c_795,c_10141]) ).
% 6.89/1.50  
% 6.89/1.50  cnf(c_876,plain,
% 6.89/1.50      ( k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
% 6.89/1.50      inference(superposition,[status(thm)],[c_816,c_792]) ).
% 6.89/1.50  
% 6.89/1.50  cnf(c_4,plain,
% 6.89/1.50      ( ~ v1_relat_1(X0)
% 6.89/1.50      | k7_relat_1(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) = k7_relat_1(k7_relat_1(X0,X1),X2) ),
% 6.89/1.50      inference(cnf_transformation,[],[f53]) ).
% 6.89/1.50  
% 6.89/1.50  cnf(c_380,plain,
% 6.89/1.50      ( k7_relat_1(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) = k7_relat_1(k7_relat_1(X0,X1),X2)
% 6.89/1.50      | v1_relat_1(X0) != iProver_top ),
% 6.89/1.50      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 6.89/1.50  
% 6.89/1.50  cnf(c_1611,plain,
% 6.89/1.50      ( k7_relat_1(X0,k1_relat_1(k7_relat_1(k6_relat_1(X1),X2))) = k7_relat_1(k7_relat_1(X0,X2),X1)
% 6.89/1.50      | v1_relat_1(X0) != iProver_top ),
% 6.89/1.50      inference(demodulation,[status(thm)],[c_380,c_816]) ).
% 6.89/1.50  
% 6.89/1.50  cnf(c_1617,plain,
% 6.89/1.50      ( k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(k6_relat_1(X1),X2))) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X2),X1) ),
% 6.89/1.50      inference(superposition,[status(thm)],[c_382,c_1611]) ).
% 6.89/1.50  
% 6.89/1.50  cnf(c_2838,plain,
% 6.89/1.50      ( k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(k6_relat_1(X1),X2))) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) ),
% 6.89/1.50      inference(superposition,[status(thm)],[c_876,c_1617]) ).
% 6.89/1.50  
% 6.89/1.50  cnf(c_12068,plain,
% 6.89/1.50      ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X1),X0))) ),
% 6.89/1.50      inference(superposition,[status(thm)],[c_10143,c_2838]) ).
% 6.89/1.50  
% 6.89/1.50  cnf(c_15386,plain,
% 6.89/1.50      ( k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k7_relat_1(k6_relat_1(X1),X0) ),
% 6.89/1.50      inference(demodulation,[status(thm)],[c_15383,c_12068]) ).
% 6.89/1.50  
% 6.89/1.50  cnf(c_13,negated_conjecture,
% 6.89/1.50      ( k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) != k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) ),
% 6.89/1.50      inference(cnf_transformation,[],[f56]) ).
% 6.89/1.50  
% 6.89/1.50  cnf(c_798,plain,
% 6.89/1.50      ( k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(sK0),sK1))) != k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) ),
% 6.89/1.50      inference(demodulation,[status(thm)],[c_792,c_13]) ).
% 6.89/1.50  
% 6.89/1.50  cnf(c_1064,plain,
% 6.89/1.50      ( k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(sK0),sK1))) != k7_relat_1(k6_relat_1(sK0),sK1) ),
% 6.89/1.50      inference(demodulation,[status(thm)],[c_735,c_798]) ).
% 6.89/1.50  
% 6.89/1.50  cnf(c_17168,plain,
% 6.89/1.50      ( k7_relat_1(k6_relat_1(sK1),sK0) != k7_relat_1(k6_relat_1(sK0),sK1) ),
% 6.89/1.50      inference(demodulation,[status(thm)],[c_15386,c_1064]) ).
% 6.89/1.50  
% 6.89/1.50  cnf(c_1463,plain,
% 6.89/1.50      ( k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X0)
% 6.89/1.50      | r1_tarski(X0,X1) != iProver_top
% 6.89/1.50      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 6.89/1.50      inference(superposition,[status(thm)],[c_8,c_374]) ).
% 6.89/1.50  
% 6.89/1.50  cnf(c_40,plain,
% 6.89/1.50      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 6.89/1.50      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 6.89/1.50  
% 6.89/1.50  cnf(c_1636,plain,
% 6.89/1.50      ( r1_tarski(X0,X1) != iProver_top
% 6.89/1.50      | k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X0) ),
% 6.89/1.50      inference(global_propositional_subsumption,[status(thm)],[c_1463,c_40]) ).
% 6.89/1.50  
% 6.89/1.50  cnf(c_1637,plain,
% 6.89/1.50      ( k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X0)
% 6.89/1.50      | r1_tarski(X0,X1) != iProver_top ),
% 6.89/1.50      inference(renaming,[status(thm)],[c_1636]) ).
% 6.89/1.50  
% 6.89/1.50  cnf(c_1644,plain,
% 6.89/1.50      ( k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X1) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
% 6.89/1.50      inference(superposition,[status(thm)],[c_795,c_1637]) ).
% 6.89/1.50  
% 6.89/1.50  cnf(c_3359,plain,
% 6.89/1.50      ( k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X0) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X1),X0))) ),
% 6.89/1.50      inference(superposition,[status(thm)],[c_876,c_1644]) ).
% 6.89/1.50  
% 6.89/1.50  cnf(c_17178,plain,
% 6.89/1.50      ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X1) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
% 6.89/1.50      inference(demodulation,[status(thm)],[c_15386,c_3359]) ).
% 6.89/1.50  
% 6.89/1.50  cnf(c_1461,plain,
% 6.89/1.50      ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X1) = k7_relat_1(k6_relat_1(X0),X1)
% 6.89/1.50      | v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) != iProver_top ),
% 6.89/1.50      inference(superposition,[status(thm)],[c_795,c_374]) ).
% 6.89/1.50  
% 6.89/1.50  cnf(c_12303,plain,
% 6.89/1.50      ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X1) = k7_relat_1(k6_relat_1(X0),X1) ),
% 6.89/1.50      inference(global_propositional_subsumption,[status(thm)],[c_1461,c_2113]) ).
% 6.89/1.50  
% 6.89/1.50  cnf(c_17202,plain,
% 6.89/1.50      ( k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X1),X0) ),
% 6.89/1.50      inference(light_normalisation,[status(thm)],[c_17178,c_12303,c_15386]) ).
% 6.89/1.50  
% 6.89/1.50  cnf(c_17216,plain,
% 6.89/1.50      ( $false ),
% 6.89/1.50      inference(forward_subsumption_resolution,[status(thm)],[c_17168,c_17202]) ).
% 6.89/1.50  
% 6.89/1.50  
% 6.89/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 6.89/1.50  
% 6.89/1.50  ------                               Statistics
% 6.89/1.50  
% 6.89/1.50  ------ General
% 6.89/1.50  
% 6.89/1.50  abstr_ref_over_cycles:                  0
% 6.89/1.50  abstr_ref_under_cycles:                 0
% 6.89/1.50  gc_basic_clause_elim:                   0
% 6.89/1.50  forced_gc_time:                         0
% 6.89/1.50  parsing_time:                           0.009
% 6.89/1.50  unif_index_cands_time:                  0.
% 6.89/1.50  unif_index_add_time:                    0.
% 6.89/1.50  orderings_time:                         0.
% 6.89/1.50  out_proof_time:                         0.011
% 6.89/1.50  total_time:                             0.648
% 6.89/1.50  num_of_symbols:                         44
% 6.89/1.50  num_of_terms:                           21148
% 6.89/1.50  
% 6.89/1.50  ------ Preprocessing
% 6.89/1.50  
% 6.89/1.50  num_of_splits:                          0
% 6.89/1.50  num_of_split_atoms:                     0
% 6.89/1.50  num_of_reused_defs:                     0
% 6.89/1.50  num_eq_ax_congr_red:                    8
% 6.89/1.50  num_of_sem_filtered_clauses:            1
% 6.89/1.50  num_of_subtypes:                        0
% 6.89/1.50  monotx_restored_types:                  0
% 6.89/1.50  sat_num_of_epr_types:                   0
% 6.89/1.50  sat_num_of_non_cyclic_types:            0
% 6.89/1.50  sat_guarded_non_collapsed_types:        0
% 6.89/1.50  num_pure_diseq_elim:                    0
% 6.89/1.50  simp_replaced_by:                       0
% 6.89/1.50  res_preprocessed:                       67
% 6.89/1.50  prep_upred:                             0
% 6.89/1.50  prep_unflattend:                        2
% 6.89/1.50  smt_new_axioms:                         0
% 6.89/1.50  pred_elim_cands:                        2
% 6.89/1.50  pred_elim:                              0
% 6.89/1.50  pred_elim_cl:                           0
% 6.89/1.50  pred_elim_cycles:                       1
% 6.89/1.50  merged_defs:                            0
% 6.89/1.50  merged_defs_ncl:                        0
% 6.89/1.50  bin_hyper_res:                          0
% 6.89/1.50  prep_cycles:                            3
% 6.89/1.50  pred_elim_time:                         0.
% 6.89/1.50  splitting_time:                         0.
% 6.89/1.50  sem_filter_time:                        0.
% 6.89/1.50  monotx_time:                            0.
% 6.89/1.50  subtype_inf_time:                       0.
% 6.89/1.50  
% 6.89/1.50  ------ Problem properties
% 6.89/1.50  
% 6.89/1.50  clauses:                                14
% 6.89/1.50  conjectures:                            1
% 6.89/1.50  epr:                                    0
% 6.89/1.50  horn:                                   14
% 6.89/1.50  ground:                                 1
% 6.89/1.50  unary:                                  6
% 6.89/1.50  binary:                                 6
% 6.89/1.50  lits:                                   24
% 6.89/1.50  lits_eq:                                11
% 6.89/1.50  fd_pure:                                0
% 6.89/1.50  fd_pseudo:                              0
% 6.89/1.50  fd_cond:                                0
% 6.89/1.50  fd_pseudo_cond:                         0
% 6.89/1.50  ac_symbols:                             0
% 6.89/1.50  
% 6.89/1.50  ------ Propositional Solver
% 6.89/1.50  
% 6.89/1.50  prop_solver_calls:                      25
% 6.89/1.50  prop_fast_solver_calls:                 446
% 6.89/1.50  smt_solver_calls:                       0
% 6.89/1.50  smt_fast_solver_calls:                  0
% 6.89/1.50  prop_num_of_clauses:                    5784
% 6.89/1.50  prop_preprocess_simplified:             8423
% 6.89/1.50  prop_fo_subsumed:                       3
% 6.89/1.50  prop_solver_time:                       0.
% 6.89/1.50  smt_solver_time:                        0.
% 6.89/1.50  smt_fast_solver_time:                   0.
% 6.89/1.50  prop_fast_solver_time:                  0.
% 6.89/1.50  prop_unsat_core_time:                   0.
% 6.89/1.50  
% 6.89/1.50  ------ QBF
% 6.89/1.50  
% 6.89/1.50  qbf_q_res:                              0
% 6.89/1.50  qbf_num_tautologies:                    0
% 6.89/1.50  qbf_prep_cycles:                        0
% 6.89/1.50  
% 6.89/1.50  ------ BMC1
% 6.89/1.50  
% 6.89/1.50  bmc1_current_bound:                     -1
% 6.89/1.50  bmc1_last_solved_bound:                 -1
% 6.89/1.50  bmc1_unsat_core_size:                   -1
% 6.89/1.50  bmc1_unsat_core_parents_size:           -1
% 6.89/1.50  bmc1_merge_next_fun:                    0
% 6.89/1.50  bmc1_unsat_core_clauses_time:           0.
% 6.89/1.50  
% 6.89/1.50  ------ Instantiation
% 6.89/1.50  
% 6.89/1.50  inst_num_of_clauses:                    1617
% 6.89/1.50  inst_num_in_passive:                    285
% 6.89/1.50  inst_num_in_active:                     640
% 6.89/1.50  inst_num_in_unprocessed:                692
% 6.89/1.50  inst_num_of_loops:                      650
% 6.89/1.50  inst_num_of_learning_restarts:          0
% 6.89/1.50  inst_num_moves_active_passive:          7
% 6.89/1.50  inst_lit_activity:                      0
% 6.89/1.50  inst_lit_activity_moves:                0
% 6.89/1.50  inst_num_tautologies:                   0
% 6.89/1.50  inst_num_prop_implied:                  0
% 6.89/1.50  inst_num_existing_simplified:           0
% 6.89/1.50  inst_num_eq_res_simplified:             0
% 6.89/1.50  inst_num_child_elim:                    0
% 6.89/1.50  inst_num_of_dismatching_blockings:      982
% 6.89/1.50  inst_num_of_non_proper_insts:           1480
% 6.89/1.50  inst_num_of_duplicates:                 0
% 6.89/1.50  inst_inst_num_from_inst_to_res:         0
% 6.89/1.50  inst_dismatching_checking_time:         0.
% 6.89/1.50  
% 6.89/1.50  ------ Resolution
% 6.89/1.50  
% 6.89/1.50  res_num_of_clauses:                     0
% 6.89/1.50  res_num_in_passive:                     0
% 6.89/1.50  res_num_in_active:                      0
% 6.89/1.50  res_num_of_loops:                       70
% 6.89/1.50  res_forward_subset_subsumed:            235
% 6.89/1.50  res_backward_subset_subsumed:           4
% 6.89/1.50  res_forward_subsumed:                   0
% 6.89/1.50  res_backward_subsumed:                  0
% 6.89/1.50  res_forward_subsumption_resolution:     0
% 6.89/1.50  res_backward_subsumption_resolution:    0
% 6.89/1.50  res_clause_to_clause_subsumption:       3599
% 6.89/1.50  res_orphan_elimination:                 0
% 6.89/1.50  res_tautology_del:                      257
% 6.89/1.50  res_num_eq_res_simplified:              0
% 6.89/1.50  res_num_sel_changes:                    0
% 6.89/1.50  res_moves_from_active_to_pass:          0
% 6.89/1.50  
% 6.89/1.50  ------ Superposition
% 6.89/1.50  
% 6.89/1.50  sup_time_total:                         0.
% 6.89/1.50  sup_time_generating:                    0.
% 6.89/1.50  sup_time_sim_full:                      0.
% 6.89/1.50  sup_time_sim_immed:                     0.
% 6.89/1.50  
% 6.89/1.50  sup_num_of_clauses:                     943
% 6.89/1.50  sup_num_in_active:                      98
% 6.89/1.50  sup_num_in_passive:                     845
% 6.89/1.50  sup_num_of_loops:                       129
% 6.89/1.50  sup_fw_superposition:                   1510
% 6.89/1.50  sup_bw_superposition:                   1842
% 6.89/1.50  sup_immediate_simplified:               1296
% 6.89/1.50  sup_given_eliminated:                   0
% 6.89/1.50  comparisons_done:                       0
% 6.89/1.50  comparisons_avoided:                    0
% 6.89/1.50  
% 6.89/1.50  ------ Simplifications
% 6.89/1.50  
% 6.89/1.50  
% 6.89/1.50  sim_fw_subset_subsumed:                 6
% 6.89/1.50  sim_bw_subset_subsumed:                 2
% 6.89/1.50  sim_fw_subsumed:                        208
% 6.89/1.50  sim_bw_subsumed:                        0
% 6.89/1.50  sim_fw_subsumption_res:                 3
% 6.89/1.50  sim_bw_subsumption_res:                 0
% 6.89/1.50  sim_tautology_del:                      19
% 6.89/1.50  sim_eq_tautology_del:                   121
% 6.89/1.50  sim_eq_res_simp:                        0
% 6.89/1.50  sim_fw_demodulated:                     701
% 6.89/1.50  sim_bw_demodulated:                     45
% 6.89/1.50  sim_light_normalised:                   629
% 6.89/1.50  sim_joinable_taut:                      0
% 6.89/1.50  sim_joinable_simp:                      0
% 6.89/1.50  sim_ac_normalised:                      0
% 6.89/1.50  sim_smt_subsumption:                    0
% 6.89/1.50  
%------------------------------------------------------------------------------
