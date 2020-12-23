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
% DateTime   : Thu Dec  3 11:50:03 EST 2020

% Result     : Theorem 3.96s
% Output     : CNFRefutation 3.96s
% Verified   : 
% Statistics : Number of formulae       :  144 (33052 expanded)
%              Number of clauses        :   92 (13334 expanded)
%              Number of leaves         :   16 (6787 expanded)
%              Depth                    :   33
%              Number of atoms          :  232 (49446 expanded)
%              Number of equality atoms :  167 (28612 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    3 (   2 average)
%              Maximal term depth       :    8 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(pure_predicate_removal,[],[f19])).

fof(f64,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k3_xboole_0(k2_relat_1(X1),X0) = k2_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k2_relat_1(X1),X0) = k2_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k2_relat_1(X1),X0) = k2_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f66,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f46,f47])).

fof(f67,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f48,f66])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_enumset1(k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),X0)) = k2_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f51,f67])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X0)) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f62,f67])).

fof(f12,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f56,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k5_relat_1(X1,k6_relat_1(X0)) = k8_relat_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = k8_relat_1(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = k8_relat_1(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f68,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f45,f67])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k5_relat_1(k6_relat_1(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f24,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f61,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k5_relat_1(k7_relat_1(X1,X0),X2) = k7_relat_1(k5_relat_1(X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k5_relat_1(k7_relat_1(X1,X0),X2) = k7_relat_1(k5_relat_1(X1,X2),X0)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k7_relat_1(X1,X0),X2) = k7_relat_1(k5_relat_1(X1,X2),X0)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f20,conjecture,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f20])).

fof(f37,plain,(
    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f21])).

fof(f40,plain,
    ( ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))
   => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f37,f40])).

fof(f65,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f41])).

fof(f71,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) ),
    inference(definition_unfolding,[],[f65,f67])).

cnf(c_19,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_623,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | k1_setfam_1(k2_enumset1(k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X0),X1)) = k2_relat_1(k8_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_634,plain,
    ( k1_setfam_1(k2_enumset1(k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X0),X1)) = k2_relat_1(k8_relat_1(X1,X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_17,plain,
    ( ~ v1_relat_1(X0)
    | k1_setfam_1(k2_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_625,plain,
    ( k1_setfam_1(k2_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1084,plain,
    ( k1_setfam_1(k2_enumset1(k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(superposition,[status(thm)],[c_623,c_625])).

cnf(c_11,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1085,plain,
    ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(light_normalisation,[status(thm)],[c_1084,c_11])).

cnf(c_1962,plain,
    ( k1_relat_1(k7_relat_1(k6_relat_1(k2_relat_1(X0)),X1)) = k2_relat_1(k8_relat_1(X1,X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_634,c_1085])).

cnf(c_1967,plain,
    ( k1_relat_1(k7_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(X0))),X1)) = k2_relat_1(k8_relat_1(X1,k6_relat_1(X0))) ),
    inference(superposition,[status(thm)],[c_623,c_1962])).

cnf(c_10,plain,
    ( k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1968,plain,
    ( k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k2_relat_1(k8_relat_1(X1,k6_relat_1(X0))) ),
    inference(light_normalisation,[status(thm)],[c_1967,c_10])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X1,X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_633,plain,
    ( k5_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X1,X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1540,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k8_relat_1(X1,k6_relat_1(X0)) ),
    inference(superposition,[status(thm)],[c_623,c_633])).

cnf(c_18,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_624,plain,
    ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1236,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(superposition,[status(thm)],[c_623,c_624])).

cnf(c_1541,plain,
    ( k8_relat_1(X0,k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(light_normalisation,[status(thm)],[c_1540,c_1236])).

cnf(c_1969,plain,
    ( k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k2_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
    inference(demodulation,[status(thm)],[c_1968,c_1541])).

cnf(c_3,plain,
    ( r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_637,plain,
    ( r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1087,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1085,c_637])).

cnf(c_2083,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1969,c_1087])).

cnf(c_14,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k6_relat_1(X1),X0) = X0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_628,plain,
    ( k5_relat_1(k6_relat_1(X0),X1) = X1
    | r1_tarski(k1_relat_1(X1),X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1955,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k6_relat_1(X1)
    | r1_tarski(X1,X0) != iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11,c_628])).

cnf(c_1956,plain,
    ( k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X0)
    | r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1955,c_1236])).

cnf(c_21,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3228,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1956,c_21])).

cnf(c_3229,plain,
    ( k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X0)
    | r1_tarski(X0,X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_3228])).

cnf(c_3240,plain,
    ( k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X1) = k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
    inference(superposition,[status(thm)],[c_2083,c_3229])).

cnf(c_3531,plain,
    ( k2_relat_1(k7_relat_1(k6_relat_1(X0),k2_relat_1(k7_relat_1(k6_relat_1(X1),X0)))) = k1_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X1),X0)))) ),
    inference(superposition,[status(thm)],[c_3240,c_1969])).

cnf(c_3534,plain,
    ( k2_relat_1(k7_relat_1(k6_relat_1(X0),k2_relat_1(k7_relat_1(k6_relat_1(X1),X0)))) = k2_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
    inference(demodulation,[status(thm)],[c_3531,c_11])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | v1_relat_1(k5_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_636,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k5_relat_1(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_16,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_626,plain,
    ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1832,plain,
    ( k5_relat_1(k5_relat_1(X0,X1),k6_relat_1(k2_relat_1(k5_relat_1(X0,X1)))) = k5_relat_1(X0,X1)
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_636,c_626])).

cnf(c_7336,plain,
    ( k5_relat_1(k5_relat_1(k6_relat_1(X0),X1),k6_relat_1(k2_relat_1(k5_relat_1(k6_relat_1(X0),X1)))) = k5_relat_1(k6_relat_1(X0),X1)
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_623,c_1832])).

cnf(c_8328,plain,
    ( k5_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),k6_relat_1(k2_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))))) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) ),
    inference(superposition,[status(thm)],[c_623,c_7336])).

cnf(c_8331,plain,
    ( k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)))) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(light_normalisation,[status(thm)],[c_8328,c_1236])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k7_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(k7_relat_1(X0,X2),X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_635,plain,
    ( k7_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(k7_relat_1(X0,X2),X1)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2379,plain,
    ( k7_relat_1(k5_relat_1(k6_relat_1(X0),X1),X2) = k5_relat_1(k7_relat_1(k6_relat_1(X0),X2),X1)
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_623,c_635])).

cnf(c_2670,plain,
    ( k7_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),X2) = k5_relat_1(k7_relat_1(k6_relat_1(X0),X2),k6_relat_1(X1)) ),
    inference(superposition,[status(thm)],[c_623,c_2379])).

cnf(c_2671,plain,
    ( k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X0),X1) ),
    inference(light_normalisation,[status(thm)],[c_2670,c_1236])).

cnf(c_8764,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X0),X1) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(superposition,[status(thm)],[c_8331,c_2671])).

cnf(c_8796,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X1),k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k7_relat_1(k6_relat_1(X1),k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
    inference(superposition,[status(thm)],[c_3534,c_8764])).

cnf(c_8850,plain,
    ( k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))),k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k7_relat_1(k6_relat_1(X1),k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
    inference(light_normalisation,[status(thm)],[c_8796,c_3240])).

cnf(c_1010,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(k2_relat_1(k6_relat_1(X0)))) = k6_relat_1(X0) ),
    inference(superposition,[status(thm)],[c_623,c_626])).

cnf(c_1011,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X0)) = k6_relat_1(X0) ),
    inference(light_normalisation,[status(thm)],[c_1010,c_10])).

cnf(c_1396,plain,
    ( k7_relat_1(k6_relat_1(X0),X0) = k6_relat_1(X0) ),
    inference(superposition,[status(thm)],[c_1011,c_1236])).

cnf(c_8851,plain,
    ( k7_relat_1(k6_relat_1(X0),k2_relat_1(k7_relat_1(k6_relat_1(X1),X0))) = k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X1),X0))) ),
    inference(demodulation,[status(thm)],[c_8850,c_1396])).

cnf(c_1828,plain,
    ( v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1236,c_636])).

cnf(c_2794,plain,
    ( v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1828,c_21])).

cnf(c_1954,plain,
    ( k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X0),X1)) = k7_relat_1(k6_relat_1(X0),X1)
    | v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1087,c_628])).

cnf(c_3221,plain,
    ( k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X0),X1)) = k7_relat_1(k6_relat_1(X0),X1)
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2794,c_1954])).

cnf(c_3859,plain,
    ( k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X0),X1)) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(superposition,[status(thm)],[c_623,c_3221])).

cnf(c_9522,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X1),X0)))) = k7_relat_1(k6_relat_1(X0),k2_relat_1(k7_relat_1(k6_relat_1(X1),X0))) ),
    inference(superposition,[status(thm)],[c_8851,c_3859])).

cnf(c_9580,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X1),X0)))) = k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X1),X0))) ),
    inference(demodulation,[status(thm)],[c_9522,c_8851])).

cnf(c_9896,plain,
    ( k5_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))),k6_relat_1(k2_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)))))) = k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X1),k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))))) ),
    inference(superposition,[status(thm)],[c_8851,c_9580])).

cnf(c_1966,plain,
    ( k1_relat_1(k7_relat_1(k6_relat_1(k2_relat_1(k5_relat_1(X0,X1))),X2)) = k2_relat_1(k8_relat_1(X2,k5_relat_1(X0,X1)))
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_636,c_1962])).

cnf(c_2087,plain,
    ( k2_relat_1(k7_relat_1(k6_relat_1(X0),k2_relat_1(k5_relat_1(X1,X2)))) = k2_relat_1(k8_relat_1(X0,k5_relat_1(X1,X2)))
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1966,c_1969])).

cnf(c_8315,plain,
    ( k2_relat_1(k7_relat_1(k6_relat_1(X0),k2_relat_1(k5_relat_1(k6_relat_1(X1),X2)))) = k2_relat_1(k8_relat_1(X0,k5_relat_1(k6_relat_1(X1),X2)))
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_623,c_2087])).

cnf(c_8521,plain,
    ( k2_relat_1(k7_relat_1(k6_relat_1(X0),k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))))) = k2_relat_1(k8_relat_1(X0,k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))) ),
    inference(superposition,[status(thm)],[c_623,c_8315])).

cnf(c_2805,plain,
    ( k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X2)) = k8_relat_1(X2,k7_relat_1(k6_relat_1(X0),X1))
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2794,c_633])).

cnf(c_2810,plain,
    ( k8_relat_1(X0,k7_relat_1(k6_relat_1(X1),X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)
    | v1_relat_1(k6_relat_1(X2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2805,c_2671])).

cnf(c_2948,plain,
    ( k8_relat_1(X0,k7_relat_1(k6_relat_1(X1),X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) ),
    inference(superposition,[status(thm)],[c_623,c_2810])).

cnf(c_8524,plain,
    ( k2_relat_1(k7_relat_1(k6_relat_1(X0),k2_relat_1(k7_relat_1(k6_relat_1(X1),X2)))) = k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)) ),
    inference(demodulation,[status(thm)],[c_8521,c_1236,c_2948])).

cnf(c_9924,plain,
    ( k6_relat_1(k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0))) = k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X1),X0))) ),
    inference(demodulation,[status(thm)],[c_9896,c_10,c_1011,c_1236,c_8524])).

cnf(c_2802,plain,
    ( k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X1),X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X0)
    | v1_relat_1(k6_relat_1(X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2794,c_624])).

cnf(c_4187,plain,
    ( k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X1),X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X0) ),
    inference(superposition,[status(thm)],[c_623,c_2802])).

cnf(c_4393,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(superposition,[status(thm)],[c_4187,c_3859])).

cnf(c_9925,plain,
    ( k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X1),X0))) ),
    inference(light_normalisation,[status(thm)],[c_9924,c_4393])).

cnf(c_10403,plain,
    ( k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X0) = k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X1),X0))) ),
    inference(superposition,[status(thm)],[c_9925,c_3240])).

cnf(c_10394,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X1),X0) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(superposition,[status(thm)],[c_9925,c_8764])).

cnf(c_10404,plain,
    ( k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X0) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(light_normalisation,[status(thm)],[c_10394,c_3240])).

cnf(c_10405,plain,
    ( k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(demodulation,[status(thm)],[c_10404,c_10403])).

cnf(c_10409,plain,
    ( k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(demodulation,[status(thm)],[c_10405,c_9925])).

cnf(c_10512,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X1) = k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
    inference(light_normalisation,[status(thm)],[c_10403,c_10409])).

cnf(c_2676,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X1) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
    inference(superposition,[status(thm)],[c_1396,c_2671])).

cnf(c_2682,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X1) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(demodulation,[status(thm)],[c_2676,c_1236])).

cnf(c_10513,plain,
    ( k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(demodulation,[status(thm)],[c_10512,c_2682,c_10409])).

cnf(c_20,negated_conjecture,
    ( k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1089,plain,
    ( k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(sK0),sK1))) != k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) ),
    inference(demodulation,[status(thm)],[c_1085,c_20])).

cnf(c_1395,plain,
    ( k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(sK0),sK1))) != k7_relat_1(k6_relat_1(sK0),sK1) ),
    inference(demodulation,[status(thm)],[c_1236,c_1089])).

cnf(c_2082,plain,
    ( k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(sK1),sK0))) != k7_relat_1(k6_relat_1(sK0),sK1) ),
    inference(demodulation,[status(thm)],[c_1969,c_1395])).

cnf(c_11192,plain,
    ( k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(sK1),sK0))) != k7_relat_1(k6_relat_1(sK1),sK0) ),
    inference(demodulation,[status(thm)],[c_10513,c_2082])).

cnf(c_11198,plain,
    ( k7_relat_1(k6_relat_1(sK1),sK0) != k7_relat_1(k6_relat_1(sK0),sK1) ),
    inference(demodulation,[status(thm)],[c_11192,c_10409])).

cnf(c_11390,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_10513,c_11198])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 19:17:15 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.96/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.96/0.99  
% 3.96/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.96/0.99  
% 3.96/0.99  ------  iProver source info
% 3.96/0.99  
% 3.96/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.96/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.96/0.99  git: non_committed_changes: false
% 3.96/0.99  git: last_make_outside_of_git: false
% 3.96/0.99  
% 3.96/0.99  ------ 
% 3.96/0.99  
% 3.96/0.99  ------ Input Options
% 3.96/0.99  
% 3.96/0.99  --out_options                           all
% 3.96/0.99  --tptp_safe_out                         true
% 3.96/0.99  --problem_path                          ""
% 3.96/0.99  --include_path                          ""
% 3.96/0.99  --clausifier                            res/vclausify_rel
% 3.96/0.99  --clausifier_options                    ""
% 3.96/0.99  --stdin                                 false
% 3.96/0.99  --stats_out                             all
% 3.96/0.99  
% 3.96/0.99  ------ General Options
% 3.96/0.99  
% 3.96/0.99  --fof                                   false
% 3.96/0.99  --time_out_real                         305.
% 3.96/0.99  --time_out_virtual                      -1.
% 3.96/0.99  --symbol_type_check                     false
% 3.96/0.99  --clausify_out                          false
% 3.96/0.99  --sig_cnt_out                           false
% 3.96/0.99  --trig_cnt_out                          false
% 3.96/0.99  --trig_cnt_out_tolerance                1.
% 3.96/0.99  --trig_cnt_out_sk_spl                   false
% 3.96/0.99  --abstr_cl_out                          false
% 3.96/0.99  
% 3.96/0.99  ------ Global Options
% 3.96/0.99  
% 3.96/0.99  --schedule                              default
% 3.96/0.99  --add_important_lit                     false
% 3.96/0.99  --prop_solver_per_cl                    1000
% 3.96/0.99  --min_unsat_core                        false
% 3.96/0.99  --soft_assumptions                      false
% 3.96/0.99  --soft_lemma_size                       3
% 3.96/0.99  --prop_impl_unit_size                   0
% 3.96/0.99  --prop_impl_unit                        []
% 3.96/0.99  --share_sel_clauses                     true
% 3.96/0.99  --reset_solvers                         false
% 3.96/0.99  --bc_imp_inh                            [conj_cone]
% 3.96/0.99  --conj_cone_tolerance                   3.
% 3.96/0.99  --extra_neg_conj                        none
% 3.96/0.99  --large_theory_mode                     true
% 3.96/0.99  --prolific_symb_bound                   200
% 3.96/0.99  --lt_threshold                          2000
% 3.96/0.99  --clause_weak_htbl                      true
% 3.96/0.99  --gc_record_bc_elim                     false
% 3.96/0.99  
% 3.96/0.99  ------ Preprocessing Options
% 3.96/0.99  
% 3.96/0.99  --preprocessing_flag                    true
% 3.96/0.99  --time_out_prep_mult                    0.1
% 3.96/0.99  --splitting_mode                        input
% 3.96/0.99  --splitting_grd                         true
% 3.96/0.99  --splitting_cvd                         false
% 3.96/0.99  --splitting_cvd_svl                     false
% 3.96/0.99  --splitting_nvd                         32
% 3.96/0.99  --sub_typing                            true
% 3.96/0.99  --prep_gs_sim                           true
% 3.96/0.99  --prep_unflatten                        true
% 3.96/0.99  --prep_res_sim                          true
% 3.96/0.99  --prep_upred                            true
% 3.96/0.99  --prep_sem_filter                       exhaustive
% 3.96/0.99  --prep_sem_filter_out                   false
% 3.96/0.99  --pred_elim                             true
% 3.96/0.99  --res_sim_input                         true
% 3.96/0.99  --eq_ax_congr_red                       true
% 3.96/0.99  --pure_diseq_elim                       true
% 3.96/0.99  --brand_transform                       false
% 3.96/0.99  --non_eq_to_eq                          false
% 3.96/0.99  --prep_def_merge                        true
% 3.96/0.99  --prep_def_merge_prop_impl              false
% 3.96/0.99  --prep_def_merge_mbd                    true
% 3.96/0.99  --prep_def_merge_tr_red                 false
% 3.96/0.99  --prep_def_merge_tr_cl                  false
% 3.96/0.99  --smt_preprocessing                     true
% 3.96/0.99  --smt_ac_axioms                         fast
% 3.96/0.99  --preprocessed_out                      false
% 3.96/0.99  --preprocessed_stats                    false
% 3.96/0.99  
% 3.96/0.99  ------ Abstraction refinement Options
% 3.96/0.99  
% 3.96/0.99  --abstr_ref                             []
% 3.96/0.99  --abstr_ref_prep                        false
% 3.96/0.99  --abstr_ref_until_sat                   false
% 3.96/0.99  --abstr_ref_sig_restrict                funpre
% 3.96/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.96/0.99  --abstr_ref_under                       []
% 3.96/0.99  
% 3.96/0.99  ------ SAT Options
% 3.96/0.99  
% 3.96/0.99  --sat_mode                              false
% 3.96/0.99  --sat_fm_restart_options                ""
% 3.96/0.99  --sat_gr_def                            false
% 3.96/0.99  --sat_epr_types                         true
% 3.96/0.99  --sat_non_cyclic_types                  false
% 3.96/0.99  --sat_finite_models                     false
% 3.96/0.99  --sat_fm_lemmas                         false
% 3.96/0.99  --sat_fm_prep                           false
% 3.96/0.99  --sat_fm_uc_incr                        true
% 3.96/0.99  --sat_out_model                         small
% 3.96/0.99  --sat_out_clauses                       false
% 3.96/0.99  
% 3.96/0.99  ------ QBF Options
% 3.96/0.99  
% 3.96/0.99  --qbf_mode                              false
% 3.96/0.99  --qbf_elim_univ                         false
% 3.96/0.99  --qbf_dom_inst                          none
% 3.96/0.99  --qbf_dom_pre_inst                      false
% 3.96/0.99  --qbf_sk_in                             false
% 3.96/0.99  --qbf_pred_elim                         true
% 3.96/0.99  --qbf_split                             512
% 3.96/0.99  
% 3.96/0.99  ------ BMC1 Options
% 3.96/0.99  
% 3.96/0.99  --bmc1_incremental                      false
% 3.96/0.99  --bmc1_axioms                           reachable_all
% 3.96/0.99  --bmc1_min_bound                        0
% 3.96/0.99  --bmc1_max_bound                        -1
% 3.96/0.99  --bmc1_max_bound_default                -1
% 3.96/0.99  --bmc1_symbol_reachability              true
% 3.96/0.99  --bmc1_property_lemmas                  false
% 3.96/0.99  --bmc1_k_induction                      false
% 3.96/0.99  --bmc1_non_equiv_states                 false
% 3.96/0.99  --bmc1_deadlock                         false
% 3.96/0.99  --bmc1_ucm                              false
% 3.96/0.99  --bmc1_add_unsat_core                   none
% 3.96/0.99  --bmc1_unsat_core_children              false
% 3.96/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.96/0.99  --bmc1_out_stat                         full
% 3.96/0.99  --bmc1_ground_init                      false
% 3.96/0.99  --bmc1_pre_inst_next_state              false
% 3.96/0.99  --bmc1_pre_inst_state                   false
% 3.96/0.99  --bmc1_pre_inst_reach_state             false
% 3.96/0.99  --bmc1_out_unsat_core                   false
% 3.96/0.99  --bmc1_aig_witness_out                  false
% 3.96/0.99  --bmc1_verbose                          false
% 3.96/0.99  --bmc1_dump_clauses_tptp                false
% 3.96/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.96/0.99  --bmc1_dump_file                        -
% 3.96/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.96/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.96/0.99  --bmc1_ucm_extend_mode                  1
% 3.96/0.99  --bmc1_ucm_init_mode                    2
% 3.96/0.99  --bmc1_ucm_cone_mode                    none
% 3.96/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.96/0.99  --bmc1_ucm_relax_model                  4
% 3.96/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.96/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.96/0.99  --bmc1_ucm_layered_model                none
% 3.96/0.99  --bmc1_ucm_max_lemma_size               10
% 3.96/0.99  
% 3.96/0.99  ------ AIG Options
% 3.96/0.99  
% 3.96/0.99  --aig_mode                              false
% 3.96/0.99  
% 3.96/0.99  ------ Instantiation Options
% 3.96/0.99  
% 3.96/0.99  --instantiation_flag                    true
% 3.96/0.99  --inst_sos_flag                         true
% 3.96/0.99  --inst_sos_phase                        true
% 3.96/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.96/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.96/0.99  --inst_lit_sel_side                     num_symb
% 3.96/0.99  --inst_solver_per_active                1400
% 3.96/0.99  --inst_solver_calls_frac                1.
% 3.96/0.99  --inst_passive_queue_type               priority_queues
% 3.96/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.96/0.99  --inst_passive_queues_freq              [25;2]
% 3.96/0.99  --inst_dismatching                      true
% 3.96/0.99  --inst_eager_unprocessed_to_passive     true
% 3.96/0.99  --inst_prop_sim_given                   true
% 3.96/0.99  --inst_prop_sim_new                     false
% 3.96/0.99  --inst_subs_new                         false
% 3.96/0.99  --inst_eq_res_simp                      false
% 3.96/0.99  --inst_subs_given                       false
% 3.96/0.99  --inst_orphan_elimination               true
% 3.96/0.99  --inst_learning_loop_flag               true
% 3.96/0.99  --inst_learning_start                   3000
% 3.96/0.99  --inst_learning_factor                  2
% 3.96/0.99  --inst_start_prop_sim_after_learn       3
% 3.96/0.99  --inst_sel_renew                        solver
% 3.96/0.99  --inst_lit_activity_flag                true
% 3.96/0.99  --inst_restr_to_given                   false
% 3.96/0.99  --inst_activity_threshold               500
% 3.96/0.99  --inst_out_proof                        true
% 3.96/0.99  
% 3.96/0.99  ------ Resolution Options
% 3.96/0.99  
% 3.96/0.99  --resolution_flag                       true
% 3.96/0.99  --res_lit_sel                           adaptive
% 3.96/0.99  --res_lit_sel_side                      none
% 3.96/0.99  --res_ordering                          kbo
% 3.96/0.99  --res_to_prop_solver                    active
% 3.96/0.99  --res_prop_simpl_new                    false
% 3.96/0.99  --res_prop_simpl_given                  true
% 3.96/0.99  --res_passive_queue_type                priority_queues
% 3.96/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.96/0.99  --res_passive_queues_freq               [15;5]
% 3.96/0.99  --res_forward_subs                      full
% 3.96/0.99  --res_backward_subs                     full
% 3.96/0.99  --res_forward_subs_resolution           true
% 3.96/0.99  --res_backward_subs_resolution          true
% 3.96/0.99  --res_orphan_elimination                true
% 3.96/0.99  --res_time_limit                        2.
% 3.96/0.99  --res_out_proof                         true
% 3.96/0.99  
% 3.96/0.99  ------ Superposition Options
% 3.96/0.99  
% 3.96/0.99  --superposition_flag                    true
% 3.96/0.99  --sup_passive_queue_type                priority_queues
% 3.96/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.96/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.96/0.99  --demod_completeness_check              fast
% 3.96/0.99  --demod_use_ground                      true
% 3.96/0.99  --sup_to_prop_solver                    passive
% 3.96/0.99  --sup_prop_simpl_new                    true
% 3.96/0.99  --sup_prop_simpl_given                  true
% 3.96/0.99  --sup_fun_splitting                     true
% 3.96/0.99  --sup_smt_interval                      50000
% 3.96/0.99  
% 3.96/0.99  ------ Superposition Simplification Setup
% 3.96/0.99  
% 3.96/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.96/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.96/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.96/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.96/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.96/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.96/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.96/0.99  --sup_immed_triv                        [TrivRules]
% 3.96/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.96/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.96/0.99  --sup_immed_bw_main                     []
% 3.96/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.96/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.96/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.96/0.99  --sup_input_bw                          []
% 3.96/0.99  
% 3.96/0.99  ------ Combination Options
% 3.96/0.99  
% 3.96/0.99  --comb_res_mult                         3
% 3.96/0.99  --comb_sup_mult                         2
% 3.96/0.99  --comb_inst_mult                        10
% 3.96/0.99  
% 3.96/0.99  ------ Debug Options
% 3.96/0.99  
% 3.96/0.99  --dbg_backtrace                         false
% 3.96/0.99  --dbg_dump_prop_clauses                 false
% 3.96/0.99  --dbg_dump_prop_clauses_file            -
% 3.96/0.99  --dbg_out_stat                          false
% 3.96/0.99  ------ Parsing...
% 3.96/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.96/0.99  
% 3.96/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.96/0.99  
% 3.96/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.96/0.99  
% 3.96/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.96/0.99  ------ Proving...
% 3.96/0.99  ------ Problem Properties 
% 3.96/0.99  
% 3.96/0.99  
% 3.96/0.99  clauses                                 20
% 3.96/0.99  conjectures                             1
% 3.96/0.99  EPR                                     2
% 3.96/0.99  Horn                                    20
% 3.96/0.99  unary                                   6
% 3.96/0.99  binary                                  8
% 3.96/0.99  lits                                    41
% 3.96/0.99  lits eq                                 13
% 3.96/0.99  fd_pure                                 0
% 3.96/0.99  fd_pseudo                               0
% 3.96/0.99  fd_cond                                 0
% 3.96/0.99  fd_pseudo_cond                          1
% 3.96/0.99  AC symbols                              0
% 3.96/0.99  
% 3.96/0.99  ------ Schedule dynamic 5 is on 
% 3.96/0.99  
% 3.96/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.96/0.99  
% 3.96/0.99  
% 3.96/0.99  ------ 
% 3.96/0.99  Current options:
% 3.96/0.99  ------ 
% 3.96/0.99  
% 3.96/0.99  ------ Input Options
% 3.96/0.99  
% 3.96/0.99  --out_options                           all
% 3.96/0.99  --tptp_safe_out                         true
% 3.96/0.99  --problem_path                          ""
% 3.96/0.99  --include_path                          ""
% 3.96/0.99  --clausifier                            res/vclausify_rel
% 3.96/0.99  --clausifier_options                    ""
% 3.96/0.99  --stdin                                 false
% 3.96/0.99  --stats_out                             all
% 3.96/0.99  
% 3.96/0.99  ------ General Options
% 3.96/0.99  
% 3.96/0.99  --fof                                   false
% 3.96/0.99  --time_out_real                         305.
% 3.96/0.99  --time_out_virtual                      -1.
% 3.96/0.99  --symbol_type_check                     false
% 3.96/0.99  --clausify_out                          false
% 3.96/0.99  --sig_cnt_out                           false
% 3.96/0.99  --trig_cnt_out                          false
% 3.96/0.99  --trig_cnt_out_tolerance                1.
% 3.96/0.99  --trig_cnt_out_sk_spl                   false
% 3.96/0.99  --abstr_cl_out                          false
% 3.96/0.99  
% 3.96/0.99  ------ Global Options
% 3.96/0.99  
% 3.96/0.99  --schedule                              default
% 3.96/0.99  --add_important_lit                     false
% 3.96/0.99  --prop_solver_per_cl                    1000
% 3.96/0.99  --min_unsat_core                        false
% 3.96/0.99  --soft_assumptions                      false
% 3.96/0.99  --soft_lemma_size                       3
% 3.96/0.99  --prop_impl_unit_size                   0
% 3.96/0.99  --prop_impl_unit                        []
% 3.96/0.99  --share_sel_clauses                     true
% 3.96/0.99  --reset_solvers                         false
% 3.96/0.99  --bc_imp_inh                            [conj_cone]
% 3.96/0.99  --conj_cone_tolerance                   3.
% 3.96/0.99  --extra_neg_conj                        none
% 3.96/0.99  --large_theory_mode                     true
% 3.96/0.99  --prolific_symb_bound                   200
% 3.96/0.99  --lt_threshold                          2000
% 3.96/0.99  --clause_weak_htbl                      true
% 3.96/0.99  --gc_record_bc_elim                     false
% 3.96/0.99  
% 3.96/0.99  ------ Preprocessing Options
% 3.96/0.99  
% 3.96/0.99  --preprocessing_flag                    true
% 3.96/0.99  --time_out_prep_mult                    0.1
% 3.96/0.99  --splitting_mode                        input
% 3.96/0.99  --splitting_grd                         true
% 3.96/0.99  --splitting_cvd                         false
% 3.96/0.99  --splitting_cvd_svl                     false
% 3.96/0.99  --splitting_nvd                         32
% 3.96/0.99  --sub_typing                            true
% 3.96/0.99  --prep_gs_sim                           true
% 3.96/0.99  --prep_unflatten                        true
% 3.96/0.99  --prep_res_sim                          true
% 3.96/0.99  --prep_upred                            true
% 3.96/0.99  --prep_sem_filter                       exhaustive
% 3.96/0.99  --prep_sem_filter_out                   false
% 3.96/0.99  --pred_elim                             true
% 3.96/0.99  --res_sim_input                         true
% 3.96/0.99  --eq_ax_congr_red                       true
% 3.96/0.99  --pure_diseq_elim                       true
% 3.96/0.99  --brand_transform                       false
% 3.96/0.99  --non_eq_to_eq                          false
% 3.96/0.99  --prep_def_merge                        true
% 3.96/0.99  --prep_def_merge_prop_impl              false
% 3.96/0.99  --prep_def_merge_mbd                    true
% 3.96/0.99  --prep_def_merge_tr_red                 false
% 3.96/0.99  --prep_def_merge_tr_cl                  false
% 3.96/0.99  --smt_preprocessing                     true
% 3.96/0.99  --smt_ac_axioms                         fast
% 3.96/0.99  --preprocessed_out                      false
% 3.96/0.99  --preprocessed_stats                    false
% 3.96/0.99  
% 3.96/0.99  ------ Abstraction refinement Options
% 3.96/0.99  
% 3.96/0.99  --abstr_ref                             []
% 3.96/0.99  --abstr_ref_prep                        false
% 3.96/0.99  --abstr_ref_until_sat                   false
% 3.96/0.99  --abstr_ref_sig_restrict                funpre
% 3.96/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.96/0.99  --abstr_ref_under                       []
% 3.96/0.99  
% 3.96/0.99  ------ SAT Options
% 3.96/0.99  
% 3.96/0.99  --sat_mode                              false
% 3.96/0.99  --sat_fm_restart_options                ""
% 3.96/0.99  --sat_gr_def                            false
% 3.96/0.99  --sat_epr_types                         true
% 3.96/0.99  --sat_non_cyclic_types                  false
% 3.96/0.99  --sat_finite_models                     false
% 3.96/0.99  --sat_fm_lemmas                         false
% 3.96/0.99  --sat_fm_prep                           false
% 3.96/0.99  --sat_fm_uc_incr                        true
% 3.96/0.99  --sat_out_model                         small
% 3.96/0.99  --sat_out_clauses                       false
% 3.96/0.99  
% 3.96/0.99  ------ QBF Options
% 3.96/0.99  
% 3.96/0.99  --qbf_mode                              false
% 3.96/0.99  --qbf_elim_univ                         false
% 3.96/0.99  --qbf_dom_inst                          none
% 3.96/0.99  --qbf_dom_pre_inst                      false
% 3.96/0.99  --qbf_sk_in                             false
% 3.96/0.99  --qbf_pred_elim                         true
% 3.96/0.99  --qbf_split                             512
% 3.96/0.99  
% 3.96/0.99  ------ BMC1 Options
% 3.96/0.99  
% 3.96/0.99  --bmc1_incremental                      false
% 3.96/0.99  --bmc1_axioms                           reachable_all
% 3.96/0.99  --bmc1_min_bound                        0
% 3.96/0.99  --bmc1_max_bound                        -1
% 3.96/0.99  --bmc1_max_bound_default                -1
% 3.96/0.99  --bmc1_symbol_reachability              true
% 3.96/0.99  --bmc1_property_lemmas                  false
% 3.96/0.99  --bmc1_k_induction                      false
% 3.96/0.99  --bmc1_non_equiv_states                 false
% 3.96/0.99  --bmc1_deadlock                         false
% 3.96/0.99  --bmc1_ucm                              false
% 3.96/0.99  --bmc1_add_unsat_core                   none
% 3.96/0.99  --bmc1_unsat_core_children              false
% 3.96/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.96/0.99  --bmc1_out_stat                         full
% 3.96/0.99  --bmc1_ground_init                      false
% 3.96/0.99  --bmc1_pre_inst_next_state              false
% 3.96/0.99  --bmc1_pre_inst_state                   false
% 3.96/0.99  --bmc1_pre_inst_reach_state             false
% 3.96/0.99  --bmc1_out_unsat_core                   false
% 3.96/0.99  --bmc1_aig_witness_out                  false
% 3.96/0.99  --bmc1_verbose                          false
% 3.96/0.99  --bmc1_dump_clauses_tptp                false
% 3.96/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.96/0.99  --bmc1_dump_file                        -
% 3.96/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.96/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.96/0.99  --bmc1_ucm_extend_mode                  1
% 3.96/0.99  --bmc1_ucm_init_mode                    2
% 3.96/0.99  --bmc1_ucm_cone_mode                    none
% 3.96/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.96/0.99  --bmc1_ucm_relax_model                  4
% 3.96/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.96/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.96/0.99  --bmc1_ucm_layered_model                none
% 3.96/0.99  --bmc1_ucm_max_lemma_size               10
% 3.96/0.99  
% 3.96/0.99  ------ AIG Options
% 3.96/0.99  
% 3.96/0.99  --aig_mode                              false
% 3.96/0.99  
% 3.96/0.99  ------ Instantiation Options
% 3.96/0.99  
% 3.96/0.99  --instantiation_flag                    true
% 3.96/0.99  --inst_sos_flag                         true
% 3.96/0.99  --inst_sos_phase                        true
% 3.96/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.96/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.96/0.99  --inst_lit_sel_side                     none
% 3.96/0.99  --inst_solver_per_active                1400
% 3.96/0.99  --inst_solver_calls_frac                1.
% 3.96/0.99  --inst_passive_queue_type               priority_queues
% 3.96/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.96/0.99  --inst_passive_queues_freq              [25;2]
% 3.96/0.99  --inst_dismatching                      true
% 3.96/0.99  --inst_eager_unprocessed_to_passive     true
% 3.96/0.99  --inst_prop_sim_given                   true
% 3.96/0.99  --inst_prop_sim_new                     false
% 3.96/0.99  --inst_subs_new                         false
% 3.96/0.99  --inst_eq_res_simp                      false
% 3.96/0.99  --inst_subs_given                       false
% 3.96/0.99  --inst_orphan_elimination               true
% 3.96/0.99  --inst_learning_loop_flag               true
% 3.96/0.99  --inst_learning_start                   3000
% 3.96/0.99  --inst_learning_factor                  2
% 3.96/0.99  --inst_start_prop_sim_after_learn       3
% 3.96/0.99  --inst_sel_renew                        solver
% 3.96/0.99  --inst_lit_activity_flag                true
% 3.96/0.99  --inst_restr_to_given                   false
% 3.96/0.99  --inst_activity_threshold               500
% 3.96/0.99  --inst_out_proof                        true
% 3.96/0.99  
% 3.96/0.99  ------ Resolution Options
% 3.96/0.99  
% 3.96/0.99  --resolution_flag                       false
% 3.96/0.99  --res_lit_sel                           adaptive
% 3.96/0.99  --res_lit_sel_side                      none
% 3.96/0.99  --res_ordering                          kbo
% 3.96/0.99  --res_to_prop_solver                    active
% 3.96/0.99  --res_prop_simpl_new                    false
% 3.96/0.99  --res_prop_simpl_given                  true
% 3.96/0.99  --res_passive_queue_type                priority_queues
% 3.96/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.96/0.99  --res_passive_queues_freq               [15;5]
% 3.96/0.99  --res_forward_subs                      full
% 3.96/0.99  --res_backward_subs                     full
% 3.96/0.99  --res_forward_subs_resolution           true
% 3.96/0.99  --res_backward_subs_resolution          true
% 3.96/0.99  --res_orphan_elimination                true
% 3.96/0.99  --res_time_limit                        2.
% 3.96/0.99  --res_out_proof                         true
% 3.96/0.99  
% 3.96/0.99  ------ Superposition Options
% 3.96/0.99  
% 3.96/0.99  --superposition_flag                    true
% 3.96/0.99  --sup_passive_queue_type                priority_queues
% 3.96/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.96/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.96/0.99  --demod_completeness_check              fast
% 3.96/0.99  --demod_use_ground                      true
% 3.96/0.99  --sup_to_prop_solver                    passive
% 3.96/0.99  --sup_prop_simpl_new                    true
% 3.96/0.99  --sup_prop_simpl_given                  true
% 3.96/0.99  --sup_fun_splitting                     true
% 3.96/0.99  --sup_smt_interval                      50000
% 3.96/0.99  
% 3.96/0.99  ------ Superposition Simplification Setup
% 3.96/0.99  
% 3.96/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.96/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.96/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.96/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.96/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.96/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.96/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.96/0.99  --sup_immed_triv                        [TrivRules]
% 3.96/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.96/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.96/0.99  --sup_immed_bw_main                     []
% 3.96/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.96/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.96/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.96/0.99  --sup_input_bw                          []
% 3.96/0.99  
% 3.96/0.99  ------ Combination Options
% 3.96/0.99  
% 3.96/0.99  --comb_res_mult                         3
% 3.96/0.99  --comb_sup_mult                         2
% 3.96/0.99  --comb_inst_mult                        10
% 3.96/0.99  
% 3.96/0.99  ------ Debug Options
% 3.96/0.99  
% 3.96/0.99  --dbg_backtrace                         false
% 3.96/0.99  --dbg_dump_prop_clauses                 false
% 3.96/0.99  --dbg_dump_prop_clauses_file            -
% 3.96/0.99  --dbg_out_stat                          false
% 3.96/0.99  
% 3.96/0.99  
% 3.96/0.99  
% 3.96/0.99  
% 3.96/0.99  ------ Proving...
% 3.96/0.99  
% 3.96/0.99  
% 3.96/0.99  % SZS status Theorem for theBenchmark.p
% 3.96/0.99  
% 3.96/0.99   Resolution empty clause
% 3.96/0.99  
% 3.96/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.96/0.99  
% 3.96/0.99  fof(f19,axiom,(
% 3.96/0.99    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 3.96/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.96/0.99  
% 3.96/0.99  fof(f22,plain,(
% 3.96/0.99    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 3.96/0.99    inference(pure_predicate_removal,[],[f19])).
% 3.96/0.99  
% 3.96/0.99  fof(f64,plain,(
% 3.96/0.99    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 3.96/0.99    inference(cnf_transformation,[],[f22])).
% 3.96/0.99  
% 3.96/0.99  fof(f8,axiom,(
% 3.96/0.99    ! [X0,X1] : (v1_relat_1(X1) => k3_xboole_0(k2_relat_1(X1),X0) = k2_relat_1(k8_relat_1(X0,X1)))),
% 3.96/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.96/0.99  
% 3.96/0.99  fof(f26,plain,(
% 3.96/0.99    ! [X0,X1] : (k3_xboole_0(k2_relat_1(X1),X0) = k2_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1))),
% 3.96/0.99    inference(ennf_transformation,[],[f8])).
% 3.96/0.99  
% 3.96/0.99  fof(f51,plain,(
% 3.96/0.99    ( ! [X0,X1] : (k3_xboole_0(k2_relat_1(X1),X0) = k2_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1)) )),
% 3.96/0.99    inference(cnf_transformation,[],[f26])).
% 3.96/0.99  
% 3.96/0.99  fof(f5,axiom,(
% 3.96/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.96/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.96/0.99  
% 3.96/0.99  fof(f48,plain,(
% 3.96/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.96/0.99    inference(cnf_transformation,[],[f5])).
% 3.96/0.99  
% 3.96/0.99  fof(f3,axiom,(
% 3.96/0.99    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.96/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.96/0.99  
% 3.96/0.99  fof(f46,plain,(
% 3.96/0.99    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.96/0.99    inference(cnf_transformation,[],[f3])).
% 3.96/0.99  
% 3.96/0.99  fof(f4,axiom,(
% 3.96/0.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.96/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.96/0.99  
% 3.96/0.99  fof(f47,plain,(
% 3.96/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.96/0.99    inference(cnf_transformation,[],[f4])).
% 3.96/0.99  
% 3.96/0.99  fof(f66,plain,(
% 3.96/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 3.96/0.99    inference(definition_unfolding,[],[f46,f47])).
% 3.96/0.99  
% 3.96/0.99  fof(f67,plain,(
% 3.96/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 3.96/0.99    inference(definition_unfolding,[],[f48,f66])).
% 3.96/0.99  
% 3.96/0.99  fof(f69,plain,(
% 3.96/0.99    ( ! [X0,X1] : (k1_setfam_1(k2_enumset1(k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),X0)) = k2_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1)) )),
% 3.96/0.99    inference(definition_unfolding,[],[f51,f67])).
% 3.96/0.99  
% 3.96/0.99  fof(f17,axiom,(
% 3.96/0.99    ! [X0,X1] : (v1_relat_1(X1) => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)))),
% 3.96/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.96/0.99  
% 3.96/0.99  fof(f35,plain,(
% 3.96/0.99    ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 3.96/0.99    inference(ennf_transformation,[],[f17])).
% 3.96/0.99  
% 3.96/0.99  fof(f62,plain,(
% 3.96/0.99    ( ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 3.96/0.99    inference(cnf_transformation,[],[f35])).
% 3.96/0.99  
% 3.96/0.99  fof(f70,plain,(
% 3.96/0.99    ( ! [X0,X1] : (k1_setfam_1(k2_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X0)) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 3.96/0.99    inference(definition_unfolding,[],[f62,f67])).
% 3.96/0.99  
% 3.96/0.99  fof(f12,axiom,(
% 3.96/0.99    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 3.96/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.96/0.99  
% 3.96/0.99  fof(f55,plain,(
% 3.96/0.99    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 3.96/0.99    inference(cnf_transformation,[],[f12])).
% 3.96/0.99  
% 3.96/0.99  fof(f56,plain,(
% 3.96/0.99    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 3.96/0.99    inference(cnf_transformation,[],[f12])).
% 3.96/0.99  
% 3.96/0.99  fof(f9,axiom,(
% 3.96/0.99    ! [X0,X1] : (v1_relat_1(X1) => k5_relat_1(X1,k6_relat_1(X0)) = k8_relat_1(X0,X1))),
% 3.96/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.96/0.99  
% 3.96/0.99  fof(f27,plain,(
% 3.96/0.99    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = k8_relat_1(X0,X1) | ~v1_relat_1(X1))),
% 3.96/0.99    inference(ennf_transformation,[],[f9])).
% 3.96/0.99  
% 3.96/0.99  fof(f52,plain,(
% 3.96/0.99    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = k8_relat_1(X0,X1) | ~v1_relat_1(X1)) )),
% 3.96/0.99    inference(cnf_transformation,[],[f27])).
% 3.96/0.99  
% 3.96/0.99  fof(f18,axiom,(
% 3.96/0.99    ! [X0,X1] : (v1_relat_1(X1) => k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0))),
% 3.96/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.96/0.99  
% 3.96/0.99  fof(f36,plain,(
% 3.96/0.99    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.96/0.99    inference(ennf_transformation,[],[f18])).
% 3.96/0.99  
% 3.96/0.99  fof(f63,plain,(
% 3.96/0.99    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.96/0.99    inference(cnf_transformation,[],[f36])).
% 3.96/0.99  
% 3.96/0.99  fof(f2,axiom,(
% 3.96/0.99    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 3.96/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.96/0.99  
% 3.96/0.99  fof(f45,plain,(
% 3.96/0.99    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 3.96/0.99    inference(cnf_transformation,[],[f2])).
% 3.96/0.99  
% 3.96/0.99  fof(f68,plain,(
% 3.96/0.99    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0)) )),
% 3.96/0.99    inference(definition_unfolding,[],[f45,f67])).
% 3.96/0.99  
% 3.96/0.99  fof(f14,axiom,(
% 3.96/0.99    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k5_relat_1(k6_relat_1(X0),X1) = X1))),
% 3.96/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.96/0.99  
% 3.96/0.99  fof(f31,plain,(
% 3.96/0.99    ! [X0,X1] : ((k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.96/0.99    inference(ennf_transformation,[],[f14])).
% 3.96/0.99  
% 3.96/0.99  fof(f32,plain,(
% 3.96/0.99    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 3.96/0.99    inference(flattening,[],[f31])).
% 3.96/0.99  
% 3.96/0.99  fof(f59,plain,(
% 3.96/0.99    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 3.96/0.99    inference(cnf_transformation,[],[f32])).
% 3.96/0.99  
% 3.96/0.99  fof(f6,axiom,(
% 3.96/0.99    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 3.96/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.96/0.99  
% 3.96/0.99  fof(f23,plain,(
% 3.96/0.99    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 3.96/0.99    inference(ennf_transformation,[],[f6])).
% 3.96/0.99  
% 3.96/0.99  fof(f24,plain,(
% 3.96/0.99    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 3.96/0.99    inference(flattening,[],[f23])).
% 3.96/0.99  
% 3.96/0.99  fof(f49,plain,(
% 3.96/0.99    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.96/0.99    inference(cnf_transformation,[],[f24])).
% 3.96/0.99  
% 3.96/0.99  fof(f16,axiom,(
% 3.96/0.99    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 3.96/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.96/0.99  
% 3.96/0.99  fof(f34,plain,(
% 3.96/0.99    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 3.96/0.99    inference(ennf_transformation,[],[f16])).
% 3.96/0.99  
% 3.96/0.99  fof(f61,plain,(
% 3.96/0.99    ( ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 3.96/0.99    inference(cnf_transformation,[],[f34])).
% 3.96/0.99  
% 3.96/0.99  fof(f7,axiom,(
% 3.96/0.99    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k7_relat_1(X1,X0),X2) = k7_relat_1(k5_relat_1(X1,X2),X0)))),
% 3.96/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.96/0.99  
% 3.96/0.99  fof(f25,plain,(
% 3.96/0.99    ! [X0,X1] : (! [X2] : (k5_relat_1(k7_relat_1(X1,X0),X2) = k7_relat_1(k5_relat_1(X1,X2),X0) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 3.96/0.99    inference(ennf_transformation,[],[f7])).
% 3.96/0.99  
% 3.96/0.99  fof(f50,plain,(
% 3.96/0.99    ( ! [X2,X0,X1] : (k5_relat_1(k7_relat_1(X1,X0),X2) = k7_relat_1(k5_relat_1(X1,X2),X0) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 3.96/0.99    inference(cnf_transformation,[],[f25])).
% 3.96/0.99  
% 3.96/0.99  fof(f20,conjecture,(
% 3.96/0.99    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 3.96/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.96/0.99  
% 3.96/0.99  fof(f21,negated_conjecture,(
% 3.96/0.99    ~! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 3.96/0.99    inference(negated_conjecture,[],[f20])).
% 3.96/0.99  
% 3.96/0.99  fof(f37,plain,(
% 3.96/0.99    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))),
% 3.96/0.99    inference(ennf_transformation,[],[f21])).
% 3.96/0.99  
% 3.96/0.99  fof(f40,plain,(
% 3.96/0.99    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 3.96/0.99    introduced(choice_axiom,[])).
% 3.96/0.99  
% 3.96/0.99  fof(f41,plain,(
% 3.96/0.99    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 3.96/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f37,f40])).
% 3.96/0.99  
% 3.96/0.99  fof(f65,plain,(
% 3.96/0.99    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 3.96/0.99    inference(cnf_transformation,[],[f41])).
% 3.96/0.99  
% 3.96/0.99  fof(f71,plain,(
% 3.96/0.99    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)))),
% 3.96/0.99    inference(definition_unfolding,[],[f65,f67])).
% 3.96/0.99  
% 3.96/0.99  cnf(c_19,plain,
% 3.96/0.99      ( v1_relat_1(k6_relat_1(X0)) ),
% 3.96/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_623,plain,
% 3.96/0.99      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 3.96/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_6,plain,
% 3.96/0.99      ( ~ v1_relat_1(X0)
% 3.96/0.99      | k1_setfam_1(k2_enumset1(k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X0),X1)) = k2_relat_1(k8_relat_1(X1,X0)) ),
% 3.96/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_634,plain,
% 3.96/0.99      ( k1_setfam_1(k2_enumset1(k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X0),X1)) = k2_relat_1(k8_relat_1(X1,X0))
% 3.96/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.96/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_17,plain,
% 3.96/0.99      ( ~ v1_relat_1(X0)
% 3.96/0.99      | k1_setfam_1(k2_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1)) ),
% 3.96/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_625,plain,
% 3.96/0.99      ( k1_setfam_1(k2_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1))
% 3.96/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.96/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_1084,plain,
% 3.96/0.99      ( k1_setfam_1(k2_enumset1(k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
% 3.96/0.99      inference(superposition,[status(thm)],[c_623,c_625]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_11,plain,
% 3.96/0.99      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 3.96/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_1085,plain,
% 3.96/0.99      ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
% 3.96/0.99      inference(light_normalisation,[status(thm)],[c_1084,c_11]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_1962,plain,
% 3.96/0.99      ( k1_relat_1(k7_relat_1(k6_relat_1(k2_relat_1(X0)),X1)) = k2_relat_1(k8_relat_1(X1,X0))
% 3.96/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.96/0.99      inference(demodulation,[status(thm)],[c_634,c_1085]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_1967,plain,
% 3.96/0.99      ( k1_relat_1(k7_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(X0))),X1)) = k2_relat_1(k8_relat_1(X1,k6_relat_1(X0))) ),
% 3.96/0.99      inference(superposition,[status(thm)],[c_623,c_1962]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_10,plain,
% 3.96/0.99      ( k2_relat_1(k6_relat_1(X0)) = X0 ),
% 3.96/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_1968,plain,
% 3.96/0.99      ( k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k2_relat_1(k8_relat_1(X1,k6_relat_1(X0))) ),
% 3.96/0.99      inference(light_normalisation,[status(thm)],[c_1967,c_10]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_7,plain,
% 3.96/0.99      ( ~ v1_relat_1(X0) | k5_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X1,X0) ),
% 3.96/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_633,plain,
% 3.96/0.99      ( k5_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X1,X0)
% 3.96/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.96/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_1540,plain,
% 3.96/0.99      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k8_relat_1(X1,k6_relat_1(X0)) ),
% 3.96/0.99      inference(superposition,[status(thm)],[c_623,c_633]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_18,plain,
% 3.96/0.99      ( ~ v1_relat_1(X0) | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
% 3.96/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_624,plain,
% 3.96/0.99      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
% 3.96/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.96/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_1236,plain,
% 3.96/0.99      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
% 3.96/0.99      inference(superposition,[status(thm)],[c_623,c_624]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_1541,plain,
% 3.96/0.99      ( k8_relat_1(X0,k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X0),X1) ),
% 3.96/0.99      inference(light_normalisation,[status(thm)],[c_1540,c_1236]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_1969,plain,
% 3.96/0.99      ( k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k2_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
% 3.96/0.99      inference(demodulation,[status(thm)],[c_1968,c_1541]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_3,plain,
% 3.96/0.99      ( r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0) ),
% 3.96/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_637,plain,
% 3.96/0.99      ( r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0) = iProver_top ),
% 3.96/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_1087,plain,
% 3.96/0.99      ( r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X0) = iProver_top ),
% 3.96/0.99      inference(demodulation,[status(thm)],[c_1085,c_637]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_2083,plain,
% 3.96/0.99      ( r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X1) = iProver_top ),
% 3.96/0.99      inference(demodulation,[status(thm)],[c_1969,c_1087]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_14,plain,
% 3.96/0.99      ( ~ r1_tarski(k1_relat_1(X0),X1)
% 3.96/0.99      | ~ v1_relat_1(X0)
% 3.96/0.99      | k5_relat_1(k6_relat_1(X1),X0) = X0 ),
% 3.96/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_628,plain,
% 3.96/0.99      ( k5_relat_1(k6_relat_1(X0),X1) = X1
% 3.96/0.99      | r1_tarski(k1_relat_1(X1),X0) != iProver_top
% 3.96/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.96/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_1955,plain,
% 3.96/0.99      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k6_relat_1(X1)
% 3.96/0.99      | r1_tarski(X1,X0) != iProver_top
% 3.96/0.99      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 3.96/0.99      inference(superposition,[status(thm)],[c_11,c_628]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_1956,plain,
% 3.96/0.99      ( k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X0)
% 3.96/0.99      | r1_tarski(X0,X1) != iProver_top
% 3.96/0.99      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 3.96/0.99      inference(demodulation,[status(thm)],[c_1955,c_1236]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_21,plain,
% 3.96/0.99      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 3.96/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_3228,plain,
% 3.96/0.99      ( r1_tarski(X0,X1) != iProver_top
% 3.96/0.99      | k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X0) ),
% 3.96/0.99      inference(global_propositional_subsumption,[status(thm)],[c_1956,c_21]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_3229,plain,
% 3.96/0.99      ( k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X0)
% 3.96/0.99      | r1_tarski(X0,X1) != iProver_top ),
% 3.96/0.99      inference(renaming,[status(thm)],[c_3228]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_3240,plain,
% 3.96/0.99      ( k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X1) = k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
% 3.96/0.99      inference(superposition,[status(thm)],[c_2083,c_3229]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_3531,plain,
% 3.96/0.99      ( k2_relat_1(k7_relat_1(k6_relat_1(X0),k2_relat_1(k7_relat_1(k6_relat_1(X1),X0)))) = k1_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X1),X0)))) ),
% 3.96/0.99      inference(superposition,[status(thm)],[c_3240,c_1969]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_3534,plain,
% 3.96/0.99      ( k2_relat_1(k7_relat_1(k6_relat_1(X0),k2_relat_1(k7_relat_1(k6_relat_1(X1),X0)))) = k2_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
% 3.96/0.99      inference(demodulation,[status(thm)],[c_3531,c_11]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_4,plain,
% 3.96/0.99      ( ~ v1_relat_1(X0) | ~ v1_relat_1(X1) | v1_relat_1(k5_relat_1(X1,X0)) ),
% 3.96/0.99      inference(cnf_transformation,[],[f49]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_636,plain,
% 3.96/0.99      ( v1_relat_1(X0) != iProver_top
% 3.96/0.99      | v1_relat_1(X1) != iProver_top
% 3.96/0.99      | v1_relat_1(k5_relat_1(X1,X0)) = iProver_top ),
% 3.96/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_16,plain,
% 3.96/0.99      ( ~ v1_relat_1(X0) | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ),
% 3.96/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_626,plain,
% 3.96/0.99      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
% 3.96/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.96/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_1832,plain,
% 3.96/0.99      ( k5_relat_1(k5_relat_1(X0,X1),k6_relat_1(k2_relat_1(k5_relat_1(X0,X1)))) = k5_relat_1(X0,X1)
% 3.96/0.99      | v1_relat_1(X1) != iProver_top
% 3.96/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.96/0.99      inference(superposition,[status(thm)],[c_636,c_626]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_7336,plain,
% 3.96/0.99      ( k5_relat_1(k5_relat_1(k6_relat_1(X0),X1),k6_relat_1(k2_relat_1(k5_relat_1(k6_relat_1(X0),X1)))) = k5_relat_1(k6_relat_1(X0),X1)
% 3.96/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.96/0.99      inference(superposition,[status(thm)],[c_623,c_1832]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_8328,plain,
% 3.96/0.99      ( k5_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),k6_relat_1(k2_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))))) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) ),
% 3.96/0.99      inference(superposition,[status(thm)],[c_623,c_7336]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_8331,plain,
% 3.96/0.99      ( k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)))) = k7_relat_1(k6_relat_1(X0),X1) ),
% 3.96/0.99      inference(light_normalisation,[status(thm)],[c_8328,c_1236]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_5,plain,
% 3.96/0.99      ( ~ v1_relat_1(X0)
% 3.96/0.99      | ~ v1_relat_1(X1)
% 3.96/0.99      | k7_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(k7_relat_1(X0,X2),X1) ),
% 3.96/0.99      inference(cnf_transformation,[],[f50]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_635,plain,
% 3.96/0.99      ( k7_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(k7_relat_1(X0,X2),X1)
% 3.96/0.99      | v1_relat_1(X0) != iProver_top
% 3.96/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.96/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_2379,plain,
% 3.96/0.99      ( k7_relat_1(k5_relat_1(k6_relat_1(X0),X1),X2) = k5_relat_1(k7_relat_1(k6_relat_1(X0),X2),X1)
% 3.96/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.96/0.99      inference(superposition,[status(thm)],[c_623,c_635]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_2670,plain,
% 3.96/0.99      ( k7_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),X2) = k5_relat_1(k7_relat_1(k6_relat_1(X0),X2),k6_relat_1(X1)) ),
% 3.96/0.99      inference(superposition,[status(thm)],[c_623,c_2379]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_2671,plain,
% 3.96/0.99      ( k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X0),X1) ),
% 3.96/0.99      inference(light_normalisation,[status(thm)],[c_2670,c_1236]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_8764,plain,
% 3.96/0.99      ( k7_relat_1(k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X0),X1) = k7_relat_1(k6_relat_1(X0),X1) ),
% 3.96/0.99      inference(superposition,[status(thm)],[c_8331,c_2671]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_8796,plain,
% 3.96/0.99      ( k7_relat_1(k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X1),k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k7_relat_1(k6_relat_1(X1),k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
% 3.96/0.99      inference(superposition,[status(thm)],[c_3534,c_8764]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_8850,plain,
% 3.96/0.99      ( k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))),k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k7_relat_1(k6_relat_1(X1),k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
% 3.96/0.99      inference(light_normalisation,[status(thm)],[c_8796,c_3240]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_1010,plain,
% 3.96/0.99      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(k2_relat_1(k6_relat_1(X0)))) = k6_relat_1(X0) ),
% 3.96/0.99      inference(superposition,[status(thm)],[c_623,c_626]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_1011,plain,
% 3.96/0.99      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X0)) = k6_relat_1(X0) ),
% 3.96/0.99      inference(light_normalisation,[status(thm)],[c_1010,c_10]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_1396,plain,
% 3.96/0.99      ( k7_relat_1(k6_relat_1(X0),X0) = k6_relat_1(X0) ),
% 3.96/0.99      inference(superposition,[status(thm)],[c_1011,c_1236]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_8851,plain,
% 3.96/0.99      ( k7_relat_1(k6_relat_1(X0),k2_relat_1(k7_relat_1(k6_relat_1(X1),X0))) = k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X1),X0))) ),
% 3.96/0.99      inference(demodulation,[status(thm)],[c_8850,c_1396]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_1828,plain,
% 3.96/0.99      ( v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = iProver_top
% 3.96/0.99      | v1_relat_1(k6_relat_1(X0)) != iProver_top
% 3.96/0.99      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 3.96/0.99      inference(superposition,[status(thm)],[c_1236,c_636]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_2794,plain,
% 3.96/0.99      ( v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = iProver_top
% 3.96/0.99      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 3.96/0.99      inference(global_propositional_subsumption,[status(thm)],[c_1828,c_21]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_1954,plain,
% 3.96/0.99      ( k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X0),X1)) = k7_relat_1(k6_relat_1(X0),X1)
% 3.96/0.99      | v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) != iProver_top ),
% 3.96/0.99      inference(superposition,[status(thm)],[c_1087,c_628]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_3221,plain,
% 3.96/0.99      ( k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X0),X1)) = k7_relat_1(k6_relat_1(X0),X1)
% 3.96/0.99      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 3.96/0.99      inference(superposition,[status(thm)],[c_2794,c_1954]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_3859,plain,
% 3.96/0.99      ( k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X0),X1)) = k7_relat_1(k6_relat_1(X0),X1) ),
% 3.96/0.99      inference(superposition,[status(thm)],[c_623,c_3221]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_9522,plain,
% 3.96/0.99      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X1),X0)))) = k7_relat_1(k6_relat_1(X0),k2_relat_1(k7_relat_1(k6_relat_1(X1),X0))) ),
% 3.96/0.99      inference(superposition,[status(thm)],[c_8851,c_3859]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_9580,plain,
% 3.96/0.99      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X1),X0)))) = k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X1),X0))) ),
% 3.96/0.99      inference(demodulation,[status(thm)],[c_9522,c_8851]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_9896,plain,
% 3.96/0.99      ( k5_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))),k6_relat_1(k2_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)))))) = k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X1),k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))))) ),
% 3.96/0.99      inference(superposition,[status(thm)],[c_8851,c_9580]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_1966,plain,
% 3.96/0.99      ( k1_relat_1(k7_relat_1(k6_relat_1(k2_relat_1(k5_relat_1(X0,X1))),X2)) = k2_relat_1(k8_relat_1(X2,k5_relat_1(X0,X1)))
% 3.96/0.99      | v1_relat_1(X1) != iProver_top
% 3.96/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.96/0.99      inference(superposition,[status(thm)],[c_636,c_1962]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_2087,plain,
% 3.96/0.99      ( k2_relat_1(k7_relat_1(k6_relat_1(X0),k2_relat_1(k5_relat_1(X1,X2)))) = k2_relat_1(k8_relat_1(X0,k5_relat_1(X1,X2)))
% 3.96/0.99      | v1_relat_1(X1) != iProver_top
% 3.96/0.99      | v1_relat_1(X2) != iProver_top ),
% 3.96/0.99      inference(demodulation,[status(thm)],[c_1966,c_1969]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_8315,plain,
% 3.96/0.99      ( k2_relat_1(k7_relat_1(k6_relat_1(X0),k2_relat_1(k5_relat_1(k6_relat_1(X1),X2)))) = k2_relat_1(k8_relat_1(X0,k5_relat_1(k6_relat_1(X1),X2)))
% 3.96/0.99      | v1_relat_1(X2) != iProver_top ),
% 3.96/0.99      inference(superposition,[status(thm)],[c_623,c_2087]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_8521,plain,
% 3.96/0.99      ( k2_relat_1(k7_relat_1(k6_relat_1(X0),k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))))) = k2_relat_1(k8_relat_1(X0,k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))) ),
% 3.96/0.99      inference(superposition,[status(thm)],[c_623,c_8315]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_2805,plain,
% 3.96/0.99      ( k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X2)) = k8_relat_1(X2,k7_relat_1(k6_relat_1(X0),X1))
% 3.96/0.99      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 3.96/0.99      inference(superposition,[status(thm)],[c_2794,c_633]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_2810,plain,
% 3.96/0.99      ( k8_relat_1(X0,k7_relat_1(k6_relat_1(X1),X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)
% 3.96/0.99      | v1_relat_1(k6_relat_1(X2)) != iProver_top ),
% 3.96/0.99      inference(light_normalisation,[status(thm)],[c_2805,c_2671]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_2948,plain,
% 3.96/0.99      ( k8_relat_1(X0,k7_relat_1(k6_relat_1(X1),X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) ),
% 3.96/0.99      inference(superposition,[status(thm)],[c_623,c_2810]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_8524,plain,
% 3.96/0.99      ( k2_relat_1(k7_relat_1(k6_relat_1(X0),k2_relat_1(k7_relat_1(k6_relat_1(X1),X2)))) = k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)) ),
% 3.96/0.99      inference(demodulation,[status(thm)],[c_8521,c_1236,c_2948]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_9924,plain,
% 3.96/0.99      ( k6_relat_1(k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0))) = k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X1),X0))) ),
% 3.96/0.99      inference(demodulation,[status(thm)],[c_9896,c_10,c_1011,c_1236,c_8524]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_2802,plain,
% 3.96/0.99      ( k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X1),X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X0)
% 3.96/0.99      | v1_relat_1(k6_relat_1(X2)) != iProver_top ),
% 3.96/0.99      inference(superposition,[status(thm)],[c_2794,c_624]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_4187,plain,
% 3.96/0.99      ( k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X1),X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X0) ),
% 3.96/0.99      inference(superposition,[status(thm)],[c_623,c_2802]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_4393,plain,
% 3.96/0.99      ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0) = k7_relat_1(k6_relat_1(X0),X1) ),
% 3.96/0.99      inference(superposition,[status(thm)],[c_4187,c_3859]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_9925,plain,
% 3.96/0.99      ( k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X1),X0))) ),
% 3.96/0.99      inference(light_normalisation,[status(thm)],[c_9924,c_4393]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_10403,plain,
% 3.96/0.99      ( k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X0) = k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X1),X0))) ),
% 3.96/0.99      inference(superposition,[status(thm)],[c_9925,c_3240]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_10394,plain,
% 3.96/0.99      ( k7_relat_1(k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X1),X0) = k7_relat_1(k6_relat_1(X1),X0) ),
% 3.96/0.99      inference(superposition,[status(thm)],[c_9925,c_8764]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_10404,plain,
% 3.96/0.99      ( k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X0) = k7_relat_1(k6_relat_1(X1),X0) ),
% 3.96/0.99      inference(light_normalisation,[status(thm)],[c_10394,c_3240]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_10405,plain,
% 3.96/0.99      ( k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k7_relat_1(k6_relat_1(X0),X1) ),
% 3.96/0.99      inference(demodulation,[status(thm)],[c_10404,c_10403]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_10409,plain,
% 3.96/0.99      ( k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k7_relat_1(k6_relat_1(X1),X0) ),
% 3.96/0.99      inference(demodulation,[status(thm)],[c_10405,c_9925]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_10512,plain,
% 3.96/0.99      ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X1) = k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
% 3.96/0.99      inference(light_normalisation,[status(thm)],[c_10403,c_10409]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_2676,plain,
% 3.96/0.99      ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X1) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
% 3.96/0.99      inference(superposition,[status(thm)],[c_1396,c_2671]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_2682,plain,
% 3.96/0.99      ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X1) = k7_relat_1(k6_relat_1(X0),X1) ),
% 3.96/0.99      inference(demodulation,[status(thm)],[c_2676,c_1236]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_10513,plain,
% 3.96/0.99      ( k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X1),X0) ),
% 3.96/0.99      inference(demodulation,[status(thm)],[c_10512,c_2682,c_10409]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_20,negated_conjecture,
% 3.96/0.99      ( k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) ),
% 3.96/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_1089,plain,
% 3.96/0.99      ( k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(sK0),sK1))) != k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) ),
% 3.96/0.99      inference(demodulation,[status(thm)],[c_1085,c_20]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_1395,plain,
% 3.96/0.99      ( k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(sK0),sK1))) != k7_relat_1(k6_relat_1(sK0),sK1) ),
% 3.96/0.99      inference(demodulation,[status(thm)],[c_1236,c_1089]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_2082,plain,
% 3.96/0.99      ( k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(sK1),sK0))) != k7_relat_1(k6_relat_1(sK0),sK1) ),
% 3.96/0.99      inference(demodulation,[status(thm)],[c_1969,c_1395]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_11192,plain,
% 3.96/0.99      ( k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(sK1),sK0))) != k7_relat_1(k6_relat_1(sK1),sK0) ),
% 3.96/0.99      inference(demodulation,[status(thm)],[c_10513,c_2082]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_11198,plain,
% 3.96/0.99      ( k7_relat_1(k6_relat_1(sK1),sK0) != k7_relat_1(k6_relat_1(sK0),sK1) ),
% 3.96/0.99      inference(demodulation,[status(thm)],[c_11192,c_10409]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_11390,plain,
% 3.96/0.99      ( $false ),
% 3.96/0.99      inference(superposition,[status(thm)],[c_10513,c_11198]) ).
% 3.96/0.99  
% 3.96/0.99  
% 3.96/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.96/0.99  
% 3.96/0.99  ------                               Statistics
% 3.96/0.99  
% 3.96/0.99  ------ General
% 3.96/0.99  
% 3.96/0.99  abstr_ref_over_cycles:                  0
% 3.96/0.99  abstr_ref_under_cycles:                 0
% 3.96/0.99  gc_basic_clause_elim:                   0
% 3.96/0.99  forced_gc_time:                         0
% 3.96/0.99  parsing_time:                           0.011
% 3.96/0.99  unif_index_cands_time:                  0.
% 3.96/0.99  unif_index_add_time:                    0.
% 3.96/0.99  orderings_time:                         0.
% 3.96/0.99  out_proof_time:                         0.008
% 3.96/0.99  total_time:                             0.352
% 3.96/0.99  num_of_symbols:                         43
% 3.96/0.99  num_of_terms:                           13862
% 3.96/0.99  
% 3.96/0.99  ------ Preprocessing
% 3.96/0.99  
% 3.96/0.99  num_of_splits:                          0
% 3.96/0.99  num_of_split_atoms:                     0
% 3.96/0.99  num_of_reused_defs:                     0
% 3.96/0.99  num_eq_ax_congr_red:                    9
% 3.96/0.99  num_of_sem_filtered_clauses:            1
% 3.96/0.99  num_of_subtypes:                        0
% 3.96/0.99  monotx_restored_types:                  0
% 3.96/0.99  sat_num_of_epr_types:                   0
% 3.96/0.99  sat_num_of_non_cyclic_types:            0
% 3.96/0.99  sat_guarded_non_collapsed_types:        0
% 3.96/0.99  num_pure_diseq_elim:                    0
% 3.96/0.99  simp_replaced_by:                       0
% 3.96/0.99  res_preprocessed:                       103
% 3.96/0.99  prep_upred:                             0
% 3.96/0.99  prep_unflattend:                        0
% 3.96/0.99  smt_new_axioms:                         0
% 3.96/0.99  pred_elim_cands:                        2
% 3.96/0.99  pred_elim:                              0
% 3.96/0.99  pred_elim_cl:                           0
% 3.96/0.99  pred_elim_cycles:                       2
% 3.96/0.99  merged_defs:                            0
% 3.96/0.99  merged_defs_ncl:                        0
% 3.96/0.99  bin_hyper_res:                          0
% 3.96/0.99  prep_cycles:                            4
% 3.96/0.99  pred_elim_time:                         0.
% 3.96/0.99  splitting_time:                         0.
% 3.96/0.99  sem_filter_time:                        0.
% 3.96/0.99  monotx_time:                            0.
% 3.96/0.99  subtype_inf_time:                       0.
% 3.96/0.99  
% 3.96/0.99  ------ Problem properties
% 3.96/0.99  
% 3.96/0.99  clauses:                                20
% 3.96/0.99  conjectures:                            1
% 3.96/0.99  epr:                                    2
% 3.96/0.99  horn:                                   20
% 3.96/0.99  ground:                                 1
% 3.96/0.99  unary:                                  6
% 3.96/0.99  binary:                                 8
% 3.96/0.99  lits:                                   41
% 3.96/0.99  lits_eq:                                13
% 3.96/0.99  fd_pure:                                0
% 3.96/0.99  fd_pseudo:                              0
% 3.96/0.99  fd_cond:                                0
% 3.96/0.99  fd_pseudo_cond:                         1
% 3.96/0.99  ac_symbols:                             0
% 3.96/0.99  
% 3.96/0.99  ------ Propositional Solver
% 3.96/0.99  
% 3.96/0.99  prop_solver_calls:                      29
% 3.96/0.99  prop_fast_solver_calls:                 681
% 3.96/0.99  smt_solver_calls:                       0
% 3.96/0.99  smt_fast_solver_calls:                  0
% 3.96/0.99  prop_num_of_clauses:                    4821
% 3.96/0.99  prop_preprocess_simplified:             9483
% 3.96/0.99  prop_fo_subsumed:                       6
% 3.96/0.99  prop_solver_time:                       0.
% 3.96/0.99  smt_solver_time:                        0.
% 3.96/0.99  smt_fast_solver_time:                   0.
% 3.96/0.99  prop_fast_solver_time:                  0.
% 3.96/0.99  prop_unsat_core_time:                   0.
% 3.96/0.99  
% 3.96/0.99  ------ QBF
% 3.96/0.99  
% 3.96/0.99  qbf_q_res:                              0
% 3.96/0.99  qbf_num_tautologies:                    0
% 3.96/0.99  qbf_prep_cycles:                        0
% 3.96/0.99  
% 3.96/0.99  ------ BMC1
% 3.96/0.99  
% 3.96/0.99  bmc1_current_bound:                     -1
% 3.96/0.99  bmc1_last_solved_bound:                 -1
% 3.96/0.99  bmc1_unsat_core_size:                   -1
% 3.96/0.99  bmc1_unsat_core_parents_size:           -1
% 3.96/0.99  bmc1_merge_next_fun:                    0
% 3.96/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.96/0.99  
% 3.96/0.99  ------ Instantiation
% 3.96/0.99  
% 3.96/0.99  inst_num_of_clauses:                    1442
% 3.96/0.99  inst_num_in_passive:                    273
% 3.96/0.99  inst_num_in_active:                     581
% 3.96/0.99  inst_num_in_unprocessed:                588
% 3.96/0.99  inst_num_of_loops:                      630
% 3.96/0.99  inst_num_of_learning_restarts:          0
% 3.96/0.99  inst_num_moves_active_passive:          48
% 3.96/0.99  inst_lit_activity:                      0
% 3.96/0.99  inst_lit_activity_moves:                0
% 3.96/0.99  inst_num_tautologies:                   0
% 3.96/0.99  inst_num_prop_implied:                  0
% 3.96/0.99  inst_num_existing_simplified:           0
% 3.96/0.99  inst_num_eq_res_simplified:             0
% 3.96/0.99  inst_num_child_elim:                    0
% 3.96/0.99  inst_num_of_dismatching_blockings:      554
% 3.96/0.99  inst_num_of_non_proper_insts:           1664
% 3.96/0.99  inst_num_of_duplicates:                 0
% 3.96/0.99  inst_inst_num_from_inst_to_res:         0
% 3.96/0.99  inst_dismatching_checking_time:         0.
% 3.96/0.99  
% 3.96/0.99  ------ Resolution
% 3.96/0.99  
% 3.96/0.99  res_num_of_clauses:                     0
% 3.96/0.99  res_num_in_passive:                     0
% 3.96/0.99  res_num_in_active:                      0
% 3.96/0.99  res_num_of_loops:                       107
% 3.96/0.99  res_forward_subset_subsumed:            246
% 3.96/0.99  res_backward_subset_subsumed:           0
% 3.96/0.99  res_forward_subsumed:                   0
% 3.96/0.99  res_backward_subsumed:                  0
% 3.96/0.99  res_forward_subsumption_resolution:     0
% 3.96/0.99  res_backward_subsumption_resolution:    0
% 3.96/0.99  res_clause_to_clause_subsumption:       1893
% 3.96/0.99  res_orphan_elimination:                 0
% 3.96/0.99  res_tautology_del:                      111
% 3.96/0.99  res_num_eq_res_simplified:              0
% 3.96/0.99  res_num_sel_changes:                    0
% 3.96/0.99  res_moves_from_active_to_pass:          0
% 3.96/0.99  
% 3.96/0.99  ------ Superposition
% 3.96/0.99  
% 3.96/0.99  sup_time_total:                         0.
% 3.96/0.99  sup_time_generating:                    0.
% 3.96/0.99  sup_time_sim_full:                      0.
% 3.96/0.99  sup_time_sim_immed:                     0.
% 3.96/0.99  
% 3.96/0.99  sup_num_of_clauses:                     416
% 3.96/0.99  sup_num_in_active:                      100
% 3.96/0.99  sup_num_in_passive:                     316
% 3.96/0.99  sup_num_of_loops:                       125
% 3.96/0.99  sup_fw_superposition:                   650
% 3.96/0.99  sup_bw_superposition:                   1112
% 3.96/0.99  sup_immediate_simplified:               1210
% 3.96/0.99  sup_given_eliminated:                   2
% 3.96/0.99  comparisons_done:                       0
% 3.96/0.99  comparisons_avoided:                    0
% 3.96/0.99  
% 3.96/0.99  ------ Simplifications
% 3.96/0.99  
% 3.96/0.99  
% 3.96/0.99  sim_fw_subset_subsumed:                 35
% 3.96/0.99  sim_bw_subset_subsumed:                 31
% 3.96/0.99  sim_fw_subsumed:                        245
% 3.96/0.99  sim_bw_subsumed:                        0
% 3.96/0.99  sim_fw_subsumption_res:                 0
% 3.96/0.99  sim_bw_subsumption_res:                 0
% 3.96/0.99  sim_tautology_del:                      11
% 3.96/0.99  sim_eq_tautology_del:                   270
% 3.96/0.99  sim_eq_res_simp:                        0
% 3.96/0.99  sim_fw_demodulated:                     804
% 3.96/0.99  sim_bw_demodulated:                     27
% 3.96/0.99  sim_light_normalised:                   389
% 3.96/0.99  sim_joinable_taut:                      0
% 3.96/0.99  sim_joinable_simp:                      0
% 3.96/0.99  sim_ac_normalised:                      0
% 3.96/0.99  sim_smt_subsumption:                    0
% 3.96/0.99  
%------------------------------------------------------------------------------
