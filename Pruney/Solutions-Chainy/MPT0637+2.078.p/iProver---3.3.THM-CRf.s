%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:50:09 EST 2020

% Result     : Theorem 4.16s
% Output     : CNFRefutation 4.16s
% Verified   : 
% Statistics : Number of formulae       :  175 (60827 expanded)
%              Number of clauses        :  113 (24590 expanded)
%              Number of leaves         :   20 (13795 expanded)
%              Depth                    :   39
%              Number of atoms          :  287 (86415 expanded)
%              Number of equality atoms :  205 (55990 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    8 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f2,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f59,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f39,f40])).

fof(f60,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f41,f59])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X0)) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f55,f60])).

fof(f13,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f61,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f38,f60])).

fof(f51,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0)) = k8_relat_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0)) = k8_relat_1(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0)) = k8_relat_1(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_enumset1(X1,X1,X1,k2_zfmisc_1(k1_relat_1(X1),X0))) = k8_relat_1(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f46,f60])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k5_relat_1(X1,k6_relat_1(X0)) = k8_relat_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = k8_relat_1(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = k8_relat_1(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f43,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f62,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f43,f60])).

fof(f19,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f57,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f14,axiom,(
    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k5_relat_1(k7_relat_1(X1,X0),X2) = k7_relat_1(k5_relat_1(X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k5_relat_1(k7_relat_1(X1,X0),X2) = k7_relat_1(k5_relat_1(X1,X2),X0)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k7_relat_1(X1,X0),X2) = k7_relat_1(k5_relat_1(X1,X2),X0)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f54,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f20,conjecture,(
    ! [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
    inference(negated_conjecture,[],[f20])).

fof(f35,plain,(
    ? [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) != k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
    inference(ennf_transformation,[],[f21])).

fof(f36,plain,
    ( ? [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) != k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))
   => k6_relat_1(k3_xboole_0(sK0,sK1)) != k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    k6_relat_1(k3_xboole_0(sK0,sK1)) != k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f35,f36])).

fof(f58,plain,(
    k6_relat_1(k3_xboole_0(sK0,sK1)) != k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f37])).

fof(f65,plain,(
    k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) != k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) ),
    inference(definition_unfolding,[],[f58,f60])).

cnf(c_1,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_483,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_14,plain,
    ( ~ v1_relat_1(X0)
    | k1_setfam_1(k2_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_473,plain,
    ( k1_setfam_1(k2_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_714,plain,
    ( k1_setfam_1(k2_enumset1(k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(superposition,[status(thm)],[c_483,c_473])).

cnf(c_10,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_715,plain,
    ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(light_normalisation,[status(thm)],[c_714,c_10])).

cnf(c_0,plain,
    ( r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_484,plain,
    ( r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_717,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_715,c_484])).

cnf(c_9,plain,
    ( k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_12,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_relat_1(X1)) = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_475,plain,
    ( k5_relat_1(X0,k6_relat_1(X1)) = X0
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1036,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k6_relat_1(X0)
    | r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9,c_475])).

cnf(c_15,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_472,plain,
    ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_850,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(superposition,[status(thm)],[c_483,c_472])).

cnf(c_1037,plain,
    ( k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X1)
    | r1_tarski(X1,X0) != iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1036,c_850])).

cnf(c_1441,plain,
    ( k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)))
    | v1_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_717,c_1037])).

cnf(c_8483,plain,
    ( k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
    inference(superposition,[status(thm)],[c_483,c_1441])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | k1_setfam_1(k2_enumset1(X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),X1))) = k8_relat_1(X1,X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_479,plain,
    ( k1_setfam_1(k2_enumset1(X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),X1))) = k8_relat_1(X1,X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1076,plain,
    ( k1_relat_1(k7_relat_1(k6_relat_1(X0),k2_zfmisc_1(k1_relat_1(X0),X1))) = k8_relat_1(X1,X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_479,c_715])).

cnf(c_1080,plain,
    ( k1_relat_1(k7_relat_1(k6_relat_1(k6_relat_1(X0)),k2_zfmisc_1(k1_relat_1(k6_relat_1(X0)),X1))) = k8_relat_1(X1,k6_relat_1(X0)) ),
    inference(superposition,[status(thm)],[c_483,c_1076])).

cnf(c_1082,plain,
    ( k1_relat_1(k7_relat_1(k6_relat_1(k6_relat_1(X0)),k2_zfmisc_1(X0,X1))) = k8_relat_1(X1,k6_relat_1(X0)) ),
    inference(light_normalisation,[status(thm)],[c_1080,c_10])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X1,X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_480,plain,
    ( k5_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X1,X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_933,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k8_relat_1(X1,k6_relat_1(X0)) ),
    inference(superposition,[status(thm)],[c_483,c_480])).

cnf(c_934,plain,
    ( k8_relat_1(X0,k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(light_normalisation,[status(thm)],[c_933,c_850])).

cnf(c_1083,plain,
    ( k1_relat_1(k7_relat_1(k6_relat_1(k6_relat_1(X0)),k2_zfmisc_1(X0,X1))) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(demodulation,[status(thm)],[c_1082,c_934])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_482,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1012,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_482,c_715])).

cnf(c_1251,plain,
    ( v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1083,c_1012])).

cnf(c_16,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(X0,k1_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_471,plain,
    ( k7_relat_1(X0,k1_relat_1(X0)) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1315,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k7_relat_1(k6_relat_1(X0),X1)
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1251,c_471])).

cnf(c_2250,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(superposition,[status(thm)],[c_483,c_1315])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_477,plain,
    ( k5_relat_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k5_relat_1(X1,X0))
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1173,plain,
    ( k5_relat_1(k4_relat_1(k6_relat_1(X0)),k4_relat_1(X1)) = k4_relat_1(k5_relat_1(X1,k6_relat_1(X0)))
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_483,c_477])).

cnf(c_11,plain,
    ( k4_relat_1(k6_relat_1(X0)) = k6_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1175,plain,
    ( k4_relat_1(k5_relat_1(X0,k6_relat_1(X1))) = k5_relat_1(k6_relat_1(X1),k4_relat_1(X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1173,c_11])).

cnf(c_1310,plain,
    ( k4_relat_1(k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X2))) = k5_relat_1(k6_relat_1(X2),k4_relat_1(k7_relat_1(k6_relat_1(X0),X1)))
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1251,c_1175])).

cnf(c_1183,plain,
    ( k4_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k5_relat_1(k6_relat_1(X1),k4_relat_1(k6_relat_1(X0))) ),
    inference(superposition,[status(thm)],[c_483,c_1175])).

cnf(c_1185,plain,
    ( k4_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) ),
    inference(light_normalisation,[status(thm)],[c_1183,c_11,c_850])).

cnf(c_1186,plain,
    ( k4_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(demodulation,[status(thm)],[c_1185,c_850])).

cnf(c_1318,plain,
    ( k4_relat_1(k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X2))) = k5_relat_1(k6_relat_1(X2),k7_relat_1(k6_relat_1(X1),X0))
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1310,c_1186])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k5_relat_1(k7_relat_1(X1,X2),X0) = k7_relat_1(k5_relat_1(X1,X0),X2) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_481,plain,
    ( k5_relat_1(k7_relat_1(X0,X1),X2) = k7_relat_1(k5_relat_1(X0,X2),X1)
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1556,plain,
    ( k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) = k7_relat_1(k5_relat_1(k6_relat_1(X0),X2),X1)
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_483,c_481])).

cnf(c_1742,plain,
    ( k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X2)) = k7_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X2)),X1) ),
    inference(superposition,[status(thm)],[c_483,c_1556])).

cnf(c_1313,plain,
    ( k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X2)) = k8_relat_1(X2,k7_relat_1(k6_relat_1(X0),X1))
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1251,c_480])).

cnf(c_1480,plain,
    ( k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X2)) = k8_relat_1(X2,k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(superposition,[status(thm)],[c_483,c_1313])).

cnf(c_1745,plain,
    ( k7_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),X2) = k8_relat_1(X1,k7_relat_1(k6_relat_1(X0),X2)) ),
    inference(light_normalisation,[status(thm)],[c_1742,c_1480])).

cnf(c_1746,plain,
    ( k8_relat_1(X0,k7_relat_1(k6_relat_1(X1),X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) ),
    inference(demodulation,[status(thm)],[c_1745,c_850])).

cnf(c_1819,plain,
    ( k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X0),X1) ),
    inference(demodulation,[status(thm)],[c_1746,c_1480])).

cnf(c_2801,plain,
    ( k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)) = k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X2),X1))
    | v1_relat_1(k6_relat_1(X2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1318,c_1819])).

cnf(c_1316,plain,
    ( k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X1),X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X0)
    | v1_relat_1(k6_relat_1(X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1251,c_472])).

cnf(c_1919,plain,
    ( k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X1),X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X0) ),
    inference(superposition,[status(thm)],[c_483,c_1316])).

cnf(c_2802,plain,
    ( k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X1),X0)
    | v1_relat_1(k6_relat_1(X2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2801,c_1919])).

cnf(c_2806,plain,
    ( k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X1),X0) ),
    inference(superposition,[status(thm)],[c_483,c_2802])).

cnf(c_2856,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X1),X0) = k4_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(superposition,[status(thm)],[c_2250,c_2806])).

cnf(c_2867,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X1),X0) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(light_normalisation,[status(thm)],[c_2856,c_1186])).

cnf(c_1558,plain,
    ( k5_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2),X3) = k7_relat_1(k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),X3),X2)
    | v1_relat_1(X3) != iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1251,c_481])).

cnf(c_4663,plain,
    ( k5_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2),X3) = k7_relat_1(k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),X3),X2)
    | v1_relat_1(X3) != iProver_top ),
    inference(superposition,[status(thm)],[c_483,c_1558])).

cnf(c_4699,plain,
    ( k5_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2),k6_relat_1(X3)) = k7_relat_1(k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X3)),X2) ),
    inference(superposition,[status(thm)],[c_483,c_4663])).

cnf(c_4702,plain,
    ( k5_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2),k6_relat_1(X3)) = k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X3),X0),X1),X2) ),
    inference(demodulation,[status(thm)],[c_4699,c_1819])).

cnf(c_4855,plain,
    ( k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(k6_relat_1(X1),X2))),X2),X1) = k5_relat_1(k7_relat_1(k6_relat_1(X2),X1),k6_relat_1(X0)) ),
    inference(superposition,[status(thm)],[c_2867,c_4702])).

cnf(c_4874,plain,
    ( k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(k6_relat_1(X1),X2))),X2),X1) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X2),X1) ),
    inference(demodulation,[status(thm)],[c_4855,c_1819])).

cnf(c_8883,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X1),X0) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0) ),
    inference(superposition,[status(thm)],[c_8483,c_4874])).

cnf(c_8890,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(light_normalisation,[status(thm)],[c_8883,c_2867])).

cnf(c_9134,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0) = k4_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
    inference(superposition,[status(thm)],[c_8890,c_2806])).

cnf(c_9146,plain,
    ( k4_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(demodulation,[status(thm)],[c_9134,c_8890])).

cnf(c_9169,plain,
    ( k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(superposition,[status(thm)],[c_9146,c_1186])).

cnf(c_6,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_478,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1440,plain,
    ( k7_relat_1(k6_relat_1(k2_relat_1(X0)),k2_relat_1(k5_relat_1(X1,X0))) = k6_relat_1(k2_relat_1(k5_relat_1(X1,X0)))
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k6_relat_1(k2_relat_1(k5_relat_1(X1,X0)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_478,c_1037])).

cnf(c_6813,plain,
    ( k7_relat_1(k6_relat_1(k2_relat_1(X0)),k2_relat_1(k5_relat_1(X1,X0))) = k6_relat_1(k2_relat_1(k5_relat_1(X1,X0)))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_483,c_1440])).

cnf(c_6936,plain,
    ( k7_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(X0))),k2_relat_1(k5_relat_1(X1,k6_relat_1(X0)))) = k6_relat_1(k2_relat_1(k5_relat_1(X1,k6_relat_1(X0))))
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_483,c_6813])).

cnf(c_6939,plain,
    ( k7_relat_1(k6_relat_1(X0),k2_relat_1(k5_relat_1(X1,k6_relat_1(X0)))) = k6_relat_1(k2_relat_1(k5_relat_1(X1,k6_relat_1(X0))))
    | v1_relat_1(X1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6936,c_9])).

cnf(c_6951,plain,
    ( k7_relat_1(k6_relat_1(X0),k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)))) = k6_relat_1(k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)))) ),
    inference(superposition,[status(thm)],[c_483,c_6939])).

cnf(c_6955,plain,
    ( k7_relat_1(k6_relat_1(X0),k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
    inference(demodulation,[status(thm)],[c_6951,c_850])).

cnf(c_7122,plain,
    ( k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X0) = k4_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)))) ),
    inference(superposition,[status(thm)],[c_6955,c_1186])).

cnf(c_7206,plain,
    ( k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X0) = k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
    inference(demodulation,[status(thm)],[c_7122,c_11])).

cnf(c_13,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_474,plain,
    ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1314,plain,
    ( k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)))) = k7_relat_1(k6_relat_1(X0),X1)
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1251,c_474])).

cnf(c_2387,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X0),X1) = k7_relat_1(k6_relat_1(X0),X1)
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1314,c_1819])).

cnf(c_2391,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X0),X1) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(superposition,[status(thm)],[c_483,c_2387])).

cnf(c_7631,plain,
    ( k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X1) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(demodulation,[status(thm)],[c_7206,c_2391])).

cnf(c_8019,plain,
    ( k7_relat_1(k6_relat_1(X0),k2_relat_1(k7_relat_1(k6_relat_1(X1),X0))) = k4_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
    inference(superposition,[status(thm)],[c_7631,c_1186])).

cnf(c_8056,plain,
    ( k7_relat_1(k6_relat_1(X0),k2_relat_1(k7_relat_1(k6_relat_1(X1),X0))) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(demodulation,[status(thm)],[c_8019,c_1186])).

cnf(c_8841,plain,
    ( k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),k2_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))))) = k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X0) ),
    inference(superposition,[status(thm)],[c_8483,c_8056])).

cnf(c_666,plain,
    ( k7_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X0))) = k6_relat_1(X0) ),
    inference(superposition,[status(thm)],[c_483,c_471])).

cnf(c_667,plain,
    ( k7_relat_1(k6_relat_1(X0),X0) = k6_relat_1(X0) ),
    inference(light_normalisation,[status(thm)],[c_666,c_10])).

cnf(c_8938,plain,
    ( k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X0) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
    inference(demodulation,[status(thm)],[c_8841,c_9,c_667])).

cnf(c_9778,plain,
    ( k7_relat_1(k6_relat_1(k1_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))))),k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X0))) ),
    inference(superposition,[status(thm)],[c_7206,c_8938])).

cnf(c_9374,plain,
    ( k7_relat_1(k6_relat_1(X0),k2_relat_1(k7_relat_1(k6_relat_1(X1),X0))) = k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
    inference(superposition,[status(thm)],[c_9169,c_6955])).

cnf(c_9461,plain,
    ( k7_relat_1(k6_relat_1(X0),k2_relat_1(k7_relat_1(k6_relat_1(X1),X0))) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(superposition,[status(thm)],[c_9169,c_7631])).

cnf(c_9465,plain,
    ( k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(demodulation,[status(thm)],[c_9374,c_9461])).

cnf(c_9923,plain,
    ( k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),k2_relat_1(k7_relat_1(k6_relat_1(X1),X0))) = k6_relat_1(k1_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X1),X0))))) ),
    inference(light_normalisation,[status(thm)],[c_9778,c_7206,c_9465])).

cnf(c_9924,plain,
    ( k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),k2_relat_1(k7_relat_1(k6_relat_1(X1),X0))) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(demodulation,[status(thm)],[c_9923,c_10,c_9465])).

cnf(c_10174,plain,
    ( k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),k2_relat_1(k7_relat_1(k6_relat_1(X1),X0))))) = k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
    inference(superposition,[status(thm)],[c_9924,c_6955])).

cnf(c_10277,plain,
    ( k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
    inference(demodulation,[status(thm)],[c_10174,c_9924])).

cnf(c_9779,plain,
    ( k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X1))) ),
    inference(superposition,[status(thm)],[c_7631,c_8938])).

cnf(c_9922,plain,
    ( k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
    inference(light_normalisation,[status(thm)],[c_9779,c_7631])).

cnf(c_10278,plain,
    ( k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(light_normalisation,[status(thm)],[c_10277,c_9465,c_9922])).

cnf(c_17,negated_conjecture,
    ( k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) != k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_719,plain,
    ( k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(sK0),sK1))) != k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) ),
    inference(demodulation,[status(thm)],[c_715,c_17])).

cnf(c_883,plain,
    ( k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(sK0),sK1))) != k7_relat_1(k6_relat_1(sK0),sK1) ),
    inference(demodulation,[status(thm)],[c_850,c_719])).

cnf(c_11479,plain,
    ( k7_relat_1(k6_relat_1(sK1),sK0) != k7_relat_1(k6_relat_1(sK0),sK1) ),
    inference(demodulation,[status(thm)],[c_10278,c_883])).

cnf(c_11742,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_9169,c_11479])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:14:39 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 4.16/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.16/0.99  
% 4.16/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 4.16/0.99  
% 4.16/0.99  ------  iProver source info
% 4.16/0.99  
% 4.16/0.99  git: date: 2020-06-30 10:37:57 +0100
% 4.16/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 4.16/0.99  git: non_committed_changes: false
% 4.16/0.99  git: last_make_outside_of_git: false
% 4.16/0.99  
% 4.16/0.99  ------ 
% 4.16/0.99  
% 4.16/0.99  ------ Input Options
% 4.16/0.99  
% 4.16/0.99  --out_options                           all
% 4.16/0.99  --tptp_safe_out                         true
% 4.16/0.99  --problem_path                          ""
% 4.16/0.99  --include_path                          ""
% 4.16/0.99  --clausifier                            res/vclausify_rel
% 4.16/0.99  --clausifier_options                    ""
% 4.16/0.99  --stdin                                 false
% 4.16/0.99  --stats_out                             all
% 4.16/0.99  
% 4.16/0.99  ------ General Options
% 4.16/0.99  
% 4.16/0.99  --fof                                   false
% 4.16/0.99  --time_out_real                         305.
% 4.16/0.99  --time_out_virtual                      -1.
% 4.16/0.99  --symbol_type_check                     false
% 4.16/0.99  --clausify_out                          false
% 4.16/0.99  --sig_cnt_out                           false
% 4.16/0.99  --trig_cnt_out                          false
% 4.16/0.99  --trig_cnt_out_tolerance                1.
% 4.16/0.99  --trig_cnt_out_sk_spl                   false
% 4.16/0.99  --abstr_cl_out                          false
% 4.16/0.99  
% 4.16/0.99  ------ Global Options
% 4.16/0.99  
% 4.16/0.99  --schedule                              default
% 4.16/0.99  --add_important_lit                     false
% 4.16/0.99  --prop_solver_per_cl                    1000
% 4.16/0.99  --min_unsat_core                        false
% 4.16/0.99  --soft_assumptions                      false
% 4.16/0.99  --soft_lemma_size                       3
% 4.16/0.99  --prop_impl_unit_size                   0
% 4.16/0.99  --prop_impl_unit                        []
% 4.16/0.99  --share_sel_clauses                     true
% 4.16/0.99  --reset_solvers                         false
% 4.16/0.99  --bc_imp_inh                            [conj_cone]
% 4.16/0.99  --conj_cone_tolerance                   3.
% 4.16/0.99  --extra_neg_conj                        none
% 4.16/0.99  --large_theory_mode                     true
% 4.16/0.99  --prolific_symb_bound                   200
% 4.16/0.99  --lt_threshold                          2000
% 4.16/0.99  --clause_weak_htbl                      true
% 4.16/0.99  --gc_record_bc_elim                     false
% 4.16/0.99  
% 4.16/0.99  ------ Preprocessing Options
% 4.16/0.99  
% 4.16/0.99  --preprocessing_flag                    true
% 4.16/0.99  --time_out_prep_mult                    0.1
% 4.16/0.99  --splitting_mode                        input
% 4.16/0.99  --splitting_grd                         true
% 4.16/0.99  --splitting_cvd                         false
% 4.16/0.99  --splitting_cvd_svl                     false
% 4.16/0.99  --splitting_nvd                         32
% 4.16/0.99  --sub_typing                            true
% 4.16/0.99  --prep_gs_sim                           true
% 4.16/0.99  --prep_unflatten                        true
% 4.16/0.99  --prep_res_sim                          true
% 4.16/0.99  --prep_upred                            true
% 4.16/0.99  --prep_sem_filter                       exhaustive
% 4.16/0.99  --prep_sem_filter_out                   false
% 4.16/0.99  --pred_elim                             true
% 4.16/0.99  --res_sim_input                         true
% 4.16/0.99  --eq_ax_congr_red                       true
% 4.16/0.99  --pure_diseq_elim                       true
% 4.16/0.99  --brand_transform                       false
% 4.16/0.99  --non_eq_to_eq                          false
% 4.16/0.99  --prep_def_merge                        true
% 4.16/0.99  --prep_def_merge_prop_impl              false
% 4.16/0.99  --prep_def_merge_mbd                    true
% 4.16/0.99  --prep_def_merge_tr_red                 false
% 4.16/0.99  --prep_def_merge_tr_cl                  false
% 4.16/0.99  --smt_preprocessing                     true
% 4.16/0.99  --smt_ac_axioms                         fast
% 4.16/0.99  --preprocessed_out                      false
% 4.16/0.99  --preprocessed_stats                    false
% 4.16/0.99  
% 4.16/0.99  ------ Abstraction refinement Options
% 4.16/0.99  
% 4.16/0.99  --abstr_ref                             []
% 4.16/0.99  --abstr_ref_prep                        false
% 4.16/0.99  --abstr_ref_until_sat                   false
% 4.16/0.99  --abstr_ref_sig_restrict                funpre
% 4.16/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 4.16/0.99  --abstr_ref_under                       []
% 4.16/0.99  
% 4.16/0.99  ------ SAT Options
% 4.16/0.99  
% 4.16/0.99  --sat_mode                              false
% 4.16/0.99  --sat_fm_restart_options                ""
% 4.16/0.99  --sat_gr_def                            false
% 4.16/0.99  --sat_epr_types                         true
% 4.16/0.99  --sat_non_cyclic_types                  false
% 4.16/0.99  --sat_finite_models                     false
% 4.16/0.99  --sat_fm_lemmas                         false
% 4.16/0.99  --sat_fm_prep                           false
% 4.16/0.99  --sat_fm_uc_incr                        true
% 4.16/0.99  --sat_out_model                         small
% 4.16/0.99  --sat_out_clauses                       false
% 4.16/0.99  
% 4.16/0.99  ------ QBF Options
% 4.16/0.99  
% 4.16/0.99  --qbf_mode                              false
% 4.16/0.99  --qbf_elim_univ                         false
% 4.16/0.99  --qbf_dom_inst                          none
% 4.16/0.99  --qbf_dom_pre_inst                      false
% 4.16/0.99  --qbf_sk_in                             false
% 4.16/0.99  --qbf_pred_elim                         true
% 4.16/0.99  --qbf_split                             512
% 4.16/0.99  
% 4.16/0.99  ------ BMC1 Options
% 4.16/0.99  
% 4.16/0.99  --bmc1_incremental                      false
% 4.16/0.99  --bmc1_axioms                           reachable_all
% 4.16/0.99  --bmc1_min_bound                        0
% 4.16/0.99  --bmc1_max_bound                        -1
% 4.16/0.99  --bmc1_max_bound_default                -1
% 4.16/0.99  --bmc1_symbol_reachability              true
% 4.16/0.99  --bmc1_property_lemmas                  false
% 4.16/0.99  --bmc1_k_induction                      false
% 4.16/0.99  --bmc1_non_equiv_states                 false
% 4.16/0.99  --bmc1_deadlock                         false
% 4.16/0.99  --bmc1_ucm                              false
% 4.16/0.99  --bmc1_add_unsat_core                   none
% 4.16/0.99  --bmc1_unsat_core_children              false
% 4.16/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 4.16/0.99  --bmc1_out_stat                         full
% 4.16/0.99  --bmc1_ground_init                      false
% 4.16/0.99  --bmc1_pre_inst_next_state              false
% 4.16/0.99  --bmc1_pre_inst_state                   false
% 4.16/0.99  --bmc1_pre_inst_reach_state             false
% 4.16/0.99  --bmc1_out_unsat_core                   false
% 4.16/0.99  --bmc1_aig_witness_out                  false
% 4.16/0.99  --bmc1_verbose                          false
% 4.16/0.99  --bmc1_dump_clauses_tptp                false
% 4.16/0.99  --bmc1_dump_unsat_core_tptp             false
% 4.16/0.99  --bmc1_dump_file                        -
% 4.16/0.99  --bmc1_ucm_expand_uc_limit              128
% 4.16/0.99  --bmc1_ucm_n_expand_iterations          6
% 4.16/0.99  --bmc1_ucm_extend_mode                  1
% 4.16/0.99  --bmc1_ucm_init_mode                    2
% 4.16/0.99  --bmc1_ucm_cone_mode                    none
% 4.16/0.99  --bmc1_ucm_reduced_relation_type        0
% 4.16/0.99  --bmc1_ucm_relax_model                  4
% 4.16/0.99  --bmc1_ucm_full_tr_after_sat            true
% 4.16/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 4.16/0.99  --bmc1_ucm_layered_model                none
% 4.16/0.99  --bmc1_ucm_max_lemma_size               10
% 4.16/0.99  
% 4.16/0.99  ------ AIG Options
% 4.16/0.99  
% 4.16/0.99  --aig_mode                              false
% 4.16/0.99  
% 4.16/0.99  ------ Instantiation Options
% 4.16/0.99  
% 4.16/0.99  --instantiation_flag                    true
% 4.16/0.99  --inst_sos_flag                         true
% 4.16/0.99  --inst_sos_phase                        true
% 4.16/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.16/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.16/0.99  --inst_lit_sel_side                     num_symb
% 4.16/0.99  --inst_solver_per_active                1400
% 4.16/0.99  --inst_solver_calls_frac                1.
% 4.16/0.99  --inst_passive_queue_type               priority_queues
% 4.16/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.16/0.99  --inst_passive_queues_freq              [25;2]
% 4.16/0.99  --inst_dismatching                      true
% 4.16/0.99  --inst_eager_unprocessed_to_passive     true
% 4.16/0.99  --inst_prop_sim_given                   true
% 4.16/0.99  --inst_prop_sim_new                     false
% 4.16/0.99  --inst_subs_new                         false
% 4.16/0.99  --inst_eq_res_simp                      false
% 4.16/0.99  --inst_subs_given                       false
% 4.16/0.99  --inst_orphan_elimination               true
% 4.16/0.99  --inst_learning_loop_flag               true
% 4.16/0.99  --inst_learning_start                   3000
% 4.16/0.99  --inst_learning_factor                  2
% 4.16/0.99  --inst_start_prop_sim_after_learn       3
% 4.16/0.99  --inst_sel_renew                        solver
% 4.16/0.99  --inst_lit_activity_flag                true
% 4.16/0.99  --inst_restr_to_given                   false
% 4.16/0.99  --inst_activity_threshold               500
% 4.16/0.99  --inst_out_proof                        true
% 4.16/0.99  
% 4.16/0.99  ------ Resolution Options
% 4.16/0.99  
% 4.16/0.99  --resolution_flag                       true
% 4.16/0.99  --res_lit_sel                           adaptive
% 4.16/0.99  --res_lit_sel_side                      none
% 4.16/0.99  --res_ordering                          kbo
% 4.16/0.99  --res_to_prop_solver                    active
% 4.16/0.99  --res_prop_simpl_new                    false
% 4.16/0.99  --res_prop_simpl_given                  true
% 4.16/0.99  --res_passive_queue_type                priority_queues
% 4.16/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.16/0.99  --res_passive_queues_freq               [15;5]
% 4.16/0.99  --res_forward_subs                      full
% 4.16/0.99  --res_backward_subs                     full
% 4.16/0.99  --res_forward_subs_resolution           true
% 4.16/0.99  --res_backward_subs_resolution          true
% 4.16/0.99  --res_orphan_elimination                true
% 4.16/0.99  --res_time_limit                        2.
% 4.16/0.99  --res_out_proof                         true
% 4.16/0.99  
% 4.16/0.99  ------ Superposition Options
% 4.16/0.99  
% 4.16/0.99  --superposition_flag                    true
% 4.16/0.99  --sup_passive_queue_type                priority_queues
% 4.16/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.16/0.99  --sup_passive_queues_freq               [8;1;4]
% 4.16/0.99  --demod_completeness_check              fast
% 4.16/0.99  --demod_use_ground                      true
% 4.16/0.99  --sup_to_prop_solver                    passive
% 4.16/0.99  --sup_prop_simpl_new                    true
% 4.16/0.99  --sup_prop_simpl_given                  true
% 4.16/0.99  --sup_fun_splitting                     true
% 4.16/0.99  --sup_smt_interval                      50000
% 4.16/0.99  
% 4.16/0.99  ------ Superposition Simplification Setup
% 4.16/0.99  
% 4.16/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 4.16/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 4.16/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 4.16/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 4.16/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 4.16/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 4.16/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 4.16/0.99  --sup_immed_triv                        [TrivRules]
% 4.16/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.16/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.16/0.99  --sup_immed_bw_main                     []
% 4.16/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 4.16/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 4.16/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.16/0.99  --sup_input_bw                          []
% 4.16/0.99  
% 4.16/0.99  ------ Combination Options
% 4.16/0.99  
% 4.16/0.99  --comb_res_mult                         3
% 4.16/0.99  --comb_sup_mult                         2
% 4.16/0.99  --comb_inst_mult                        10
% 4.16/0.99  
% 4.16/0.99  ------ Debug Options
% 4.16/0.99  
% 4.16/0.99  --dbg_backtrace                         false
% 4.16/0.99  --dbg_dump_prop_clauses                 false
% 4.16/0.99  --dbg_dump_prop_clauses_file            -
% 4.16/0.99  --dbg_out_stat                          false
% 4.16/0.99  ------ Parsing...
% 4.16/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 4.16/0.99  
% 4.16/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 4.16/0.99  
% 4.16/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 4.16/0.99  
% 4.16/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.16/0.99  ------ Proving...
% 4.16/0.99  ------ Problem Properties 
% 4.16/0.99  
% 4.16/0.99  
% 4.16/0.99  clauses                                 18
% 4.16/0.99  conjectures                             1
% 4.16/0.99  EPR                                     0
% 4.16/0.99  Horn                                    18
% 4.16/0.99  unary                                   6
% 4.16/0.99  binary                                  7
% 4.16/0.99  lits                                    36
% 4.16/0.99  lits eq                                 14
% 4.16/0.99  fd_pure                                 0
% 4.16/0.99  fd_pseudo                               0
% 4.16/0.99  fd_cond                                 0
% 4.16/0.99  fd_pseudo_cond                          0
% 4.16/0.99  AC symbols                              0
% 4.16/0.99  
% 4.16/0.99  ------ Schedule dynamic 5 is on 
% 4.16/0.99  
% 4.16/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 4.16/0.99  
% 4.16/0.99  
% 4.16/0.99  ------ 
% 4.16/0.99  Current options:
% 4.16/0.99  ------ 
% 4.16/0.99  
% 4.16/0.99  ------ Input Options
% 4.16/0.99  
% 4.16/0.99  --out_options                           all
% 4.16/0.99  --tptp_safe_out                         true
% 4.16/0.99  --problem_path                          ""
% 4.16/0.99  --include_path                          ""
% 4.16/0.99  --clausifier                            res/vclausify_rel
% 4.16/0.99  --clausifier_options                    ""
% 4.16/0.99  --stdin                                 false
% 4.16/0.99  --stats_out                             all
% 4.16/0.99  
% 4.16/0.99  ------ General Options
% 4.16/0.99  
% 4.16/0.99  --fof                                   false
% 4.16/0.99  --time_out_real                         305.
% 4.16/0.99  --time_out_virtual                      -1.
% 4.16/0.99  --symbol_type_check                     false
% 4.16/0.99  --clausify_out                          false
% 4.16/0.99  --sig_cnt_out                           false
% 4.16/0.99  --trig_cnt_out                          false
% 4.16/0.99  --trig_cnt_out_tolerance                1.
% 4.16/0.99  --trig_cnt_out_sk_spl                   false
% 4.16/0.99  --abstr_cl_out                          false
% 4.16/0.99  
% 4.16/0.99  ------ Global Options
% 4.16/0.99  
% 4.16/0.99  --schedule                              default
% 4.16/0.99  --add_important_lit                     false
% 4.16/0.99  --prop_solver_per_cl                    1000
% 4.16/0.99  --min_unsat_core                        false
% 4.16/0.99  --soft_assumptions                      false
% 4.16/0.99  --soft_lemma_size                       3
% 4.16/0.99  --prop_impl_unit_size                   0
% 4.16/0.99  --prop_impl_unit                        []
% 4.16/0.99  --share_sel_clauses                     true
% 4.16/0.99  --reset_solvers                         false
% 4.16/0.99  --bc_imp_inh                            [conj_cone]
% 4.16/0.99  --conj_cone_tolerance                   3.
% 4.16/0.99  --extra_neg_conj                        none
% 4.16/0.99  --large_theory_mode                     true
% 4.16/0.99  --prolific_symb_bound                   200
% 4.16/0.99  --lt_threshold                          2000
% 4.16/0.99  --clause_weak_htbl                      true
% 4.16/0.99  --gc_record_bc_elim                     false
% 4.16/0.99  
% 4.16/0.99  ------ Preprocessing Options
% 4.16/0.99  
% 4.16/0.99  --preprocessing_flag                    true
% 4.16/0.99  --time_out_prep_mult                    0.1
% 4.16/0.99  --splitting_mode                        input
% 4.16/0.99  --splitting_grd                         true
% 4.16/0.99  --splitting_cvd                         false
% 4.16/0.99  --splitting_cvd_svl                     false
% 4.16/0.99  --splitting_nvd                         32
% 4.16/0.99  --sub_typing                            true
% 4.16/0.99  --prep_gs_sim                           true
% 4.16/0.99  --prep_unflatten                        true
% 4.16/0.99  --prep_res_sim                          true
% 4.16/0.99  --prep_upred                            true
% 4.16/0.99  --prep_sem_filter                       exhaustive
% 4.16/0.99  --prep_sem_filter_out                   false
% 4.16/0.99  --pred_elim                             true
% 4.16/0.99  --res_sim_input                         true
% 4.16/0.99  --eq_ax_congr_red                       true
% 4.16/0.99  --pure_diseq_elim                       true
% 4.16/0.99  --brand_transform                       false
% 4.16/0.99  --non_eq_to_eq                          false
% 4.16/0.99  --prep_def_merge                        true
% 4.16/0.99  --prep_def_merge_prop_impl              false
% 4.16/0.99  --prep_def_merge_mbd                    true
% 4.16/0.99  --prep_def_merge_tr_red                 false
% 4.16/0.99  --prep_def_merge_tr_cl                  false
% 4.16/0.99  --smt_preprocessing                     true
% 4.16/0.99  --smt_ac_axioms                         fast
% 4.16/0.99  --preprocessed_out                      false
% 4.16/0.99  --preprocessed_stats                    false
% 4.16/0.99  
% 4.16/0.99  ------ Abstraction refinement Options
% 4.16/0.99  
% 4.16/0.99  --abstr_ref                             []
% 4.16/0.99  --abstr_ref_prep                        false
% 4.16/0.99  --abstr_ref_until_sat                   false
% 4.16/0.99  --abstr_ref_sig_restrict                funpre
% 4.16/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 4.16/0.99  --abstr_ref_under                       []
% 4.16/0.99  
% 4.16/0.99  ------ SAT Options
% 4.16/0.99  
% 4.16/0.99  --sat_mode                              false
% 4.16/0.99  --sat_fm_restart_options                ""
% 4.16/0.99  --sat_gr_def                            false
% 4.16/0.99  --sat_epr_types                         true
% 4.16/0.99  --sat_non_cyclic_types                  false
% 4.16/0.99  --sat_finite_models                     false
% 4.16/0.99  --sat_fm_lemmas                         false
% 4.16/0.99  --sat_fm_prep                           false
% 4.16/0.99  --sat_fm_uc_incr                        true
% 4.16/0.99  --sat_out_model                         small
% 4.16/0.99  --sat_out_clauses                       false
% 4.16/0.99  
% 4.16/0.99  ------ QBF Options
% 4.16/0.99  
% 4.16/0.99  --qbf_mode                              false
% 4.16/0.99  --qbf_elim_univ                         false
% 4.16/0.99  --qbf_dom_inst                          none
% 4.16/0.99  --qbf_dom_pre_inst                      false
% 4.16/0.99  --qbf_sk_in                             false
% 4.16/0.99  --qbf_pred_elim                         true
% 4.16/0.99  --qbf_split                             512
% 4.16/0.99  
% 4.16/0.99  ------ BMC1 Options
% 4.16/0.99  
% 4.16/0.99  --bmc1_incremental                      false
% 4.16/0.99  --bmc1_axioms                           reachable_all
% 4.16/0.99  --bmc1_min_bound                        0
% 4.16/0.99  --bmc1_max_bound                        -1
% 4.16/0.99  --bmc1_max_bound_default                -1
% 4.16/0.99  --bmc1_symbol_reachability              true
% 4.16/0.99  --bmc1_property_lemmas                  false
% 4.16/0.99  --bmc1_k_induction                      false
% 4.16/0.99  --bmc1_non_equiv_states                 false
% 4.16/0.99  --bmc1_deadlock                         false
% 4.16/0.99  --bmc1_ucm                              false
% 4.16/0.99  --bmc1_add_unsat_core                   none
% 4.16/0.99  --bmc1_unsat_core_children              false
% 4.16/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 4.16/0.99  --bmc1_out_stat                         full
% 4.16/0.99  --bmc1_ground_init                      false
% 4.16/0.99  --bmc1_pre_inst_next_state              false
% 4.16/0.99  --bmc1_pre_inst_state                   false
% 4.16/0.99  --bmc1_pre_inst_reach_state             false
% 4.16/0.99  --bmc1_out_unsat_core                   false
% 4.16/0.99  --bmc1_aig_witness_out                  false
% 4.16/0.99  --bmc1_verbose                          false
% 4.16/0.99  --bmc1_dump_clauses_tptp                false
% 4.16/0.99  --bmc1_dump_unsat_core_tptp             false
% 4.16/0.99  --bmc1_dump_file                        -
% 4.16/0.99  --bmc1_ucm_expand_uc_limit              128
% 4.16/0.99  --bmc1_ucm_n_expand_iterations          6
% 4.16/0.99  --bmc1_ucm_extend_mode                  1
% 4.16/0.99  --bmc1_ucm_init_mode                    2
% 4.16/0.99  --bmc1_ucm_cone_mode                    none
% 4.16/0.99  --bmc1_ucm_reduced_relation_type        0
% 4.16/0.99  --bmc1_ucm_relax_model                  4
% 4.16/0.99  --bmc1_ucm_full_tr_after_sat            true
% 4.16/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 4.16/0.99  --bmc1_ucm_layered_model                none
% 4.16/0.99  --bmc1_ucm_max_lemma_size               10
% 4.16/0.99  
% 4.16/0.99  ------ AIG Options
% 4.16/0.99  
% 4.16/0.99  --aig_mode                              false
% 4.16/0.99  
% 4.16/0.99  ------ Instantiation Options
% 4.16/0.99  
% 4.16/0.99  --instantiation_flag                    true
% 4.16/0.99  --inst_sos_flag                         true
% 4.16/0.99  --inst_sos_phase                        true
% 4.16/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.16/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.16/0.99  --inst_lit_sel_side                     none
% 4.16/0.99  --inst_solver_per_active                1400
% 4.16/0.99  --inst_solver_calls_frac                1.
% 4.16/0.99  --inst_passive_queue_type               priority_queues
% 4.16/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.16/0.99  --inst_passive_queues_freq              [25;2]
% 4.16/0.99  --inst_dismatching                      true
% 4.16/0.99  --inst_eager_unprocessed_to_passive     true
% 4.16/0.99  --inst_prop_sim_given                   true
% 4.16/0.99  --inst_prop_sim_new                     false
% 4.16/0.99  --inst_subs_new                         false
% 4.16/0.99  --inst_eq_res_simp                      false
% 4.16/0.99  --inst_subs_given                       false
% 4.16/0.99  --inst_orphan_elimination               true
% 4.16/0.99  --inst_learning_loop_flag               true
% 4.16/0.99  --inst_learning_start                   3000
% 4.16/0.99  --inst_learning_factor                  2
% 4.16/0.99  --inst_start_prop_sim_after_learn       3
% 4.16/0.99  --inst_sel_renew                        solver
% 4.16/0.99  --inst_lit_activity_flag                true
% 4.16/0.99  --inst_restr_to_given                   false
% 4.16/0.99  --inst_activity_threshold               500
% 4.16/0.99  --inst_out_proof                        true
% 4.16/0.99  
% 4.16/0.99  ------ Resolution Options
% 4.16/0.99  
% 4.16/0.99  --resolution_flag                       false
% 4.16/0.99  --res_lit_sel                           adaptive
% 4.16/0.99  --res_lit_sel_side                      none
% 4.16/0.99  --res_ordering                          kbo
% 4.16/0.99  --res_to_prop_solver                    active
% 4.16/0.99  --res_prop_simpl_new                    false
% 4.16/0.99  --res_prop_simpl_given                  true
% 4.16/0.99  --res_passive_queue_type                priority_queues
% 4.16/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.16/0.99  --res_passive_queues_freq               [15;5]
% 4.16/0.99  --res_forward_subs                      full
% 4.16/0.99  --res_backward_subs                     full
% 4.16/0.99  --res_forward_subs_resolution           true
% 4.16/0.99  --res_backward_subs_resolution          true
% 4.16/0.99  --res_orphan_elimination                true
% 4.16/0.99  --res_time_limit                        2.
% 4.16/0.99  --res_out_proof                         true
% 4.16/0.99  
% 4.16/0.99  ------ Superposition Options
% 4.16/0.99  
% 4.16/0.99  --superposition_flag                    true
% 4.16/0.99  --sup_passive_queue_type                priority_queues
% 4.16/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.16/0.99  --sup_passive_queues_freq               [8;1;4]
% 4.16/0.99  --demod_completeness_check              fast
% 4.16/0.99  --demod_use_ground                      true
% 4.16/0.99  --sup_to_prop_solver                    passive
% 4.16/0.99  --sup_prop_simpl_new                    true
% 4.16/0.99  --sup_prop_simpl_given                  true
% 4.16/0.99  --sup_fun_splitting                     true
% 4.16/0.99  --sup_smt_interval                      50000
% 4.16/0.99  
% 4.16/0.99  ------ Superposition Simplification Setup
% 4.16/0.99  
% 4.16/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 4.16/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 4.16/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 4.16/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 4.16/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 4.16/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 4.16/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 4.16/0.99  --sup_immed_triv                        [TrivRules]
% 4.16/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.16/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.16/0.99  --sup_immed_bw_main                     []
% 4.16/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 4.16/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 4.16/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.16/0.99  --sup_input_bw                          []
% 4.16/0.99  
% 4.16/0.99  ------ Combination Options
% 4.16/0.99  
% 4.16/0.99  --comb_res_mult                         3
% 4.16/0.99  --comb_sup_mult                         2
% 4.16/0.99  --comb_inst_mult                        10
% 4.16/0.99  
% 4.16/0.99  ------ Debug Options
% 4.16/0.99  
% 4.16/0.99  --dbg_backtrace                         false
% 4.16/0.99  --dbg_dump_prop_clauses                 false
% 4.16/0.99  --dbg_dump_prop_clauses_file            -
% 4.16/0.99  --dbg_out_stat                          false
% 4.16/0.99  
% 4.16/0.99  
% 4.16/0.99  
% 4.16/0.99  
% 4.16/0.99  ------ Proving...
% 4.16/0.99  
% 4.16/0.99  
% 4.16/0.99  % SZS status Theorem for theBenchmark.p
% 4.16/0.99  
% 4.16/0.99   Resolution empty clause
% 4.16/0.99  
% 4.16/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 4.16/0.99  
% 4.16/0.99  fof(f5,axiom,(
% 4.16/0.99    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 4.16/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.16/0.99  
% 4.16/0.99  fof(f42,plain,(
% 4.16/0.99    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 4.16/0.99    inference(cnf_transformation,[],[f5])).
% 4.16/0.99  
% 4.16/0.99  fof(f17,axiom,(
% 4.16/0.99    ! [X0,X1] : (v1_relat_1(X1) => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)))),
% 4.16/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.16/0.99  
% 4.16/0.99  fof(f32,plain,(
% 4.16/0.99    ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 4.16/0.99    inference(ennf_transformation,[],[f17])).
% 4.16/0.99  
% 4.16/0.99  fof(f55,plain,(
% 4.16/0.99    ( ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 4.16/0.99    inference(cnf_transformation,[],[f32])).
% 4.16/0.99  
% 4.16/0.99  fof(f4,axiom,(
% 4.16/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 4.16/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.16/0.99  
% 4.16/0.99  fof(f41,plain,(
% 4.16/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 4.16/0.99    inference(cnf_transformation,[],[f4])).
% 4.16/0.99  
% 4.16/0.99  fof(f2,axiom,(
% 4.16/0.99    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 4.16/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.16/0.99  
% 4.16/0.99  fof(f39,plain,(
% 4.16/0.99    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 4.16/0.99    inference(cnf_transformation,[],[f2])).
% 4.16/0.99  
% 4.16/0.99  fof(f3,axiom,(
% 4.16/0.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 4.16/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.16/0.99  
% 4.16/0.99  fof(f40,plain,(
% 4.16/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 4.16/0.99    inference(cnf_transformation,[],[f3])).
% 4.16/0.99  
% 4.16/0.99  fof(f59,plain,(
% 4.16/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 4.16/0.99    inference(definition_unfolding,[],[f39,f40])).
% 4.16/0.99  
% 4.16/0.99  fof(f60,plain,(
% 4.16/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 4.16/0.99    inference(definition_unfolding,[],[f41,f59])).
% 4.16/0.99  
% 4.16/0.99  fof(f64,plain,(
% 4.16/0.99    ( ! [X0,X1] : (k1_setfam_1(k2_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X0)) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 4.16/0.99    inference(definition_unfolding,[],[f55,f60])).
% 4.16/0.99  
% 4.16/0.99  fof(f13,axiom,(
% 4.16/0.99    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 4.16/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.16/0.99  
% 4.16/0.99  fof(f50,plain,(
% 4.16/0.99    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 4.16/0.99    inference(cnf_transformation,[],[f13])).
% 4.16/0.99  
% 4.16/0.99  fof(f1,axiom,(
% 4.16/0.99    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 4.16/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.16/0.99  
% 4.16/0.99  fof(f38,plain,(
% 4.16/0.99    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 4.16/0.99    inference(cnf_transformation,[],[f1])).
% 4.16/0.99  
% 4.16/0.99  fof(f61,plain,(
% 4.16/0.99    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0)) )),
% 4.16/0.99    inference(definition_unfolding,[],[f38,f60])).
% 4.16/0.99  
% 4.16/0.99  fof(f51,plain,(
% 4.16/0.99    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 4.16/0.99    inference(cnf_transformation,[],[f13])).
% 4.16/0.99  
% 4.16/0.99  fof(f15,axiom,(
% 4.16/0.99    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 4.16/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.16/0.99  
% 4.16/0.99  fof(f29,plain,(
% 4.16/0.99    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 4.16/0.99    inference(ennf_transformation,[],[f15])).
% 4.16/0.99  
% 4.16/0.99  fof(f30,plain,(
% 4.16/0.99    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 4.16/0.99    inference(flattening,[],[f29])).
% 4.16/0.99  
% 4.16/0.99  fof(f53,plain,(
% 4.16/0.99    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 4.16/0.99    inference(cnf_transformation,[],[f30])).
% 4.16/0.99  
% 4.16/0.99  fof(f18,axiom,(
% 4.16/0.99    ! [X0,X1] : (v1_relat_1(X1) => k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0))),
% 4.16/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.16/0.99  
% 4.16/0.99  fof(f33,plain,(
% 4.16/0.99    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 4.16/0.99    inference(ennf_transformation,[],[f18])).
% 4.16/0.99  
% 4.16/0.99  fof(f56,plain,(
% 4.16/0.99    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 4.16/0.99    inference(cnf_transformation,[],[f33])).
% 4.16/0.99  
% 4.16/0.99  fof(f9,axiom,(
% 4.16/0.99    ! [X0,X1] : (v1_relat_1(X1) => k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0)) = k8_relat_1(X0,X1))),
% 4.16/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.16/0.99  
% 4.16/0.99  fof(f25,plain,(
% 4.16/0.99    ! [X0,X1] : (k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0)) = k8_relat_1(X0,X1) | ~v1_relat_1(X1))),
% 4.16/0.99    inference(ennf_transformation,[],[f9])).
% 4.16/0.99  
% 4.16/0.99  fof(f46,plain,(
% 4.16/0.99    ( ! [X0,X1] : (k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0)) = k8_relat_1(X0,X1) | ~v1_relat_1(X1)) )),
% 4.16/0.99    inference(cnf_transformation,[],[f25])).
% 4.16/0.99  
% 4.16/0.99  fof(f63,plain,(
% 4.16/0.99    ( ! [X0,X1] : (k1_setfam_1(k2_enumset1(X1,X1,X1,k2_zfmisc_1(k1_relat_1(X1),X0))) = k8_relat_1(X0,X1) | ~v1_relat_1(X1)) )),
% 4.16/0.99    inference(definition_unfolding,[],[f46,f60])).
% 4.16/0.99  
% 4.16/0.99  fof(f8,axiom,(
% 4.16/0.99    ! [X0,X1] : (v1_relat_1(X1) => k5_relat_1(X1,k6_relat_1(X0)) = k8_relat_1(X0,X1))),
% 4.16/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.16/0.99  
% 4.16/0.99  fof(f24,plain,(
% 4.16/0.99    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = k8_relat_1(X0,X1) | ~v1_relat_1(X1))),
% 4.16/0.99    inference(ennf_transformation,[],[f8])).
% 4.16/0.99  
% 4.16/0.99  fof(f45,plain,(
% 4.16/0.99    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = k8_relat_1(X0,X1) | ~v1_relat_1(X1)) )),
% 4.16/0.99    inference(cnf_transformation,[],[f24])).
% 4.16/0.99  
% 4.16/0.99  fof(f6,axiom,(
% 4.16/0.99    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k3_xboole_0(X0,X1)))),
% 4.16/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.16/0.99  
% 4.16/0.99  fof(f22,plain,(
% 4.16/0.99    ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 4.16/0.99    inference(ennf_transformation,[],[f6])).
% 4.16/0.99  
% 4.16/0.99  fof(f43,plain,(
% 4.16/0.99    ( ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0)) )),
% 4.16/0.99    inference(cnf_transformation,[],[f22])).
% 4.16/0.99  
% 4.16/0.99  fof(f62,plain,(
% 4.16/0.99    ( ! [X0,X1] : (v1_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) | ~v1_relat_1(X0)) )),
% 4.16/0.99    inference(definition_unfolding,[],[f43,f60])).
% 4.16/0.99  
% 4.16/0.99  fof(f19,axiom,(
% 4.16/0.99    ! [X0] : (v1_relat_1(X0) => k7_relat_1(X0,k1_relat_1(X0)) = X0)),
% 4.16/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.16/0.99  
% 4.16/0.99  fof(f34,plain,(
% 4.16/0.99    ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 4.16/0.99    inference(ennf_transformation,[],[f19])).
% 4.16/0.99  
% 4.16/0.99  fof(f57,plain,(
% 4.16/0.99    ( ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0)) )),
% 4.16/0.99    inference(cnf_transformation,[],[f34])).
% 4.16/0.99  
% 4.16/0.99  fof(f11,axiom,(
% 4.16/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,X1))))),
% 4.16/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.16/0.99  
% 4.16/0.99  fof(f27,plain,(
% 4.16/0.99    ! [X0] : (! [X1] : (k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 4.16/0.99    inference(ennf_transformation,[],[f11])).
% 4.16/0.99  
% 4.16/0.99  fof(f48,plain,(
% 4.16/0.99    ( ! [X0,X1] : (k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 4.16/0.99    inference(cnf_transformation,[],[f27])).
% 4.16/0.99  
% 4.16/0.99  fof(f14,axiom,(
% 4.16/0.99    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))),
% 4.16/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.16/0.99  
% 4.16/0.99  fof(f52,plain,(
% 4.16/0.99    ( ! [X0] : (k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))) )),
% 4.16/0.99    inference(cnf_transformation,[],[f14])).
% 4.16/0.99  
% 4.16/0.99  fof(f7,axiom,(
% 4.16/0.99    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k7_relat_1(X1,X0),X2) = k7_relat_1(k5_relat_1(X1,X2),X0)))),
% 4.16/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.16/0.99  
% 4.16/0.99  fof(f23,plain,(
% 4.16/0.99    ! [X0,X1] : (! [X2] : (k5_relat_1(k7_relat_1(X1,X0),X2) = k7_relat_1(k5_relat_1(X1,X2),X0) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 4.16/0.99    inference(ennf_transformation,[],[f7])).
% 4.16/0.99  
% 4.16/0.99  fof(f44,plain,(
% 4.16/0.99    ( ! [X2,X0,X1] : (k5_relat_1(k7_relat_1(X1,X0),X2) = k7_relat_1(k5_relat_1(X1,X2),X0) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 4.16/0.99    inference(cnf_transformation,[],[f23])).
% 4.16/0.99  
% 4.16/0.99  fof(f10,axiom,(
% 4.16/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 4.16/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.16/0.99  
% 4.16/0.99  fof(f26,plain,(
% 4.16/0.99    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 4.16/0.99    inference(ennf_transformation,[],[f10])).
% 4.16/0.99  
% 4.16/0.99  fof(f47,plain,(
% 4.16/0.99    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 4.16/0.99    inference(cnf_transformation,[],[f26])).
% 4.16/0.99  
% 4.16/0.99  fof(f16,axiom,(
% 4.16/0.99    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 4.16/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.16/0.99  
% 4.16/0.99  fof(f31,plain,(
% 4.16/0.99    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 4.16/0.99    inference(ennf_transformation,[],[f16])).
% 4.16/0.99  
% 4.16/0.99  fof(f54,plain,(
% 4.16/0.99    ( ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 4.16/0.99    inference(cnf_transformation,[],[f31])).
% 4.16/0.99  
% 4.16/0.99  fof(f20,conjecture,(
% 4.16/0.99    ! [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))),
% 4.16/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.16/0.99  
% 4.16/0.99  fof(f21,negated_conjecture,(
% 4.16/0.99    ~! [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))),
% 4.16/0.99    inference(negated_conjecture,[],[f20])).
% 4.16/0.99  
% 4.16/0.99  fof(f35,plain,(
% 4.16/0.99    ? [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) != k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))),
% 4.16/0.99    inference(ennf_transformation,[],[f21])).
% 4.16/0.99  
% 4.16/0.99  fof(f36,plain,(
% 4.16/0.99    ? [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) != k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) => k6_relat_1(k3_xboole_0(sK0,sK1)) != k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0))),
% 4.16/0.99    introduced(choice_axiom,[])).
% 4.16/0.99  
% 4.16/0.99  fof(f37,plain,(
% 4.16/0.99    k6_relat_1(k3_xboole_0(sK0,sK1)) != k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0))),
% 4.16/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f35,f36])).
% 4.16/0.99  
% 4.16/0.99  fof(f58,plain,(
% 4.16/0.99    k6_relat_1(k3_xboole_0(sK0,sK1)) != k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0))),
% 4.16/0.99    inference(cnf_transformation,[],[f37])).
% 4.16/0.99  
% 4.16/0.99  fof(f65,plain,(
% 4.16/0.99    k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) != k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0))),
% 4.16/0.99    inference(definition_unfolding,[],[f58,f60])).
% 4.16/0.99  
% 4.16/0.99  cnf(c_1,plain,
% 4.16/0.99      ( v1_relat_1(k6_relat_1(X0)) ),
% 4.16/0.99      inference(cnf_transformation,[],[f42]) ).
% 4.16/0.99  
% 4.16/0.99  cnf(c_483,plain,
% 4.16/0.99      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 4.16/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 4.16/0.99  
% 4.16/0.99  cnf(c_14,plain,
% 4.16/0.99      ( ~ v1_relat_1(X0)
% 4.16/0.99      | k1_setfam_1(k2_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1)) ),
% 4.16/0.99      inference(cnf_transformation,[],[f64]) ).
% 4.16/0.99  
% 4.16/0.99  cnf(c_473,plain,
% 4.16/0.99      ( k1_setfam_1(k2_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1))
% 4.16/0.99      | v1_relat_1(X0) != iProver_top ),
% 4.16/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 4.16/0.99  
% 4.16/0.99  cnf(c_714,plain,
% 4.16/0.99      ( k1_setfam_1(k2_enumset1(k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
% 4.16/0.99      inference(superposition,[status(thm)],[c_483,c_473]) ).
% 4.16/0.99  
% 4.16/0.99  cnf(c_10,plain,
% 4.16/0.99      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 4.16/0.99      inference(cnf_transformation,[],[f50]) ).
% 4.16/0.99  
% 4.16/0.99  cnf(c_715,plain,
% 4.16/0.99      ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
% 4.16/0.99      inference(light_normalisation,[status(thm)],[c_714,c_10]) ).
% 4.16/0.99  
% 4.16/0.99  cnf(c_0,plain,
% 4.16/0.99      ( r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0) ),
% 4.16/0.99      inference(cnf_transformation,[],[f61]) ).
% 4.16/0.99  
% 4.16/0.99  cnf(c_484,plain,
% 4.16/0.99      ( r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0) = iProver_top ),
% 4.16/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 4.16/0.99  
% 4.16/0.99  cnf(c_717,plain,
% 4.16/0.99      ( r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X0) = iProver_top ),
% 4.16/0.99      inference(demodulation,[status(thm)],[c_715,c_484]) ).
% 4.16/0.99  
% 4.16/0.99  cnf(c_9,plain,
% 4.16/0.99      ( k2_relat_1(k6_relat_1(X0)) = X0 ),
% 4.16/0.99      inference(cnf_transformation,[],[f51]) ).
% 4.16/0.99  
% 4.16/0.99  cnf(c_12,plain,
% 4.16/0.99      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 4.16/0.99      | ~ v1_relat_1(X0)
% 4.16/0.99      | k5_relat_1(X0,k6_relat_1(X1)) = X0 ),
% 4.16/0.99      inference(cnf_transformation,[],[f53]) ).
% 4.16/0.99  
% 4.16/0.99  cnf(c_475,plain,
% 4.16/0.99      ( k5_relat_1(X0,k6_relat_1(X1)) = X0
% 4.16/0.99      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 4.16/0.99      | v1_relat_1(X0) != iProver_top ),
% 4.16/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 4.16/0.99  
% 4.16/0.99  cnf(c_1036,plain,
% 4.16/0.99      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k6_relat_1(X0)
% 4.16/0.99      | r1_tarski(X0,X1) != iProver_top
% 4.16/0.99      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 4.16/0.99      inference(superposition,[status(thm)],[c_9,c_475]) ).
% 4.16/0.99  
% 4.16/0.99  cnf(c_15,plain,
% 4.16/0.99      ( ~ v1_relat_1(X0) | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
% 4.16/0.99      inference(cnf_transformation,[],[f56]) ).
% 4.16/0.99  
% 4.16/0.99  cnf(c_472,plain,
% 4.16/0.99      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
% 4.16/0.99      | v1_relat_1(X1) != iProver_top ),
% 4.16/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 4.16/0.99  
% 4.16/0.99  cnf(c_850,plain,
% 4.16/0.99      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
% 4.16/0.99      inference(superposition,[status(thm)],[c_483,c_472]) ).
% 4.16/0.99  
% 4.16/0.99  cnf(c_1037,plain,
% 4.16/0.99      ( k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X1)
% 4.16/0.99      | r1_tarski(X1,X0) != iProver_top
% 4.16/0.99      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 4.16/0.99      inference(demodulation,[status(thm)],[c_1036,c_850]) ).
% 4.16/0.99  
% 4.16/0.99  cnf(c_1441,plain,
% 4.16/0.99      ( k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)))
% 4.16/0.99      | v1_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)))) != iProver_top ),
% 4.16/0.99      inference(superposition,[status(thm)],[c_717,c_1037]) ).
% 4.16/0.99  
% 4.16/0.99  cnf(c_8483,plain,
% 4.16/0.99      ( k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
% 4.16/0.99      inference(superposition,[status(thm)],[c_483,c_1441]) ).
% 4.16/0.99  
% 4.16/0.99  cnf(c_5,plain,
% 4.16/0.99      ( ~ v1_relat_1(X0)
% 4.16/0.99      | k1_setfam_1(k2_enumset1(X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),X1))) = k8_relat_1(X1,X0) ),
% 4.16/0.99      inference(cnf_transformation,[],[f63]) ).
% 4.16/0.99  
% 4.16/0.99  cnf(c_479,plain,
% 4.16/0.99      ( k1_setfam_1(k2_enumset1(X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),X1))) = k8_relat_1(X1,X0)
% 4.16/0.99      | v1_relat_1(X0) != iProver_top ),
% 4.16/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 4.16/0.99  
% 4.16/0.99  cnf(c_1076,plain,
% 4.16/0.99      ( k1_relat_1(k7_relat_1(k6_relat_1(X0),k2_zfmisc_1(k1_relat_1(X0),X1))) = k8_relat_1(X1,X0)
% 4.16/0.99      | v1_relat_1(X0) != iProver_top ),
% 4.16/0.99      inference(demodulation,[status(thm)],[c_479,c_715]) ).
% 4.16/0.99  
% 4.16/0.99  cnf(c_1080,plain,
% 4.16/0.99      ( k1_relat_1(k7_relat_1(k6_relat_1(k6_relat_1(X0)),k2_zfmisc_1(k1_relat_1(k6_relat_1(X0)),X1))) = k8_relat_1(X1,k6_relat_1(X0)) ),
% 4.16/0.99      inference(superposition,[status(thm)],[c_483,c_1076]) ).
% 4.16/0.99  
% 4.16/0.99  cnf(c_1082,plain,
% 4.16/0.99      ( k1_relat_1(k7_relat_1(k6_relat_1(k6_relat_1(X0)),k2_zfmisc_1(X0,X1))) = k8_relat_1(X1,k6_relat_1(X0)) ),
% 4.16/0.99      inference(light_normalisation,[status(thm)],[c_1080,c_10]) ).
% 4.16/0.99  
% 4.16/0.99  cnf(c_4,plain,
% 4.16/0.99      ( ~ v1_relat_1(X0) | k5_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X1,X0) ),
% 4.16/0.99      inference(cnf_transformation,[],[f45]) ).
% 4.16/0.99  
% 4.16/0.99  cnf(c_480,plain,
% 4.16/0.99      ( k5_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X1,X0)
% 4.16/0.99      | v1_relat_1(X0) != iProver_top ),
% 4.16/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 4.16/0.99  
% 4.16/0.99  cnf(c_933,plain,
% 4.16/0.99      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k8_relat_1(X1,k6_relat_1(X0)) ),
% 4.16/0.99      inference(superposition,[status(thm)],[c_483,c_480]) ).
% 4.16/0.99  
% 4.16/0.99  cnf(c_934,plain,
% 4.16/0.99      ( k8_relat_1(X0,k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X0),X1) ),
% 4.16/0.99      inference(light_normalisation,[status(thm)],[c_933,c_850]) ).
% 4.16/0.99  
% 4.16/0.99  cnf(c_1083,plain,
% 4.16/0.99      ( k1_relat_1(k7_relat_1(k6_relat_1(k6_relat_1(X0)),k2_zfmisc_1(X0,X1))) = k7_relat_1(k6_relat_1(X1),X0) ),
% 4.16/0.99      inference(demodulation,[status(thm)],[c_1082,c_934]) ).
% 4.16/0.99  
% 4.16/0.99  cnf(c_2,plain,
% 4.16/0.99      ( ~ v1_relat_1(X0) | v1_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) ),
% 4.16/0.99      inference(cnf_transformation,[],[f62]) ).
% 4.16/0.99  
% 4.16/0.99  cnf(c_482,plain,
% 4.16/0.99      ( v1_relat_1(X0) != iProver_top
% 4.16/0.99      | v1_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) = iProver_top ),
% 4.16/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 4.16/0.99  
% 4.16/0.99  cnf(c_1012,plain,
% 4.16/0.99      ( v1_relat_1(X0) != iProver_top
% 4.16/0.99      | v1_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = iProver_top ),
% 4.16/0.99      inference(light_normalisation,[status(thm)],[c_482,c_715]) ).
% 4.16/0.99  
% 4.16/0.99  cnf(c_1251,plain,
% 4.16/0.99      ( v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = iProver_top
% 4.16/0.99      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 4.16/0.99      inference(superposition,[status(thm)],[c_1083,c_1012]) ).
% 4.16/0.99  
% 4.16/0.99  cnf(c_16,plain,
% 4.16/0.99      ( ~ v1_relat_1(X0) | k7_relat_1(X0,k1_relat_1(X0)) = X0 ),
% 4.16/0.99      inference(cnf_transformation,[],[f57]) ).
% 4.16/0.99  
% 4.16/0.99  cnf(c_471,plain,
% 4.16/0.99      ( k7_relat_1(X0,k1_relat_1(X0)) = X0 | v1_relat_1(X0) != iProver_top ),
% 4.16/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 4.16/0.99  
% 4.16/0.99  cnf(c_1315,plain,
% 4.16/0.99      ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k7_relat_1(k6_relat_1(X0),X1)
% 4.16/0.99      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 4.16/0.99      inference(superposition,[status(thm)],[c_1251,c_471]) ).
% 4.16/0.99  
% 4.16/0.99  cnf(c_2250,plain,
% 4.16/0.99      ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k7_relat_1(k6_relat_1(X0),X1) ),
% 4.16/0.99      inference(superposition,[status(thm)],[c_483,c_1315]) ).
% 4.16/0.99  
% 4.16/0.99  cnf(c_7,plain,
% 4.16/0.99      ( ~ v1_relat_1(X0)
% 4.16/0.99      | ~ v1_relat_1(X1)
% 4.16/0.99      | k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,X1)) ),
% 4.16/0.99      inference(cnf_transformation,[],[f48]) ).
% 4.16/0.99  
% 4.16/0.99  cnf(c_477,plain,
% 4.16/0.99      ( k5_relat_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k5_relat_1(X1,X0))
% 4.16/0.99      | v1_relat_1(X1) != iProver_top
% 4.16/0.99      | v1_relat_1(X0) != iProver_top ),
% 4.16/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 4.16/0.99  
% 4.16/0.99  cnf(c_1173,plain,
% 4.16/0.99      ( k5_relat_1(k4_relat_1(k6_relat_1(X0)),k4_relat_1(X1)) = k4_relat_1(k5_relat_1(X1,k6_relat_1(X0)))
% 4.16/0.99      | v1_relat_1(X1) != iProver_top ),
% 4.16/0.99      inference(superposition,[status(thm)],[c_483,c_477]) ).
% 4.16/0.99  
% 4.16/0.99  cnf(c_11,plain,
% 4.16/0.99      ( k4_relat_1(k6_relat_1(X0)) = k6_relat_1(X0) ),
% 4.16/0.99      inference(cnf_transformation,[],[f52]) ).
% 4.16/0.99  
% 4.16/0.99  cnf(c_1175,plain,
% 4.16/0.99      ( k4_relat_1(k5_relat_1(X0,k6_relat_1(X1))) = k5_relat_1(k6_relat_1(X1),k4_relat_1(X0))
% 4.16/0.99      | v1_relat_1(X0) != iProver_top ),
% 4.16/0.99      inference(light_normalisation,[status(thm)],[c_1173,c_11]) ).
% 4.16/0.99  
% 4.16/0.99  cnf(c_1310,plain,
% 4.16/0.99      ( k4_relat_1(k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X2))) = k5_relat_1(k6_relat_1(X2),k4_relat_1(k7_relat_1(k6_relat_1(X0),X1)))
% 4.16/0.99      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 4.16/0.99      inference(superposition,[status(thm)],[c_1251,c_1175]) ).
% 4.16/0.99  
% 4.16/0.99  cnf(c_1183,plain,
% 4.16/0.99      ( k4_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k5_relat_1(k6_relat_1(X1),k4_relat_1(k6_relat_1(X0))) ),
% 4.16/0.99      inference(superposition,[status(thm)],[c_483,c_1175]) ).
% 4.16/0.99  
% 4.16/0.99  cnf(c_1185,plain,
% 4.16/0.99      ( k4_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) ),
% 4.16/0.99      inference(light_normalisation,[status(thm)],[c_1183,c_11,c_850]) ).
% 4.16/0.99  
% 4.16/0.99  cnf(c_1186,plain,
% 4.16/0.99      ( k4_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
% 4.16/0.99      inference(demodulation,[status(thm)],[c_1185,c_850]) ).
% 4.16/0.99  
% 4.16/0.99  cnf(c_1318,plain,
% 4.16/0.99      ( k4_relat_1(k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X2))) = k5_relat_1(k6_relat_1(X2),k7_relat_1(k6_relat_1(X1),X0))
% 4.16/0.99      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 4.16/0.99      inference(light_normalisation,[status(thm)],[c_1310,c_1186]) ).
% 4.16/0.99  
% 4.16/0.99  cnf(c_3,plain,
% 4.16/0.99      ( ~ v1_relat_1(X0)
% 4.16/0.99      | ~ v1_relat_1(X1)
% 4.16/0.99      | k5_relat_1(k7_relat_1(X1,X2),X0) = k7_relat_1(k5_relat_1(X1,X0),X2) ),
% 4.16/0.99      inference(cnf_transformation,[],[f44]) ).
% 4.16/0.99  
% 4.16/0.99  cnf(c_481,plain,
% 4.16/0.99      ( k5_relat_1(k7_relat_1(X0,X1),X2) = k7_relat_1(k5_relat_1(X0,X2),X1)
% 4.16/0.99      | v1_relat_1(X2) != iProver_top
% 4.16/0.99      | v1_relat_1(X0) != iProver_top ),
% 4.16/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 4.16/0.99  
% 4.16/0.99  cnf(c_1556,plain,
% 4.16/0.99      ( k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) = k7_relat_1(k5_relat_1(k6_relat_1(X0),X2),X1)
% 4.16/0.99      | v1_relat_1(X2) != iProver_top ),
% 4.16/0.99      inference(superposition,[status(thm)],[c_483,c_481]) ).
% 4.16/0.99  
% 4.16/0.99  cnf(c_1742,plain,
% 4.16/0.99      ( k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X2)) = k7_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X2)),X1) ),
% 4.16/0.99      inference(superposition,[status(thm)],[c_483,c_1556]) ).
% 4.16/0.99  
% 4.16/0.99  cnf(c_1313,plain,
% 4.16/0.99      ( k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X2)) = k8_relat_1(X2,k7_relat_1(k6_relat_1(X0),X1))
% 4.16/0.99      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 4.16/0.99      inference(superposition,[status(thm)],[c_1251,c_480]) ).
% 4.16/0.99  
% 4.16/0.99  cnf(c_1480,plain,
% 4.16/0.99      ( k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X2)) = k8_relat_1(X2,k7_relat_1(k6_relat_1(X0),X1)) ),
% 4.16/0.99      inference(superposition,[status(thm)],[c_483,c_1313]) ).
% 4.16/0.99  
% 4.16/0.99  cnf(c_1745,plain,
% 4.16/0.99      ( k7_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),X2) = k8_relat_1(X1,k7_relat_1(k6_relat_1(X0),X2)) ),
% 4.16/0.99      inference(light_normalisation,[status(thm)],[c_1742,c_1480]) ).
% 4.16/0.99  
% 4.16/0.99  cnf(c_1746,plain,
% 4.16/0.99      ( k8_relat_1(X0,k7_relat_1(k6_relat_1(X1),X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) ),
% 4.16/0.99      inference(demodulation,[status(thm)],[c_1745,c_850]) ).
% 4.16/0.99  
% 4.16/0.99  cnf(c_1819,plain,
% 4.16/0.99      ( k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X0),X1) ),
% 4.16/0.99      inference(demodulation,[status(thm)],[c_1746,c_1480]) ).
% 4.16/0.99  
% 4.16/0.99  cnf(c_2801,plain,
% 4.16/0.99      ( k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)) = k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X2),X1))
% 4.16/0.99      | v1_relat_1(k6_relat_1(X2)) != iProver_top ),
% 4.16/0.99      inference(light_normalisation,[status(thm)],[c_1318,c_1819]) ).
% 4.16/0.99  
% 4.16/0.99  cnf(c_1316,plain,
% 4.16/0.99      ( k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X1),X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X0)
% 4.16/0.99      | v1_relat_1(k6_relat_1(X2)) != iProver_top ),
% 4.16/0.99      inference(superposition,[status(thm)],[c_1251,c_472]) ).
% 4.16/0.99  
% 4.16/0.99  cnf(c_1919,plain,
% 4.16/0.99      ( k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X1),X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X0) ),
% 4.16/0.99      inference(superposition,[status(thm)],[c_483,c_1316]) ).
% 4.16/0.99  
% 4.16/0.99  cnf(c_2802,plain,
% 4.16/0.99      ( k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X1),X0)
% 4.16/0.99      | v1_relat_1(k6_relat_1(X2)) != iProver_top ),
% 4.16/0.99      inference(demodulation,[status(thm)],[c_2801,c_1919]) ).
% 4.16/0.99  
% 4.16/0.99  cnf(c_2806,plain,
% 4.16/0.99      ( k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X1),X0) ),
% 4.16/0.99      inference(superposition,[status(thm)],[c_483,c_2802]) ).
% 4.16/0.99  
% 4.16/0.99  cnf(c_2856,plain,
% 4.16/0.99      ( k7_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X1),X0) = k4_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
% 4.16/0.99      inference(superposition,[status(thm)],[c_2250,c_2806]) ).
% 4.16/0.99  
% 4.16/0.99  cnf(c_2867,plain,
% 4.16/0.99      ( k7_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X1),X0) = k7_relat_1(k6_relat_1(X1),X0) ),
% 4.16/0.99      inference(light_normalisation,[status(thm)],[c_2856,c_1186]) ).
% 4.16/0.99  
% 4.16/0.99  cnf(c_1558,plain,
% 4.16/0.99      ( k5_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2),X3) = k7_relat_1(k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),X3),X2)
% 4.16/0.99      | v1_relat_1(X3) != iProver_top
% 4.16/0.99      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 4.16/0.99      inference(superposition,[status(thm)],[c_1251,c_481]) ).
% 4.16/0.99  
% 4.16/0.99  cnf(c_4663,plain,
% 4.16/0.99      ( k5_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2),X3) = k7_relat_1(k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),X3),X2)
% 4.16/0.99      | v1_relat_1(X3) != iProver_top ),
% 4.16/0.99      inference(superposition,[status(thm)],[c_483,c_1558]) ).
% 4.16/0.99  
% 4.16/0.99  cnf(c_4699,plain,
% 4.16/0.99      ( k5_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2),k6_relat_1(X3)) = k7_relat_1(k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X3)),X2) ),
% 4.16/0.99      inference(superposition,[status(thm)],[c_483,c_4663]) ).
% 4.16/0.99  
% 4.16/0.99  cnf(c_4702,plain,
% 4.16/0.99      ( k5_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2),k6_relat_1(X3)) = k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X3),X0),X1),X2) ),
% 4.16/0.99      inference(demodulation,[status(thm)],[c_4699,c_1819]) ).
% 4.16/0.99  
% 4.16/0.99  cnf(c_4855,plain,
% 4.16/0.99      ( k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(k6_relat_1(X1),X2))),X2),X1) = k5_relat_1(k7_relat_1(k6_relat_1(X2),X1),k6_relat_1(X0)) ),
% 4.16/0.99      inference(superposition,[status(thm)],[c_2867,c_4702]) ).
% 4.16/0.99  
% 4.16/0.99  cnf(c_4874,plain,
% 4.16/0.99      ( k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(k6_relat_1(X1),X2))),X2),X1) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X2),X1) ),
% 4.16/0.99      inference(demodulation,[status(thm)],[c_4855,c_1819]) ).
% 4.16/0.99  
% 4.16/0.99  cnf(c_8883,plain,
% 4.16/0.99      ( k7_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X1),X0) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0) ),
% 4.16/0.99      inference(superposition,[status(thm)],[c_8483,c_4874]) ).
% 4.16/0.99  
% 4.16/0.99  cnf(c_8890,plain,
% 4.16/0.99      ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0) = k7_relat_1(k6_relat_1(X1),X0) ),
% 4.16/0.99      inference(light_normalisation,[status(thm)],[c_8883,c_2867]) ).
% 4.16/0.99  
% 4.16/0.99  cnf(c_9134,plain,
% 4.16/0.99      ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0) = k4_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
% 4.16/0.99      inference(superposition,[status(thm)],[c_8890,c_2806]) ).
% 4.16/0.99  
% 4.16/0.99  cnf(c_9146,plain,
% 4.16/0.99      ( k4_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k7_relat_1(k6_relat_1(X0),X1) ),
% 4.16/0.99      inference(demodulation,[status(thm)],[c_9134,c_8890]) ).
% 4.16/0.99  
% 4.16/0.99  cnf(c_9169,plain,
% 4.16/0.99      ( k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X1),X0) ),
% 4.16/0.99      inference(superposition,[status(thm)],[c_9146,c_1186]) ).
% 4.16/0.99  
% 4.16/0.99  cnf(c_6,plain,
% 4.16/0.99      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
% 4.16/0.99      | ~ v1_relat_1(X0)
% 4.16/0.99      | ~ v1_relat_1(X1) ),
% 4.16/0.99      inference(cnf_transformation,[],[f47]) ).
% 4.16/0.99  
% 4.16/0.99  cnf(c_478,plain,
% 4.16/0.99      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) = iProver_top
% 4.16/0.99      | v1_relat_1(X0) != iProver_top
% 4.16/0.99      | v1_relat_1(X1) != iProver_top ),
% 4.16/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 4.16/0.99  
% 4.16/0.99  cnf(c_1440,plain,
% 4.16/0.99      ( k7_relat_1(k6_relat_1(k2_relat_1(X0)),k2_relat_1(k5_relat_1(X1,X0))) = k6_relat_1(k2_relat_1(k5_relat_1(X1,X0)))
% 4.16/0.99      | v1_relat_1(X1) != iProver_top
% 4.16/0.99      | v1_relat_1(X0) != iProver_top
% 4.16/0.99      | v1_relat_1(k6_relat_1(k2_relat_1(k5_relat_1(X1,X0)))) != iProver_top ),
% 4.16/0.99      inference(superposition,[status(thm)],[c_478,c_1037]) ).
% 4.16/0.99  
% 4.16/0.99  cnf(c_6813,plain,
% 4.16/0.99      ( k7_relat_1(k6_relat_1(k2_relat_1(X0)),k2_relat_1(k5_relat_1(X1,X0))) = k6_relat_1(k2_relat_1(k5_relat_1(X1,X0)))
% 4.16/0.99      | v1_relat_1(X0) != iProver_top
% 4.16/0.99      | v1_relat_1(X1) != iProver_top ),
% 4.16/0.99      inference(superposition,[status(thm)],[c_483,c_1440]) ).
% 4.16/0.99  
% 4.16/0.99  cnf(c_6936,plain,
% 4.16/0.99      ( k7_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(X0))),k2_relat_1(k5_relat_1(X1,k6_relat_1(X0)))) = k6_relat_1(k2_relat_1(k5_relat_1(X1,k6_relat_1(X0))))
% 4.16/0.99      | v1_relat_1(X1) != iProver_top ),
% 4.16/0.99      inference(superposition,[status(thm)],[c_483,c_6813]) ).
% 4.16/0.99  
% 4.16/0.99  cnf(c_6939,plain,
% 4.16/0.99      ( k7_relat_1(k6_relat_1(X0),k2_relat_1(k5_relat_1(X1,k6_relat_1(X0)))) = k6_relat_1(k2_relat_1(k5_relat_1(X1,k6_relat_1(X0))))
% 4.16/0.99      | v1_relat_1(X1) != iProver_top ),
% 4.16/0.99      inference(light_normalisation,[status(thm)],[c_6936,c_9]) ).
% 4.16/0.99  
% 4.16/0.99  cnf(c_6951,plain,
% 4.16/0.99      ( k7_relat_1(k6_relat_1(X0),k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)))) = k6_relat_1(k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)))) ),
% 4.16/0.99      inference(superposition,[status(thm)],[c_483,c_6939]) ).
% 4.16/0.99  
% 4.16/0.99  cnf(c_6955,plain,
% 4.16/0.99      ( k7_relat_1(k6_relat_1(X0),k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
% 4.16/0.99      inference(demodulation,[status(thm)],[c_6951,c_850]) ).
% 4.16/0.99  
% 4.16/0.99  cnf(c_7122,plain,
% 4.16/0.99      ( k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X0) = k4_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)))) ),
% 4.16/0.99      inference(superposition,[status(thm)],[c_6955,c_1186]) ).
% 4.16/0.99  
% 4.16/0.99  cnf(c_7206,plain,
% 4.16/0.99      ( k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X0) = k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
% 4.16/0.99      inference(demodulation,[status(thm)],[c_7122,c_11]) ).
% 4.16/0.99  
% 4.16/0.99  cnf(c_13,plain,
% 4.16/0.99      ( ~ v1_relat_1(X0) | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ),
% 4.16/0.99      inference(cnf_transformation,[],[f54]) ).
% 4.16/0.99  
% 4.16/0.99  cnf(c_474,plain,
% 4.16/0.99      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
% 4.16/0.99      | v1_relat_1(X0) != iProver_top ),
% 4.16/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 4.16/0.99  
% 4.16/0.99  cnf(c_1314,plain,
% 4.16/0.99      ( k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)))) = k7_relat_1(k6_relat_1(X0),X1)
% 4.16/0.99      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 4.16/0.99      inference(superposition,[status(thm)],[c_1251,c_474]) ).
% 4.16/0.99  
% 4.16/0.99  cnf(c_2387,plain,
% 4.16/0.99      ( k7_relat_1(k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X0),X1) = k7_relat_1(k6_relat_1(X0),X1)
% 4.16/0.99      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 4.16/0.99      inference(demodulation,[status(thm)],[c_1314,c_1819]) ).
% 4.16/0.99  
% 4.16/0.99  cnf(c_2391,plain,
% 4.16/0.99      ( k7_relat_1(k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X0),X1) = k7_relat_1(k6_relat_1(X0),X1) ),
% 4.16/0.99      inference(superposition,[status(thm)],[c_483,c_2387]) ).
% 4.16/0.99  
% 4.16/0.99  cnf(c_7631,plain,
% 4.16/0.99      ( k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X1) = k7_relat_1(k6_relat_1(X0),X1) ),
% 4.16/0.99      inference(demodulation,[status(thm)],[c_7206,c_2391]) ).
% 4.16/0.99  
% 4.16/0.99  cnf(c_8019,plain,
% 4.16/0.99      ( k7_relat_1(k6_relat_1(X0),k2_relat_1(k7_relat_1(k6_relat_1(X1),X0))) = k4_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
% 4.16/0.99      inference(superposition,[status(thm)],[c_7631,c_1186]) ).
% 4.16/0.99  
% 4.16/0.99  cnf(c_8056,plain,
% 4.16/0.99      ( k7_relat_1(k6_relat_1(X0),k2_relat_1(k7_relat_1(k6_relat_1(X1),X0))) = k7_relat_1(k6_relat_1(X0),X1) ),
% 4.16/0.99      inference(demodulation,[status(thm)],[c_8019,c_1186]) ).
% 4.16/0.99  
% 4.16/0.99  cnf(c_8841,plain,
% 4.16/0.99      ( k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),k2_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))))) = k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X0) ),
% 4.16/0.99      inference(superposition,[status(thm)],[c_8483,c_8056]) ).
% 4.16/0.99  
% 4.16/0.99  cnf(c_666,plain,
% 4.16/0.99      ( k7_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X0))) = k6_relat_1(X0) ),
% 4.16/0.99      inference(superposition,[status(thm)],[c_483,c_471]) ).
% 4.16/0.99  
% 4.16/0.99  cnf(c_667,plain,
% 4.16/0.99      ( k7_relat_1(k6_relat_1(X0),X0) = k6_relat_1(X0) ),
% 4.16/0.99      inference(light_normalisation,[status(thm)],[c_666,c_10]) ).
% 4.16/0.99  
% 4.16/0.99  cnf(c_8938,plain,
% 4.16/0.99      ( k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X0) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
% 4.16/0.99      inference(demodulation,[status(thm)],[c_8841,c_9,c_667]) ).
% 4.16/0.99  
% 4.16/0.99  cnf(c_9778,plain,
% 4.16/0.99      ( k7_relat_1(k6_relat_1(k1_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))))),k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X0))) ),
% 4.16/0.99      inference(superposition,[status(thm)],[c_7206,c_8938]) ).
% 4.16/0.99  
% 4.16/0.99  cnf(c_9374,plain,
% 4.16/0.99      ( k7_relat_1(k6_relat_1(X0),k2_relat_1(k7_relat_1(k6_relat_1(X1),X0))) = k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
% 4.16/0.99      inference(superposition,[status(thm)],[c_9169,c_6955]) ).
% 4.16/0.99  
% 4.16/0.99  cnf(c_9461,plain,
% 4.16/0.99      ( k7_relat_1(k6_relat_1(X0),k2_relat_1(k7_relat_1(k6_relat_1(X1),X0))) = k7_relat_1(k6_relat_1(X1),X0) ),
% 4.16/0.99      inference(superposition,[status(thm)],[c_9169,c_7631]) ).
% 4.16/0.99  
% 4.16/0.99  cnf(c_9465,plain,
% 4.16/0.99      ( k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k7_relat_1(k6_relat_1(X1),X0) ),
% 4.16/0.99      inference(demodulation,[status(thm)],[c_9374,c_9461]) ).
% 4.16/0.99  
% 4.16/0.99  cnf(c_9923,plain,
% 4.16/0.99      ( k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),k2_relat_1(k7_relat_1(k6_relat_1(X1),X0))) = k6_relat_1(k1_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X1),X0))))) ),
% 4.16/0.99      inference(light_normalisation,[status(thm)],[c_9778,c_7206,c_9465]) ).
% 4.16/0.99  
% 4.16/0.99  cnf(c_9924,plain,
% 4.16/0.99      ( k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),k2_relat_1(k7_relat_1(k6_relat_1(X1),X0))) = k7_relat_1(k6_relat_1(X0),X1) ),
% 4.16/0.99      inference(demodulation,[status(thm)],[c_9923,c_10,c_9465]) ).
% 4.16/0.99  
% 4.16/0.99  cnf(c_10174,plain,
% 4.16/0.99      ( k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),k2_relat_1(k7_relat_1(k6_relat_1(X1),X0))))) = k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
% 4.16/0.99      inference(superposition,[status(thm)],[c_9924,c_6955]) ).
% 4.16/0.99  
% 4.16/0.99  cnf(c_10277,plain,
% 4.16/0.99      ( k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
% 4.16/0.99      inference(demodulation,[status(thm)],[c_10174,c_9924]) ).
% 4.16/0.99  
% 4.16/0.99  cnf(c_9779,plain,
% 4.16/0.99      ( k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X1))) ),
% 4.16/0.99      inference(superposition,[status(thm)],[c_7631,c_8938]) ).
% 4.16/0.99  
% 4.16/0.99  cnf(c_9922,plain,
% 4.16/0.99      ( k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
% 4.16/0.99      inference(light_normalisation,[status(thm)],[c_9779,c_7631]) ).
% 4.16/0.99  
% 4.16/0.99  cnf(c_10278,plain,
% 4.16/0.99      ( k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k7_relat_1(k6_relat_1(X1),X0) ),
% 4.16/0.99      inference(light_normalisation,[status(thm)],[c_10277,c_9465,c_9922]) ).
% 4.16/0.99  
% 4.16/0.99  cnf(c_17,negated_conjecture,
% 4.16/0.99      ( k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) != k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) ),
% 4.16/0.99      inference(cnf_transformation,[],[f65]) ).
% 4.16/0.99  
% 4.16/0.99  cnf(c_719,plain,
% 4.16/0.99      ( k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(sK0),sK1))) != k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) ),
% 4.16/0.99      inference(demodulation,[status(thm)],[c_715,c_17]) ).
% 4.16/0.99  
% 4.16/0.99  cnf(c_883,plain,
% 4.16/0.99      ( k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(sK0),sK1))) != k7_relat_1(k6_relat_1(sK0),sK1) ),
% 4.16/0.99      inference(demodulation,[status(thm)],[c_850,c_719]) ).
% 4.16/0.99  
% 4.16/0.99  cnf(c_11479,plain,
% 4.16/0.99      ( k7_relat_1(k6_relat_1(sK1),sK0) != k7_relat_1(k6_relat_1(sK0),sK1) ),
% 4.16/0.99      inference(demodulation,[status(thm)],[c_10278,c_883]) ).
% 4.16/0.99  
% 4.16/0.99  cnf(c_11742,plain,
% 4.16/0.99      ( $false ),
% 4.16/0.99      inference(superposition,[status(thm)],[c_9169,c_11479]) ).
% 4.16/0.99  
% 4.16/0.99  
% 4.16/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 4.16/0.99  
% 4.16/0.99  ------                               Statistics
% 4.16/0.99  
% 4.16/0.99  ------ General
% 4.16/0.99  
% 4.16/0.99  abstr_ref_over_cycles:                  0
% 4.16/0.99  abstr_ref_under_cycles:                 0
% 4.16/0.99  gc_basic_clause_elim:                   0
% 4.16/0.99  forced_gc_time:                         0
% 4.16/0.99  parsing_time:                           0.014
% 4.16/0.99  unif_index_cands_time:                  0.
% 4.16/0.99  unif_index_add_time:                    0.
% 4.16/0.99  orderings_time:                         0.
% 4.16/0.99  out_proof_time:                         0.009
% 4.16/0.99  total_time:                             0.489
% 4.16/0.99  num_of_symbols:                         45
% 4.16/0.99  num_of_terms:                           18719
% 4.16/0.99  
% 4.16/0.99  ------ Preprocessing
% 4.16/0.99  
% 4.16/0.99  num_of_splits:                          0
% 4.16/0.99  num_of_split_atoms:                     0
% 4.16/0.99  num_of_reused_defs:                     0
% 4.16/0.99  num_eq_ax_congr_red:                    6
% 4.16/0.99  num_of_sem_filtered_clauses:            1
% 4.16/0.99  num_of_subtypes:                        0
% 4.16/0.99  monotx_restored_types:                  0
% 4.16/0.99  sat_num_of_epr_types:                   0
% 4.16/0.99  sat_num_of_non_cyclic_types:            0
% 4.16/0.99  sat_guarded_non_collapsed_types:        0
% 4.16/0.99  num_pure_diseq_elim:                    0
% 4.16/0.99  simp_replaced_by:                       0
% 4.16/0.99  res_preprocessed:                       81
% 4.16/0.99  prep_upred:                             0
% 4.16/0.99  prep_unflattend:                        2
% 4.16/0.99  smt_new_axioms:                         0
% 4.16/0.99  pred_elim_cands:                        2
% 4.16/0.99  pred_elim:                              0
% 4.16/0.99  pred_elim_cl:                           0
% 4.16/0.99  pred_elim_cycles:                       1
% 4.16/0.99  merged_defs:                            0
% 4.16/0.99  merged_defs_ncl:                        0
% 4.16/0.99  bin_hyper_res:                          0
% 4.16/0.99  prep_cycles:                            3
% 4.16/0.99  pred_elim_time:                         0.001
% 4.16/0.99  splitting_time:                         0.
% 4.16/0.99  sem_filter_time:                        0.
% 4.16/0.99  monotx_time:                            0.
% 4.16/0.99  subtype_inf_time:                       0.
% 4.16/0.99  
% 4.16/0.99  ------ Problem properties
% 4.16/0.99  
% 4.16/0.99  clauses:                                18
% 4.16/0.99  conjectures:                            1
% 4.16/0.99  epr:                                    0
% 4.16/0.99  horn:                                   18
% 4.16/0.99  ground:                                 1
% 4.16/0.99  unary:                                  6
% 4.16/0.99  binary:                                 7
% 4.16/0.99  lits:                                   36
% 4.16/0.99  lits_eq:                                14
% 4.16/0.99  fd_pure:                                0
% 4.16/0.99  fd_pseudo:                              0
% 4.16/0.99  fd_cond:                                0
% 4.16/0.99  fd_pseudo_cond:                         0
% 4.16/0.99  ac_symbols:                             0
% 4.16/0.99  
% 4.16/0.99  ------ Propositional Solver
% 4.16/0.99  
% 4.16/0.99  prop_solver_calls:                      28
% 4.16/0.99  prop_fast_solver_calls:                 649
% 4.16/0.99  smt_solver_calls:                       0
% 4.16/0.99  smt_fast_solver_calls:                  0
% 4.16/0.99  prop_num_of_clauses:                    5514
% 4.16/0.99  prop_preprocess_simplified:             7974
% 4.16/0.99  prop_fo_subsumed:                       4
% 4.16/0.99  prop_solver_time:                       0.
% 4.16/0.99  smt_solver_time:                        0.
% 4.16/0.99  smt_fast_solver_time:                   0.
% 4.16/0.99  prop_fast_solver_time:                  0.
% 4.16/0.99  prop_unsat_core_time:                   0.
% 4.16/0.99  
% 4.16/0.99  ------ QBF
% 4.16/0.99  
% 4.16/0.99  qbf_q_res:                              0
% 4.16/0.99  qbf_num_tautologies:                    0
% 4.16/0.99  qbf_prep_cycles:                        0
% 4.16/0.99  
% 4.16/0.99  ------ BMC1
% 4.16/0.99  
% 4.16/0.99  bmc1_current_bound:                     -1
% 4.16/0.99  bmc1_last_solved_bound:                 -1
% 4.16/0.99  bmc1_unsat_core_size:                   -1
% 4.16/0.99  bmc1_unsat_core_parents_size:           -1
% 4.16/0.99  bmc1_merge_next_fun:                    0
% 4.16/0.99  bmc1_unsat_core_clauses_time:           0.
% 4.16/0.99  
% 4.16/0.99  ------ Instantiation
% 4.16/0.99  
% 4.16/0.99  inst_num_of_clauses:                    2039
% 4.16/0.99  inst_num_in_passive:                    556
% 4.16/0.99  inst_num_in_active:                     810
% 4.16/0.99  inst_num_in_unprocessed:                673
% 4.16/0.99  inst_num_of_loops:                      870
% 4.16/0.99  inst_num_of_learning_restarts:          0
% 4.16/0.99  inst_num_moves_active_passive:          56
% 4.16/0.99  inst_lit_activity:                      0
% 4.16/0.99  inst_lit_activity_moves:                0
% 4.16/0.99  inst_num_tautologies:                   0
% 4.16/0.99  inst_num_prop_implied:                  0
% 4.16/0.99  inst_num_existing_simplified:           0
% 4.16/0.99  inst_num_eq_res_simplified:             0
% 4.16/0.99  inst_num_child_elim:                    0
% 4.16/0.99  inst_num_of_dismatching_blockings:      613
% 4.16/0.99  inst_num_of_non_proper_insts:           2072
% 4.16/0.99  inst_num_of_duplicates:                 0
% 4.16/0.99  inst_inst_num_from_inst_to_res:         0
% 4.16/0.99  inst_dismatching_checking_time:         0.
% 4.16/0.99  
% 4.16/0.99  ------ Resolution
% 4.16/0.99  
% 4.16/0.99  res_num_of_clauses:                     0
% 4.16/0.99  res_num_in_passive:                     0
% 4.16/0.99  res_num_in_active:                      0
% 4.16/0.99  res_num_of_loops:                       84
% 4.16/0.99  res_forward_subset_subsumed:            392
% 4.16/0.99  res_backward_subset_subsumed:           2
% 4.16/0.99  res_forward_subsumed:                   0
% 4.16/0.99  res_backward_subsumed:                  0
% 4.16/0.99  res_forward_subsumption_resolution:     0
% 4.16/0.99  res_backward_subsumption_resolution:    0
% 4.16/0.99  res_clause_to_clause_subsumption:       3623
% 4.16/0.99  res_orphan_elimination:                 0
% 4.16/0.99  res_tautology_del:                      233
% 4.16/0.99  res_num_eq_res_simplified:              0
% 4.16/0.99  res_num_sel_changes:                    0
% 4.16/0.99  res_moves_from_active_to_pass:          0
% 4.16/0.99  
% 4.16/0.99  ------ Superposition
% 4.16/0.99  
% 4.16/0.99  sup_time_total:                         0.
% 4.16/0.99  sup_time_generating:                    0.
% 4.16/0.99  sup_time_sim_full:                      0.
% 4.16/0.99  sup_time_sim_immed:                     0.
% 4.16/0.99  
% 4.16/0.99  sup_num_of_clauses:                     731
% 4.16/0.99  sup_num_in_active:                      103
% 4.16/0.99  sup_num_in_passive:                     628
% 4.16/0.99  sup_num_of_loops:                       172
% 4.16/0.99  sup_fw_superposition:                   814
% 4.16/0.99  sup_bw_superposition:                   1344
% 4.16/0.99  sup_immediate_simplified:               1451
% 4.16/0.99  sup_given_eliminated:                   3
% 4.16/0.99  comparisons_done:                       0
% 4.16/0.99  comparisons_avoided:                    0
% 4.16/0.99  
% 4.16/0.99  ------ Simplifications
% 4.16/0.99  
% 4.16/0.99  
% 4.16/0.99  sim_fw_subset_subsumed:                 11
% 4.16/0.99  sim_bw_subset_subsumed:                 51
% 4.16/0.99  sim_fw_subsumed:                        264
% 4.16/0.99  sim_bw_subsumed:                        2
% 4.16/0.99  sim_fw_subsumption_res:                 0
% 4.16/0.99  sim_bw_subsumption_res:                 0
% 4.16/0.99  sim_tautology_del:                      15
% 4.16/0.99  sim_eq_tautology_del:                   278
% 4.16/0.99  sim_eq_res_simp:                        0
% 4.16/0.99  sim_fw_demodulated:                     993
% 4.16/0.99  sim_bw_demodulated:                     107
% 4.16/0.99  sim_light_normalised:                   557
% 4.16/0.99  sim_joinable_taut:                      0
% 4.16/0.99  sim_joinable_simp:                      0
% 4.16/0.99  sim_ac_normalised:                      0
% 4.16/0.99  sim_smt_subsumption:                    0
% 4.16/0.99  
%------------------------------------------------------------------------------
