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
% DateTime   : Thu Dec  3 11:49:58 EST 2020

% Result     : Theorem 3.19s
% Output     : CNFRefutation 3.19s
% Verified   : 
% Statistics : Number of formulae       :  147 (4943 expanded)
%              Number of clauses        :   80 (1828 expanded)
%              Number of leaves         :   22 (1184 expanded)
%              Depth                    :   24
%              Number of atoms          :  233 (6745 expanded)
%              Number of equality atoms :  163 (4565 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    3 (   2 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f8])).

fof(f59,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f43,f44])).

fof(f60,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f42,f59])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f41,f60])).

fof(f62,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f40,f61])).

fof(f63,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f39,f62])).

fof(f64,plain,(
    ! [X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f38,f63,f63])).

fof(f11,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f1])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_relat_1(X1),k4_xboole_0(k1_relat_1(X1),X0)) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f56,f37])).

fof(f15,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f15])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f65,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f45,f37,f63])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k5_relat_1(X1,k6_relat_1(X0)) = k8_relat_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = k8_relat_1(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = k8_relat_1(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f52,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f15])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f24,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f53,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k5_relat_1(X1,k8_relat_1(X0,X2)) = k8_relat_1(X0,k5_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k5_relat_1(X1,k8_relat_1(X0,X2)) = k8_relat_1(X0,k5_relat_1(X1,X2))
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X1,k8_relat_1(X0,X2)) = k8_relat_1(X0,k5_relat_1(X1,X2))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f55,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f21,conjecture,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f21])).

fof(f34,plain,(
    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f22])).

fof(f35,plain,
    ( ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))
   => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f34,f35])).

fof(f58,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f36])).

fof(f67,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(definition_unfolding,[],[f58,f37])).

cnf(c_0,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_3,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_369,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_12,plain,
    ( ~ v1_relat_1(X0)
    | k4_xboole_0(k1_relat_1(X0),k4_xboole_0(k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_362,plain,
    ( k4_xboole_0(k1_relat_1(X0),k4_xboole_0(k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_828,plain,
    ( k4_xboole_0(k1_relat_1(k6_relat_1(X0)),k4_xboole_0(k1_relat_1(k6_relat_1(X0)),X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(superposition,[status(thm)],[c_369,c_362])).

cnf(c_8,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_829,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(light_normalisation,[status(thm)],[c_828,c_8])).

cnf(c_1,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1014,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(demodulation,[status(thm)],[c_829,c_1])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X1,X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_368,plain,
    ( k5_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X1,X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1480,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k8_relat_1(X1,k6_relat_1(X0)) ),
    inference(superposition,[status(thm)],[c_369,c_368])).

cnf(c_13,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_361,plain,
    ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_695,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(superposition,[status(thm)],[c_369,c_361])).

cnf(c_1483,plain,
    ( k7_relat_1(k6_relat_1(X0),X1) = k8_relat_1(X0,k6_relat_1(X1)) ),
    inference(demodulation,[status(thm)],[c_1480,c_695])).

cnf(c_1995,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))) ),
    inference(light_normalisation,[status(thm)],[c_1014,c_1483])).

cnf(c_1999,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))) ),
    inference(superposition,[status(thm)],[c_0,c_1995])).

cnf(c_2270,plain,
    ( k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))) = k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))) ),
    inference(superposition,[status(thm)],[c_1999,c_1995])).

cnf(c_6,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_366,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3727,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(k6_relat_1(X0),X1)),X0) = iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8,c_366])).

cnf(c_41,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_3870,plain,
    ( v1_relat_1(X1) != iProver_top
    | r1_tarski(k1_relat_1(k5_relat_1(k6_relat_1(X0),X1)),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3727,c_41])).

cnf(c_3871,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(k6_relat_1(X0),X1)),X0) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_3870])).

cnf(c_3878,plain,
    ( r1_tarski(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))),X1) = iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1480,c_3871])).

cnf(c_4045,plain,
    ( r1_tarski(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))),X1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3878,c_41])).

cnf(c_4052,plain,
    ( r1_tarski(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2270,c_4045])).

cnf(c_7,plain,
    ( k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_10,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_relat_1(X1)) = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_364,plain,
    ( k5_relat_1(X0,k6_relat_1(X1)) = X0
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1893,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k6_relat_1(X0)
    | r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_364])).

cnf(c_1894,plain,
    ( k8_relat_1(X0,k6_relat_1(X1)) = k6_relat_1(X1)
    | r1_tarski(X1,X0) != iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1893,c_1480])).

cnf(c_5423,plain,
    ( k8_relat_1(X0,k6_relat_1(X1)) = k6_relat_1(X1)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1894,c_369])).

cnf(c_5429,plain,
    ( k8_relat_1(X0,k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))))) = k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))) ),
    inference(superposition,[status(thm)],[c_4052,c_5423])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | v1_relat_1(k5_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_370,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k5_relat_1(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2278,plain,
    ( v1_relat_1(k8_relat_1(X0,k6_relat_1(X1))) = iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1480,c_370])).

cnf(c_5506,plain,
    ( v1_relat_1(k8_relat_1(X0,k6_relat_1(X1))) = iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2278,c_41])).

cnf(c_5512,plain,
    ( v1_relat_1(k8_relat_1(X0,k6_relat_1(X1))) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5506,c_369])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_365,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_5521,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))),k8_relat_1(X0,k6_relat_1(X1))) = k8_relat_1(X0,k6_relat_1(X1)) ),
    inference(superposition,[status(thm)],[c_5512,c_365])).

cnf(c_7444,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1(k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))))),k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))))) = k8_relat_1(X0,k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))))) ),
    inference(superposition,[status(thm)],[c_5429,c_5521])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k8_relat_1(X2,k5_relat_1(X0,X1)) = k5_relat_1(X0,k8_relat_1(X2,X1)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_367,plain,
    ( k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2))
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_4025,plain,
    ( k8_relat_1(X0,k5_relat_1(k6_relat_1(X1),X2)) = k5_relat_1(k6_relat_1(X1),k8_relat_1(X0,X2))
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_369,c_367])).

cnf(c_5491,plain,
    ( k8_relat_1(X0,k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) = k5_relat_1(k6_relat_1(X1),k8_relat_1(X0,k6_relat_1(X2))) ),
    inference(superposition,[status(thm)],[c_369,c_4025])).

cnf(c_5493,plain,
    ( k5_relat_1(k6_relat_1(X0),k8_relat_1(X1,k6_relat_1(X2))) = k8_relat_1(X1,k8_relat_1(X2,k6_relat_1(X0))) ),
    inference(demodulation,[status(thm)],[c_5491,c_1480])).

cnf(c_7452,plain,
    ( k8_relat_1(X0,k8_relat_1(X1,k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))))) = k8_relat_1(X0,k6_relat_1(X1)) ),
    inference(superposition,[status(thm)],[c_5521,c_5493])).

cnf(c_5744,plain,
    ( k8_relat_1(X0,k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))))) = k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))) ),
    inference(superposition,[status(thm)],[c_2270,c_5429])).

cnf(c_7454,plain,
    ( k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))) = k8_relat_1(X0,k6_relat_1(X1)) ),
    inference(demodulation,[status(thm)],[c_7452,c_5744])).

cnf(c_5428,plain,
    ( k8_relat_1(X0,k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))))) = k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0)))) ),
    inference(superposition,[status(thm)],[c_4045,c_5423])).

cnf(c_5683,plain,
    ( k8_relat_1(X0,k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))))) = k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0)))) ),
    inference(superposition,[status(thm)],[c_2270,c_5428])).

cnf(c_7470,plain,
    ( k8_relat_1(X0,k8_relat_1(X0,k6_relat_1(X1))) = k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0)))) ),
    inference(demodulation,[status(thm)],[c_7454,c_5683])).

cnf(c_11,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_363,plain,
    ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_566,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(k2_relat_1(k6_relat_1(X0)))) = k6_relat_1(X0) ),
    inference(superposition,[status(thm)],[c_369,c_363])).

cnf(c_567,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X0)) = k6_relat_1(X0) ),
    inference(light_normalisation,[status(thm)],[c_566,c_7])).

cnf(c_1485,plain,
    ( k8_relat_1(X0,k6_relat_1(X0)) = k6_relat_1(X0) ),
    inference(superposition,[status(thm)],[c_567,c_1480])).

cnf(c_5616,plain,
    ( k8_relat_1(X0,k8_relat_1(X0,k6_relat_1(X1))) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
    inference(superposition,[status(thm)],[c_1485,c_5493])).

cnf(c_5639,plain,
    ( k8_relat_1(X0,k8_relat_1(X0,k6_relat_1(X1))) = k8_relat_1(X0,k6_relat_1(X1)) ),
    inference(demodulation,[status(thm)],[c_5616,c_1480])).

cnf(c_7477,plain,
    ( k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))) = k8_relat_1(X1,k6_relat_1(X0)) ),
    inference(light_normalisation,[status(thm)],[c_7470,c_5639])).

cnf(c_7489,plain,
    ( k8_relat_1(X0,k8_relat_1(X1,k8_relat_1(X1,k6_relat_1(X0)))) = k8_relat_1(X0,k6_relat_1(X1)) ),
    inference(light_normalisation,[status(thm)],[c_7452,c_7477])).

cnf(c_7491,plain,
    ( k8_relat_1(X0,k8_relat_1(X1,k6_relat_1(X0))) = k8_relat_1(X0,k6_relat_1(X1)) ),
    inference(demodulation,[status(thm)],[c_7489,c_5639])).

cnf(c_7511,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))),k8_relat_1(X0,k6_relat_1(X1))) = k8_relat_1(X1,k6_relat_1(X0)) ),
    inference(light_normalisation,[status(thm)],[c_7444,c_7477,c_7491])).

cnf(c_7446,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1(k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))))),k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))))) = k8_relat_1(X1,k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))))) ),
    inference(superposition,[status(thm)],[c_5428,c_5521])).

cnf(c_7502,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))),k8_relat_1(X0,k6_relat_1(X1))) = k8_relat_1(X0,k8_relat_1(X0,k6_relat_1(X1))) ),
    inference(light_normalisation,[status(thm)],[c_7446,c_7477])).

cnf(c_7503,plain,
    ( k5_relat_1(k8_relat_1(X0,k6_relat_1(X1)),k8_relat_1(X1,k6_relat_1(X0))) = k8_relat_1(X1,k8_relat_1(X1,k6_relat_1(X0))) ),
    inference(demodulation,[status(thm)],[c_7502,c_7477])).

cnf(c_7505,plain,
    ( k5_relat_1(k8_relat_1(X0,k6_relat_1(X1)),k8_relat_1(X1,k6_relat_1(X0))) = k8_relat_1(X1,k6_relat_1(X0)) ),
    inference(demodulation,[status(thm)],[c_7503,c_5639])).

cnf(c_7512,plain,
    ( k8_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X1,k6_relat_1(X0)) ),
    inference(demodulation,[status(thm)],[c_7511,c_7477,c_7505])).

cnf(c_14,negated_conjecture,
    ( k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1016,plain,
    ( k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(sK0),sK1))) != k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) ),
    inference(demodulation,[status(thm)],[c_829,c_14])).

cnf(c_1114,plain,
    ( k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(sK0),sK1))) != k7_relat_1(k6_relat_1(sK0),sK1) ),
    inference(demodulation,[status(thm)],[c_695,c_1016])).

cnf(c_1686,plain,
    ( k6_relat_1(k1_relat_1(k8_relat_1(sK0,k6_relat_1(sK1)))) != k8_relat_1(sK0,k6_relat_1(sK1)) ),
    inference(demodulation,[status(thm)],[c_1483,c_1114])).

cnf(c_3472,plain,
    ( k6_relat_1(k1_relat_1(k8_relat_1(sK1,k6_relat_1(sK0)))) != k8_relat_1(sK0,k6_relat_1(sK1)) ),
    inference(demodulation,[status(thm)],[c_2270,c_1686])).

cnf(c_7464,plain,
    ( k8_relat_1(sK1,k6_relat_1(sK0)) != k8_relat_1(sK0,k6_relat_1(sK1)) ),
    inference(demodulation,[status(thm)],[c_7454,c_3472])).

cnf(c_7514,plain,
    ( k8_relat_1(sK1,k6_relat_1(sK0)) != k8_relat_1(sK1,k6_relat_1(sK0)) ),
    inference(demodulation,[status(thm)],[c_7512,c_7464])).

cnf(c_7516,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_7514])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:34:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.19/1.06  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.19/1.06  
% 3.19/1.06  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.19/1.06  
% 3.19/1.06  ------  iProver source info
% 3.19/1.06  
% 3.19/1.06  git: date: 2020-06-30 10:37:57 +0100
% 3.19/1.06  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.19/1.06  git: non_committed_changes: false
% 3.19/1.06  git: last_make_outside_of_git: false
% 3.19/1.06  
% 3.19/1.06  ------ 
% 3.19/1.06  
% 3.19/1.06  ------ Input Options
% 3.19/1.06  
% 3.19/1.06  --out_options                           all
% 3.19/1.06  --tptp_safe_out                         true
% 3.19/1.06  --problem_path                          ""
% 3.19/1.06  --include_path                          ""
% 3.19/1.06  --clausifier                            res/vclausify_rel
% 3.19/1.06  --clausifier_options                    --mode clausify
% 3.19/1.06  --stdin                                 false
% 3.19/1.06  --stats_out                             all
% 3.19/1.06  
% 3.19/1.06  ------ General Options
% 3.19/1.06  
% 3.19/1.06  --fof                                   false
% 3.19/1.06  --time_out_real                         305.
% 3.19/1.06  --time_out_virtual                      -1.
% 3.19/1.06  --symbol_type_check                     false
% 3.19/1.06  --clausify_out                          false
% 3.19/1.06  --sig_cnt_out                           false
% 3.19/1.06  --trig_cnt_out                          false
% 3.19/1.06  --trig_cnt_out_tolerance                1.
% 3.19/1.06  --trig_cnt_out_sk_spl                   false
% 3.19/1.06  --abstr_cl_out                          false
% 3.19/1.06  
% 3.19/1.06  ------ Global Options
% 3.19/1.06  
% 3.19/1.06  --schedule                              default
% 3.19/1.06  --add_important_lit                     false
% 3.19/1.06  --prop_solver_per_cl                    1000
% 3.19/1.06  --min_unsat_core                        false
% 3.19/1.06  --soft_assumptions                      false
% 3.19/1.06  --soft_lemma_size                       3
% 3.19/1.06  --prop_impl_unit_size                   0
% 3.19/1.06  --prop_impl_unit                        []
% 3.19/1.06  --share_sel_clauses                     true
% 3.19/1.06  --reset_solvers                         false
% 3.19/1.06  --bc_imp_inh                            [conj_cone]
% 3.19/1.06  --conj_cone_tolerance                   3.
% 3.19/1.06  --extra_neg_conj                        none
% 3.19/1.06  --large_theory_mode                     true
% 3.19/1.06  --prolific_symb_bound                   200
% 3.19/1.06  --lt_threshold                          2000
% 3.19/1.06  --clause_weak_htbl                      true
% 3.19/1.06  --gc_record_bc_elim                     false
% 3.19/1.06  
% 3.19/1.06  ------ Preprocessing Options
% 3.19/1.06  
% 3.19/1.06  --preprocessing_flag                    true
% 3.19/1.06  --time_out_prep_mult                    0.1
% 3.19/1.06  --splitting_mode                        input
% 3.19/1.06  --splitting_grd                         true
% 3.19/1.06  --splitting_cvd                         false
% 3.19/1.06  --splitting_cvd_svl                     false
% 3.19/1.06  --splitting_nvd                         32
% 3.19/1.06  --sub_typing                            true
% 3.19/1.06  --prep_gs_sim                           true
% 3.19/1.06  --prep_unflatten                        true
% 3.19/1.06  --prep_res_sim                          true
% 3.19/1.06  --prep_upred                            true
% 3.19/1.06  --prep_sem_filter                       exhaustive
% 3.19/1.06  --prep_sem_filter_out                   false
% 3.19/1.06  --pred_elim                             true
% 3.19/1.06  --res_sim_input                         true
% 3.19/1.06  --eq_ax_congr_red                       true
% 3.19/1.06  --pure_diseq_elim                       true
% 3.19/1.06  --brand_transform                       false
% 3.19/1.06  --non_eq_to_eq                          false
% 3.19/1.06  --prep_def_merge                        true
% 3.19/1.06  --prep_def_merge_prop_impl              false
% 3.19/1.06  --prep_def_merge_mbd                    true
% 3.19/1.06  --prep_def_merge_tr_red                 false
% 3.19/1.06  --prep_def_merge_tr_cl                  false
% 3.19/1.06  --smt_preprocessing                     true
% 3.19/1.06  --smt_ac_axioms                         fast
% 3.19/1.06  --preprocessed_out                      false
% 3.19/1.06  --preprocessed_stats                    false
% 3.19/1.06  
% 3.19/1.06  ------ Abstraction refinement Options
% 3.19/1.06  
% 3.19/1.06  --abstr_ref                             []
% 3.19/1.06  --abstr_ref_prep                        false
% 3.19/1.06  --abstr_ref_until_sat                   false
% 3.19/1.06  --abstr_ref_sig_restrict                funpre
% 3.19/1.06  --abstr_ref_af_restrict_to_split_sk     false
% 3.19/1.06  --abstr_ref_under                       []
% 3.19/1.06  
% 3.19/1.06  ------ SAT Options
% 3.19/1.06  
% 3.19/1.06  --sat_mode                              false
% 3.19/1.06  --sat_fm_restart_options                ""
% 3.19/1.06  --sat_gr_def                            false
% 3.19/1.06  --sat_epr_types                         true
% 3.19/1.06  --sat_non_cyclic_types                  false
% 3.19/1.06  --sat_finite_models                     false
% 3.19/1.06  --sat_fm_lemmas                         false
% 3.19/1.06  --sat_fm_prep                           false
% 3.19/1.06  --sat_fm_uc_incr                        true
% 3.19/1.06  --sat_out_model                         small
% 3.19/1.06  --sat_out_clauses                       false
% 3.19/1.06  
% 3.19/1.06  ------ QBF Options
% 3.19/1.06  
% 3.19/1.06  --qbf_mode                              false
% 3.19/1.06  --qbf_elim_univ                         false
% 3.19/1.06  --qbf_dom_inst                          none
% 3.19/1.06  --qbf_dom_pre_inst                      false
% 3.19/1.06  --qbf_sk_in                             false
% 3.19/1.06  --qbf_pred_elim                         true
% 3.19/1.06  --qbf_split                             512
% 3.19/1.06  
% 3.19/1.06  ------ BMC1 Options
% 3.19/1.06  
% 3.19/1.06  --bmc1_incremental                      false
% 3.19/1.06  --bmc1_axioms                           reachable_all
% 3.19/1.06  --bmc1_min_bound                        0
% 3.19/1.06  --bmc1_max_bound                        -1
% 3.19/1.06  --bmc1_max_bound_default                -1
% 3.19/1.06  --bmc1_symbol_reachability              true
% 3.19/1.06  --bmc1_property_lemmas                  false
% 3.19/1.06  --bmc1_k_induction                      false
% 3.19/1.06  --bmc1_non_equiv_states                 false
% 3.19/1.06  --bmc1_deadlock                         false
% 3.19/1.06  --bmc1_ucm                              false
% 3.19/1.06  --bmc1_add_unsat_core                   none
% 3.19/1.06  --bmc1_unsat_core_children              false
% 3.19/1.06  --bmc1_unsat_core_extrapolate_axioms    false
% 3.19/1.06  --bmc1_out_stat                         full
% 3.19/1.06  --bmc1_ground_init                      false
% 3.19/1.06  --bmc1_pre_inst_next_state              false
% 3.19/1.06  --bmc1_pre_inst_state                   false
% 3.19/1.06  --bmc1_pre_inst_reach_state             false
% 3.19/1.06  --bmc1_out_unsat_core                   false
% 3.19/1.06  --bmc1_aig_witness_out                  false
% 3.19/1.06  --bmc1_verbose                          false
% 3.19/1.06  --bmc1_dump_clauses_tptp                false
% 3.19/1.06  --bmc1_dump_unsat_core_tptp             false
% 3.19/1.06  --bmc1_dump_file                        -
% 3.19/1.06  --bmc1_ucm_expand_uc_limit              128
% 3.19/1.06  --bmc1_ucm_n_expand_iterations          6
% 3.19/1.06  --bmc1_ucm_extend_mode                  1
% 3.19/1.06  --bmc1_ucm_init_mode                    2
% 3.19/1.06  --bmc1_ucm_cone_mode                    none
% 3.19/1.06  --bmc1_ucm_reduced_relation_type        0
% 3.19/1.06  --bmc1_ucm_relax_model                  4
% 3.19/1.06  --bmc1_ucm_full_tr_after_sat            true
% 3.19/1.06  --bmc1_ucm_expand_neg_assumptions       false
% 3.19/1.06  --bmc1_ucm_layered_model                none
% 3.19/1.06  --bmc1_ucm_max_lemma_size               10
% 3.19/1.06  
% 3.19/1.06  ------ AIG Options
% 3.19/1.06  
% 3.19/1.06  --aig_mode                              false
% 3.19/1.06  
% 3.19/1.06  ------ Instantiation Options
% 3.19/1.06  
% 3.19/1.06  --instantiation_flag                    true
% 3.19/1.06  --inst_sos_flag                         false
% 3.19/1.06  --inst_sos_phase                        true
% 3.19/1.06  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.19/1.06  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.19/1.06  --inst_lit_sel_side                     num_symb
% 3.19/1.06  --inst_solver_per_active                1400
% 3.19/1.06  --inst_solver_calls_frac                1.
% 3.19/1.06  --inst_passive_queue_type               priority_queues
% 3.19/1.06  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.19/1.06  --inst_passive_queues_freq              [25;2]
% 3.19/1.06  --inst_dismatching                      true
% 3.19/1.06  --inst_eager_unprocessed_to_passive     true
% 3.19/1.06  --inst_prop_sim_given                   true
% 3.19/1.06  --inst_prop_sim_new                     false
% 3.19/1.06  --inst_subs_new                         false
% 3.19/1.06  --inst_eq_res_simp                      false
% 3.19/1.06  --inst_subs_given                       false
% 3.19/1.06  --inst_orphan_elimination               true
% 3.19/1.06  --inst_learning_loop_flag               true
% 3.19/1.06  --inst_learning_start                   3000
% 3.19/1.06  --inst_learning_factor                  2
% 3.19/1.06  --inst_start_prop_sim_after_learn       3
% 3.19/1.06  --inst_sel_renew                        solver
% 3.19/1.06  --inst_lit_activity_flag                true
% 3.19/1.06  --inst_restr_to_given                   false
% 3.19/1.06  --inst_activity_threshold               500
% 3.19/1.06  --inst_out_proof                        true
% 3.19/1.06  
% 3.19/1.06  ------ Resolution Options
% 3.19/1.06  
% 3.19/1.06  --resolution_flag                       true
% 3.19/1.06  --res_lit_sel                           adaptive
% 3.19/1.06  --res_lit_sel_side                      none
% 3.19/1.06  --res_ordering                          kbo
% 3.19/1.06  --res_to_prop_solver                    active
% 3.19/1.06  --res_prop_simpl_new                    false
% 3.19/1.06  --res_prop_simpl_given                  true
% 3.19/1.06  --res_passive_queue_type                priority_queues
% 3.19/1.06  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.19/1.06  --res_passive_queues_freq               [15;5]
% 3.19/1.06  --res_forward_subs                      full
% 3.19/1.06  --res_backward_subs                     full
% 3.19/1.06  --res_forward_subs_resolution           true
% 3.19/1.06  --res_backward_subs_resolution          true
% 3.19/1.06  --res_orphan_elimination                true
% 3.19/1.06  --res_time_limit                        2.
% 3.19/1.06  --res_out_proof                         true
% 3.19/1.06  
% 3.19/1.06  ------ Superposition Options
% 3.19/1.06  
% 3.19/1.06  --superposition_flag                    true
% 3.19/1.06  --sup_passive_queue_type                priority_queues
% 3.19/1.06  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.19/1.06  --sup_passive_queues_freq               [8;1;4]
% 3.19/1.06  --demod_completeness_check              fast
% 3.19/1.06  --demod_use_ground                      true
% 3.19/1.06  --sup_to_prop_solver                    passive
% 3.19/1.06  --sup_prop_simpl_new                    true
% 3.19/1.06  --sup_prop_simpl_given                  true
% 3.19/1.06  --sup_fun_splitting                     false
% 3.19/1.06  --sup_smt_interval                      50000
% 3.19/1.06  
% 3.19/1.06  ------ Superposition Simplification Setup
% 3.19/1.06  
% 3.19/1.06  --sup_indices_passive                   []
% 3.19/1.06  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.19/1.06  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.19/1.06  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.19/1.06  --sup_full_triv                         [TrivRules;PropSubs]
% 3.19/1.06  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.19/1.06  --sup_full_bw                           [BwDemod]
% 3.19/1.06  --sup_immed_triv                        [TrivRules]
% 3.19/1.06  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.19/1.06  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.19/1.06  --sup_immed_bw_main                     []
% 3.19/1.06  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.19/1.06  --sup_input_triv                        [Unflattening;TrivRules]
% 3.19/1.06  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.19/1.06  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.19/1.06  
% 3.19/1.06  ------ Combination Options
% 3.19/1.06  
% 3.19/1.06  --comb_res_mult                         3
% 3.19/1.06  --comb_sup_mult                         2
% 3.19/1.06  --comb_inst_mult                        10
% 3.19/1.06  
% 3.19/1.06  ------ Debug Options
% 3.19/1.06  
% 3.19/1.06  --dbg_backtrace                         false
% 3.19/1.06  --dbg_dump_prop_clauses                 false
% 3.19/1.06  --dbg_dump_prop_clauses_file            -
% 3.19/1.06  --dbg_out_stat                          false
% 3.19/1.06  ------ Parsing...
% 3.19/1.06  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.19/1.06  
% 3.19/1.06  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.19/1.06  
% 3.19/1.06  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.19/1.06  
% 3.19/1.06  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.19/1.06  ------ Proving...
% 3.19/1.06  ------ Problem Properties 
% 3.19/1.06  
% 3.19/1.06  
% 3.19/1.06  clauses                                 15
% 3.19/1.06  conjectures                             1
% 3.19/1.06  EPR                                     0
% 3.19/1.06  Horn                                    15
% 3.19/1.06  unary                                   6
% 3.19/1.06  binary                                  5
% 3.19/1.06  lits                                    28
% 3.19/1.06  lits eq                                 12
% 3.19/1.06  fd_pure                                 0
% 3.19/1.06  fd_pseudo                               0
% 3.19/1.06  fd_cond                                 0
% 3.19/1.06  fd_pseudo_cond                          0
% 3.19/1.06  AC symbols                              0
% 3.19/1.06  
% 3.19/1.06  ------ Schedule dynamic 5 is on 
% 3.19/1.06  
% 3.19/1.06  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.19/1.06  
% 3.19/1.06  
% 3.19/1.06  ------ 
% 3.19/1.06  Current options:
% 3.19/1.06  ------ 
% 3.19/1.06  
% 3.19/1.06  ------ Input Options
% 3.19/1.06  
% 3.19/1.06  --out_options                           all
% 3.19/1.06  --tptp_safe_out                         true
% 3.19/1.06  --problem_path                          ""
% 3.19/1.06  --include_path                          ""
% 3.19/1.06  --clausifier                            res/vclausify_rel
% 3.19/1.06  --clausifier_options                    --mode clausify
% 3.19/1.06  --stdin                                 false
% 3.19/1.06  --stats_out                             all
% 3.19/1.06  
% 3.19/1.06  ------ General Options
% 3.19/1.06  
% 3.19/1.06  --fof                                   false
% 3.19/1.06  --time_out_real                         305.
% 3.19/1.06  --time_out_virtual                      -1.
% 3.19/1.06  --symbol_type_check                     false
% 3.19/1.06  --clausify_out                          false
% 3.19/1.06  --sig_cnt_out                           false
% 3.19/1.06  --trig_cnt_out                          false
% 3.19/1.06  --trig_cnt_out_tolerance                1.
% 3.19/1.06  --trig_cnt_out_sk_spl                   false
% 3.19/1.06  --abstr_cl_out                          false
% 3.19/1.06  
% 3.19/1.06  ------ Global Options
% 3.19/1.06  
% 3.19/1.06  --schedule                              default
% 3.19/1.06  --add_important_lit                     false
% 3.19/1.06  --prop_solver_per_cl                    1000
% 3.19/1.06  --min_unsat_core                        false
% 3.19/1.06  --soft_assumptions                      false
% 3.19/1.06  --soft_lemma_size                       3
% 3.19/1.06  --prop_impl_unit_size                   0
% 3.19/1.06  --prop_impl_unit                        []
% 3.19/1.06  --share_sel_clauses                     true
% 3.19/1.06  --reset_solvers                         false
% 3.19/1.06  --bc_imp_inh                            [conj_cone]
% 3.19/1.06  --conj_cone_tolerance                   3.
% 3.19/1.06  --extra_neg_conj                        none
% 3.19/1.06  --large_theory_mode                     true
% 3.19/1.06  --prolific_symb_bound                   200
% 3.19/1.06  --lt_threshold                          2000
% 3.19/1.06  --clause_weak_htbl                      true
% 3.19/1.06  --gc_record_bc_elim                     false
% 3.19/1.06  
% 3.19/1.06  ------ Preprocessing Options
% 3.19/1.06  
% 3.19/1.06  --preprocessing_flag                    true
% 3.19/1.06  --time_out_prep_mult                    0.1
% 3.19/1.06  --splitting_mode                        input
% 3.19/1.06  --splitting_grd                         true
% 3.19/1.06  --splitting_cvd                         false
% 3.19/1.06  --splitting_cvd_svl                     false
% 3.19/1.06  --splitting_nvd                         32
% 3.19/1.06  --sub_typing                            true
% 3.19/1.06  --prep_gs_sim                           true
% 3.19/1.06  --prep_unflatten                        true
% 3.19/1.06  --prep_res_sim                          true
% 3.19/1.06  --prep_upred                            true
% 3.19/1.06  --prep_sem_filter                       exhaustive
% 3.19/1.06  --prep_sem_filter_out                   false
% 3.19/1.06  --pred_elim                             true
% 3.19/1.06  --res_sim_input                         true
% 3.19/1.06  --eq_ax_congr_red                       true
% 3.19/1.06  --pure_diseq_elim                       true
% 3.19/1.06  --brand_transform                       false
% 3.19/1.06  --non_eq_to_eq                          false
% 3.19/1.06  --prep_def_merge                        true
% 3.19/1.06  --prep_def_merge_prop_impl              false
% 3.19/1.06  --prep_def_merge_mbd                    true
% 3.19/1.06  --prep_def_merge_tr_red                 false
% 3.19/1.06  --prep_def_merge_tr_cl                  false
% 3.19/1.06  --smt_preprocessing                     true
% 3.19/1.06  --smt_ac_axioms                         fast
% 3.19/1.06  --preprocessed_out                      false
% 3.19/1.06  --preprocessed_stats                    false
% 3.19/1.06  
% 3.19/1.06  ------ Abstraction refinement Options
% 3.19/1.06  
% 3.19/1.06  --abstr_ref                             []
% 3.19/1.06  --abstr_ref_prep                        false
% 3.19/1.06  --abstr_ref_until_sat                   false
% 3.19/1.06  --abstr_ref_sig_restrict                funpre
% 3.19/1.06  --abstr_ref_af_restrict_to_split_sk     false
% 3.19/1.06  --abstr_ref_under                       []
% 3.19/1.06  
% 3.19/1.06  ------ SAT Options
% 3.19/1.06  
% 3.19/1.06  --sat_mode                              false
% 3.19/1.06  --sat_fm_restart_options                ""
% 3.19/1.06  --sat_gr_def                            false
% 3.19/1.06  --sat_epr_types                         true
% 3.19/1.06  --sat_non_cyclic_types                  false
% 3.19/1.06  --sat_finite_models                     false
% 3.19/1.06  --sat_fm_lemmas                         false
% 3.19/1.06  --sat_fm_prep                           false
% 3.19/1.06  --sat_fm_uc_incr                        true
% 3.19/1.06  --sat_out_model                         small
% 3.19/1.06  --sat_out_clauses                       false
% 3.19/1.06  
% 3.19/1.06  ------ QBF Options
% 3.19/1.06  
% 3.19/1.06  --qbf_mode                              false
% 3.19/1.06  --qbf_elim_univ                         false
% 3.19/1.06  --qbf_dom_inst                          none
% 3.19/1.06  --qbf_dom_pre_inst                      false
% 3.19/1.06  --qbf_sk_in                             false
% 3.19/1.06  --qbf_pred_elim                         true
% 3.19/1.06  --qbf_split                             512
% 3.19/1.06  
% 3.19/1.06  ------ BMC1 Options
% 3.19/1.06  
% 3.19/1.06  --bmc1_incremental                      false
% 3.19/1.06  --bmc1_axioms                           reachable_all
% 3.19/1.06  --bmc1_min_bound                        0
% 3.19/1.06  --bmc1_max_bound                        -1
% 3.19/1.06  --bmc1_max_bound_default                -1
% 3.19/1.06  --bmc1_symbol_reachability              true
% 3.19/1.06  --bmc1_property_lemmas                  false
% 3.19/1.06  --bmc1_k_induction                      false
% 3.19/1.06  --bmc1_non_equiv_states                 false
% 3.19/1.06  --bmc1_deadlock                         false
% 3.19/1.06  --bmc1_ucm                              false
% 3.19/1.06  --bmc1_add_unsat_core                   none
% 3.19/1.06  --bmc1_unsat_core_children              false
% 3.19/1.06  --bmc1_unsat_core_extrapolate_axioms    false
% 3.19/1.06  --bmc1_out_stat                         full
% 3.19/1.06  --bmc1_ground_init                      false
% 3.19/1.06  --bmc1_pre_inst_next_state              false
% 3.19/1.06  --bmc1_pre_inst_state                   false
% 3.19/1.06  --bmc1_pre_inst_reach_state             false
% 3.19/1.06  --bmc1_out_unsat_core                   false
% 3.19/1.06  --bmc1_aig_witness_out                  false
% 3.19/1.06  --bmc1_verbose                          false
% 3.19/1.06  --bmc1_dump_clauses_tptp                false
% 3.19/1.06  --bmc1_dump_unsat_core_tptp             false
% 3.19/1.06  --bmc1_dump_file                        -
% 3.19/1.06  --bmc1_ucm_expand_uc_limit              128
% 3.19/1.06  --bmc1_ucm_n_expand_iterations          6
% 3.19/1.06  --bmc1_ucm_extend_mode                  1
% 3.19/1.06  --bmc1_ucm_init_mode                    2
% 3.19/1.06  --bmc1_ucm_cone_mode                    none
% 3.19/1.06  --bmc1_ucm_reduced_relation_type        0
% 3.19/1.06  --bmc1_ucm_relax_model                  4
% 3.19/1.06  --bmc1_ucm_full_tr_after_sat            true
% 3.19/1.06  --bmc1_ucm_expand_neg_assumptions       false
% 3.19/1.06  --bmc1_ucm_layered_model                none
% 3.19/1.06  --bmc1_ucm_max_lemma_size               10
% 3.19/1.06  
% 3.19/1.06  ------ AIG Options
% 3.19/1.06  
% 3.19/1.06  --aig_mode                              false
% 3.19/1.06  
% 3.19/1.06  ------ Instantiation Options
% 3.19/1.06  
% 3.19/1.06  --instantiation_flag                    true
% 3.19/1.06  --inst_sos_flag                         false
% 3.19/1.06  --inst_sos_phase                        true
% 3.19/1.06  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.19/1.06  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.19/1.06  --inst_lit_sel_side                     none
% 3.19/1.06  --inst_solver_per_active                1400
% 3.19/1.06  --inst_solver_calls_frac                1.
% 3.19/1.06  --inst_passive_queue_type               priority_queues
% 3.19/1.06  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.19/1.06  --inst_passive_queues_freq              [25;2]
% 3.19/1.06  --inst_dismatching                      true
% 3.19/1.06  --inst_eager_unprocessed_to_passive     true
% 3.19/1.06  --inst_prop_sim_given                   true
% 3.19/1.06  --inst_prop_sim_new                     false
% 3.19/1.06  --inst_subs_new                         false
% 3.19/1.06  --inst_eq_res_simp                      false
% 3.19/1.06  --inst_subs_given                       false
% 3.19/1.06  --inst_orphan_elimination               true
% 3.19/1.06  --inst_learning_loop_flag               true
% 3.19/1.06  --inst_learning_start                   3000
% 3.19/1.06  --inst_learning_factor                  2
% 3.19/1.06  --inst_start_prop_sim_after_learn       3
% 3.19/1.06  --inst_sel_renew                        solver
% 3.19/1.06  --inst_lit_activity_flag                true
% 3.19/1.06  --inst_restr_to_given                   false
% 3.19/1.06  --inst_activity_threshold               500
% 3.19/1.06  --inst_out_proof                        true
% 3.19/1.06  
% 3.19/1.06  ------ Resolution Options
% 3.19/1.06  
% 3.19/1.06  --resolution_flag                       false
% 3.19/1.06  --res_lit_sel                           adaptive
% 3.19/1.06  --res_lit_sel_side                      none
% 3.19/1.06  --res_ordering                          kbo
% 3.19/1.06  --res_to_prop_solver                    active
% 3.19/1.06  --res_prop_simpl_new                    false
% 3.19/1.06  --res_prop_simpl_given                  true
% 3.19/1.06  --res_passive_queue_type                priority_queues
% 3.19/1.06  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.19/1.06  --res_passive_queues_freq               [15;5]
% 3.19/1.06  --res_forward_subs                      full
% 3.19/1.06  --res_backward_subs                     full
% 3.19/1.06  --res_forward_subs_resolution           true
% 3.19/1.06  --res_backward_subs_resolution          true
% 3.19/1.06  --res_orphan_elimination                true
% 3.19/1.06  --res_time_limit                        2.
% 3.19/1.06  --res_out_proof                         true
% 3.19/1.06  
% 3.19/1.06  ------ Superposition Options
% 3.19/1.06  
% 3.19/1.06  --superposition_flag                    true
% 3.19/1.06  --sup_passive_queue_type                priority_queues
% 3.19/1.06  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.19/1.06  --sup_passive_queues_freq               [8;1;4]
% 3.19/1.06  --demod_completeness_check              fast
% 3.19/1.06  --demod_use_ground                      true
% 3.19/1.06  --sup_to_prop_solver                    passive
% 3.19/1.06  --sup_prop_simpl_new                    true
% 3.19/1.06  --sup_prop_simpl_given                  true
% 3.19/1.06  --sup_fun_splitting                     false
% 3.19/1.06  --sup_smt_interval                      50000
% 3.19/1.06  
% 3.19/1.06  ------ Superposition Simplification Setup
% 3.19/1.06  
% 3.19/1.06  --sup_indices_passive                   []
% 3.19/1.06  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.19/1.06  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.19/1.06  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.19/1.06  --sup_full_triv                         [TrivRules;PropSubs]
% 3.19/1.06  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.19/1.06  --sup_full_bw                           [BwDemod]
% 3.19/1.06  --sup_immed_triv                        [TrivRules]
% 3.19/1.06  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.19/1.06  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.19/1.06  --sup_immed_bw_main                     []
% 3.19/1.06  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.19/1.06  --sup_input_triv                        [Unflattening;TrivRules]
% 3.19/1.06  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.19/1.06  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.19/1.06  
% 3.19/1.06  ------ Combination Options
% 3.19/1.06  
% 3.19/1.06  --comb_res_mult                         3
% 3.19/1.06  --comb_sup_mult                         2
% 3.19/1.06  --comb_inst_mult                        10
% 3.19/1.06  
% 3.19/1.06  ------ Debug Options
% 3.19/1.06  
% 3.19/1.06  --dbg_backtrace                         false
% 3.19/1.06  --dbg_dump_prop_clauses                 false
% 3.19/1.06  --dbg_dump_prop_clauses_file            -
% 3.19/1.06  --dbg_out_stat                          false
% 3.19/1.06  
% 3.19/1.06  
% 3.19/1.06  
% 3.19/1.06  
% 3.19/1.06  ------ Proving...
% 3.19/1.06  
% 3.19/1.06  
% 3.19/1.06  % SZS status Theorem for theBenchmark.p
% 3.19/1.06  
% 3.19/1.06   Resolution empty clause
% 3.19/1.06  
% 3.19/1.06  % SZS output start CNFRefutation for theBenchmark.p
% 3.19/1.06  
% 3.19/1.06  fof(f2,axiom,(
% 3.19/1.06    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 3.19/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.19/1.06  
% 3.19/1.06  fof(f38,plain,(
% 3.19/1.06    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 3.19/1.06    inference(cnf_transformation,[],[f2])).
% 3.19/1.06  
% 3.19/1.06  fof(f3,axiom,(
% 3.19/1.06    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.19/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.19/1.06  
% 3.19/1.06  fof(f39,plain,(
% 3.19/1.06    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.19/1.06    inference(cnf_transformation,[],[f3])).
% 3.19/1.06  
% 3.19/1.06  fof(f4,axiom,(
% 3.19/1.06    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.19/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.19/1.06  
% 3.19/1.06  fof(f40,plain,(
% 3.19/1.06    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.19/1.06    inference(cnf_transformation,[],[f4])).
% 3.19/1.06  
% 3.19/1.06  fof(f5,axiom,(
% 3.19/1.06    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.19/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.19/1.06  
% 3.19/1.06  fof(f41,plain,(
% 3.19/1.06    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.19/1.06    inference(cnf_transformation,[],[f5])).
% 3.19/1.06  
% 3.19/1.06  fof(f6,axiom,(
% 3.19/1.06    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 3.19/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.19/1.06  
% 3.19/1.06  fof(f42,plain,(
% 3.19/1.06    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 3.19/1.06    inference(cnf_transformation,[],[f6])).
% 3.19/1.06  
% 3.19/1.06  fof(f7,axiom,(
% 3.19/1.06    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 3.19/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.19/1.06  
% 3.19/1.06  fof(f43,plain,(
% 3.19/1.06    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 3.19/1.06    inference(cnf_transformation,[],[f7])).
% 3.19/1.06  
% 3.19/1.06  fof(f8,axiom,(
% 3.19/1.06    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 3.19/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.19/1.06  
% 3.19/1.06  fof(f44,plain,(
% 3.19/1.06    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 3.19/1.06    inference(cnf_transformation,[],[f8])).
% 3.19/1.06  
% 3.19/1.06  fof(f59,plain,(
% 3.19/1.06    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 3.19/1.06    inference(definition_unfolding,[],[f43,f44])).
% 3.19/1.06  
% 3.19/1.06  fof(f60,plain,(
% 3.19/1.06    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 3.19/1.06    inference(definition_unfolding,[],[f42,f59])).
% 3.19/1.06  
% 3.19/1.06  fof(f61,plain,(
% 3.19/1.06    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 3.19/1.06    inference(definition_unfolding,[],[f41,f60])).
% 3.19/1.06  
% 3.19/1.06  fof(f62,plain,(
% 3.19/1.06    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 3.19/1.06    inference(definition_unfolding,[],[f40,f61])).
% 3.19/1.06  
% 3.19/1.06  fof(f63,plain,(
% 3.19/1.06    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 3.19/1.06    inference(definition_unfolding,[],[f39,f62])).
% 3.19/1.06  
% 3.19/1.06  fof(f64,plain,(
% 3.19/1.06    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)) )),
% 3.19/1.06    inference(definition_unfolding,[],[f38,f63,f63])).
% 3.19/1.06  
% 3.19/1.06  fof(f11,axiom,(
% 3.19/1.06    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 3.19/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.19/1.06  
% 3.19/1.06  fof(f47,plain,(
% 3.19/1.06    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 3.19/1.06    inference(cnf_transformation,[],[f11])).
% 3.19/1.06  
% 3.19/1.06  fof(f19,axiom,(
% 3.19/1.06    ! [X0,X1] : (v1_relat_1(X1) => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)))),
% 3.19/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.19/1.06  
% 3.19/1.06  fof(f32,plain,(
% 3.19/1.06    ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 3.19/1.06    inference(ennf_transformation,[],[f19])).
% 3.19/1.06  
% 3.19/1.06  fof(f56,plain,(
% 3.19/1.06    ( ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 3.19/1.06    inference(cnf_transformation,[],[f32])).
% 3.19/1.06  
% 3.19/1.06  fof(f1,axiom,(
% 3.19/1.06    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 3.19/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.19/1.06  
% 3.19/1.06  fof(f37,plain,(
% 3.19/1.06    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 3.19/1.06    inference(cnf_transformation,[],[f1])).
% 3.19/1.06  
% 3.19/1.06  fof(f66,plain,(
% 3.19/1.06    ( ! [X0,X1] : (k4_xboole_0(k1_relat_1(X1),k4_xboole_0(k1_relat_1(X1),X0)) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 3.19/1.06    inference(definition_unfolding,[],[f56,f37])).
% 3.19/1.06  
% 3.19/1.06  fof(f15,axiom,(
% 3.19/1.06    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 3.19/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.19/1.06  
% 3.19/1.06  fof(f51,plain,(
% 3.19/1.06    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 3.19/1.06    inference(cnf_transformation,[],[f15])).
% 3.19/1.06  
% 3.19/1.06  fof(f9,axiom,(
% 3.19/1.06    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.19/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.19/1.06  
% 3.19/1.06  fof(f45,plain,(
% 3.19/1.06    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.19/1.06    inference(cnf_transformation,[],[f9])).
% 3.19/1.06  
% 3.19/1.06  fof(f65,plain,(
% 3.19/1.06    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 3.19/1.06    inference(definition_unfolding,[],[f45,f37,f63])).
% 3.19/1.06  
% 3.19/1.06  fof(f12,axiom,(
% 3.19/1.06    ! [X0,X1] : (v1_relat_1(X1) => k5_relat_1(X1,k6_relat_1(X0)) = k8_relat_1(X0,X1))),
% 3.19/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.19/1.06  
% 3.19/1.06  fof(f25,plain,(
% 3.19/1.06    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = k8_relat_1(X0,X1) | ~v1_relat_1(X1))),
% 3.19/1.06    inference(ennf_transformation,[],[f12])).
% 3.19/1.06  
% 3.19/1.06  fof(f48,plain,(
% 3.19/1.06    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = k8_relat_1(X0,X1) | ~v1_relat_1(X1)) )),
% 3.19/1.06    inference(cnf_transformation,[],[f25])).
% 3.19/1.06  
% 3.19/1.06  fof(f20,axiom,(
% 3.19/1.06    ! [X0,X1] : (v1_relat_1(X1) => k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0))),
% 3.19/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.19/1.06  
% 3.19/1.06  fof(f33,plain,(
% 3.19/1.06    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.19/1.06    inference(ennf_transformation,[],[f20])).
% 3.19/1.06  
% 3.19/1.06  fof(f57,plain,(
% 3.19/1.06    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.19/1.06    inference(cnf_transformation,[],[f33])).
% 3.19/1.06  
% 3.19/1.06  fof(f14,axiom,(
% 3.19/1.06    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))))),
% 3.19/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.19/1.06  
% 3.19/1.06  fof(f27,plain,(
% 3.19/1.06    ! [X0] : (! [X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.19/1.06    inference(ennf_transformation,[],[f14])).
% 3.19/1.06  
% 3.19/1.06  fof(f50,plain,(
% 3.19/1.06    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.19/1.06    inference(cnf_transformation,[],[f27])).
% 3.19/1.06  
% 3.19/1.06  fof(f52,plain,(
% 3.19/1.06    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 3.19/1.06    inference(cnf_transformation,[],[f15])).
% 3.19/1.06  
% 3.19/1.06  fof(f17,axiom,(
% 3.19/1.06    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 3.19/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.19/1.06  
% 3.19/1.06  fof(f29,plain,(
% 3.19/1.06    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.19/1.06    inference(ennf_transformation,[],[f17])).
% 3.19/1.06  
% 3.19/1.06  fof(f30,plain,(
% 3.19/1.06    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 3.19/1.06    inference(flattening,[],[f29])).
% 3.19/1.06  
% 3.19/1.06  fof(f54,plain,(
% 3.19/1.06    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 3.19/1.06    inference(cnf_transformation,[],[f30])).
% 3.19/1.06  
% 3.19/1.06  fof(f10,axiom,(
% 3.19/1.06    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 3.19/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.19/1.06  
% 3.19/1.06  fof(f23,plain,(
% 3.19/1.06    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 3.19/1.06    inference(ennf_transformation,[],[f10])).
% 3.19/1.06  
% 3.19/1.06  fof(f24,plain,(
% 3.19/1.06    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 3.19/1.06    inference(flattening,[],[f23])).
% 3.19/1.06  
% 3.19/1.06  fof(f46,plain,(
% 3.19/1.06    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.19/1.06    inference(cnf_transformation,[],[f24])).
% 3.19/1.06  
% 3.19/1.06  fof(f16,axiom,(
% 3.19/1.06    ! [X0] : (v1_relat_1(X0) => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0)),
% 3.19/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.19/1.06  
% 3.19/1.06  fof(f28,plain,(
% 3.19/1.06    ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0))),
% 3.19/1.06    inference(ennf_transformation,[],[f16])).
% 3.19/1.06  
% 3.19/1.06  fof(f53,plain,(
% 3.19/1.06    ( ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0)) )),
% 3.19/1.06    inference(cnf_transformation,[],[f28])).
% 3.19/1.06  
% 3.19/1.06  fof(f13,axiom,(
% 3.19/1.06    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(X1,k8_relat_1(X0,X2)) = k8_relat_1(X0,k5_relat_1(X1,X2))))),
% 3.19/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.19/1.06  
% 3.19/1.06  fof(f26,plain,(
% 3.19/1.06    ! [X0,X1] : (! [X2] : (k5_relat_1(X1,k8_relat_1(X0,X2)) = k8_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 3.19/1.06    inference(ennf_transformation,[],[f13])).
% 3.19/1.06  
% 3.19/1.06  fof(f49,plain,(
% 3.19/1.06    ( ! [X2,X0,X1] : (k5_relat_1(X1,k8_relat_1(X0,X2)) = k8_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 3.19/1.06    inference(cnf_transformation,[],[f26])).
% 3.19/1.06  
% 3.19/1.06  fof(f18,axiom,(
% 3.19/1.06    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 3.19/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.19/1.06  
% 3.19/1.06  fof(f31,plain,(
% 3.19/1.06    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 3.19/1.06    inference(ennf_transformation,[],[f18])).
% 3.19/1.06  
% 3.19/1.06  fof(f55,plain,(
% 3.19/1.06    ( ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 3.19/1.06    inference(cnf_transformation,[],[f31])).
% 3.19/1.06  
% 3.19/1.06  fof(f21,conjecture,(
% 3.19/1.06    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 3.19/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.19/1.06  
% 3.19/1.06  fof(f22,negated_conjecture,(
% 3.19/1.06    ~! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 3.19/1.06    inference(negated_conjecture,[],[f21])).
% 3.19/1.06  
% 3.19/1.06  fof(f34,plain,(
% 3.19/1.06    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))),
% 3.19/1.06    inference(ennf_transformation,[],[f22])).
% 3.19/1.06  
% 3.19/1.06  fof(f35,plain,(
% 3.19/1.06    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 3.19/1.06    introduced(choice_axiom,[])).
% 3.19/1.06  
% 3.19/1.06  fof(f36,plain,(
% 3.19/1.06    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 3.19/1.06    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f34,f35])).
% 3.19/1.06  
% 3.19/1.06  fof(f58,plain,(
% 3.19/1.06    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 3.19/1.06    inference(cnf_transformation,[],[f36])).
% 3.19/1.06  
% 3.19/1.06  fof(f67,plain,(
% 3.19/1.06    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 3.19/1.06    inference(definition_unfolding,[],[f58,f37])).
% 3.19/1.06  
% 3.19/1.06  cnf(c_0,plain,
% 3.19/1.06      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
% 3.19/1.06      inference(cnf_transformation,[],[f64]) ).
% 3.19/1.06  
% 3.19/1.06  cnf(c_3,plain,
% 3.19/1.06      ( v1_relat_1(k6_relat_1(X0)) ),
% 3.19/1.06      inference(cnf_transformation,[],[f47]) ).
% 3.19/1.06  
% 3.19/1.06  cnf(c_369,plain,
% 3.19/1.06      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 3.19/1.06      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.19/1.06  
% 3.19/1.06  cnf(c_12,plain,
% 3.19/1.06      ( ~ v1_relat_1(X0)
% 3.19/1.06      | k4_xboole_0(k1_relat_1(X0),k4_xboole_0(k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1)) ),
% 3.19/1.06      inference(cnf_transformation,[],[f66]) ).
% 3.19/1.06  
% 3.19/1.06  cnf(c_362,plain,
% 3.19/1.06      ( k4_xboole_0(k1_relat_1(X0),k4_xboole_0(k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1))
% 3.19/1.06      | v1_relat_1(X0) != iProver_top ),
% 3.19/1.06      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.19/1.06  
% 3.19/1.06  cnf(c_828,plain,
% 3.19/1.06      ( k4_xboole_0(k1_relat_1(k6_relat_1(X0)),k4_xboole_0(k1_relat_1(k6_relat_1(X0)),X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
% 3.19/1.06      inference(superposition,[status(thm)],[c_369,c_362]) ).
% 3.19/1.06  
% 3.19/1.06  cnf(c_8,plain,
% 3.19/1.06      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 3.19/1.06      inference(cnf_transformation,[],[f51]) ).
% 3.19/1.06  
% 3.19/1.06  cnf(c_829,plain,
% 3.19/1.06      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
% 3.19/1.06      inference(light_normalisation,[status(thm)],[c_828,c_8]) ).
% 3.19/1.06  
% 3.19/1.06  cnf(c_1,plain,
% 3.19/1.06      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 3.19/1.06      inference(cnf_transformation,[],[f65]) ).
% 3.19/1.06  
% 3.19/1.06  cnf(c_1014,plain,
% 3.19/1.06      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
% 3.19/1.06      inference(demodulation,[status(thm)],[c_829,c_1]) ).
% 3.19/1.06  
% 3.19/1.06  cnf(c_4,plain,
% 3.19/1.06      ( ~ v1_relat_1(X0) | k5_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X1,X0) ),
% 3.19/1.06      inference(cnf_transformation,[],[f48]) ).
% 3.19/1.06  
% 3.19/1.06  cnf(c_368,plain,
% 3.19/1.06      ( k5_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X1,X0)
% 3.19/1.06      | v1_relat_1(X0) != iProver_top ),
% 3.19/1.06      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.19/1.06  
% 3.19/1.06  cnf(c_1480,plain,
% 3.19/1.06      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k8_relat_1(X1,k6_relat_1(X0)) ),
% 3.19/1.06      inference(superposition,[status(thm)],[c_369,c_368]) ).
% 3.19/1.06  
% 3.19/1.06  cnf(c_13,plain,
% 3.19/1.06      ( ~ v1_relat_1(X0) | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
% 3.19/1.06      inference(cnf_transformation,[],[f57]) ).
% 3.19/1.06  
% 3.19/1.06  cnf(c_361,plain,
% 3.19/1.06      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
% 3.19/1.06      | v1_relat_1(X1) != iProver_top ),
% 3.19/1.06      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.19/1.06  
% 3.19/1.06  cnf(c_695,plain,
% 3.19/1.06      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
% 3.19/1.06      inference(superposition,[status(thm)],[c_369,c_361]) ).
% 3.19/1.06  
% 3.19/1.06  cnf(c_1483,plain,
% 3.19/1.06      ( k7_relat_1(k6_relat_1(X0),X1) = k8_relat_1(X0,k6_relat_1(X1)) ),
% 3.19/1.06      inference(demodulation,[status(thm)],[c_1480,c_695]) ).
% 3.19/1.06  
% 3.19/1.06  cnf(c_1995,plain,
% 3.19/1.06      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))) ),
% 3.19/1.06      inference(light_normalisation,[status(thm)],[c_1014,c_1483]) ).
% 3.19/1.06  
% 3.19/1.06  cnf(c_1999,plain,
% 3.19/1.06      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))) ),
% 3.19/1.06      inference(superposition,[status(thm)],[c_0,c_1995]) ).
% 3.19/1.06  
% 3.19/1.06  cnf(c_2270,plain,
% 3.19/1.06      ( k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))) = k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))) ),
% 3.19/1.06      inference(superposition,[status(thm)],[c_1999,c_1995]) ).
% 3.19/1.06  
% 3.19/1.06  cnf(c_6,plain,
% 3.19/1.06      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
% 3.19/1.06      | ~ v1_relat_1(X1)
% 3.19/1.06      | ~ v1_relat_1(X0) ),
% 3.19/1.06      inference(cnf_transformation,[],[f50]) ).
% 3.19/1.06  
% 3.19/1.06  cnf(c_366,plain,
% 3.19/1.06      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) = iProver_top
% 3.19/1.06      | v1_relat_1(X0) != iProver_top
% 3.19/1.06      | v1_relat_1(X1) != iProver_top ),
% 3.19/1.06      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.19/1.06  
% 3.19/1.06  cnf(c_3727,plain,
% 3.19/1.06      ( r1_tarski(k1_relat_1(k5_relat_1(k6_relat_1(X0),X1)),X0) = iProver_top
% 3.19/1.06      | v1_relat_1(X1) != iProver_top
% 3.19/1.06      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 3.19/1.06      inference(superposition,[status(thm)],[c_8,c_366]) ).
% 3.19/1.06  
% 3.19/1.06  cnf(c_41,plain,
% 3.19/1.06      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 3.19/1.06      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.19/1.06  
% 3.19/1.06  cnf(c_3870,plain,
% 3.19/1.06      ( v1_relat_1(X1) != iProver_top
% 3.19/1.06      | r1_tarski(k1_relat_1(k5_relat_1(k6_relat_1(X0),X1)),X0) = iProver_top ),
% 3.19/1.06      inference(global_propositional_subsumption,[status(thm)],[c_3727,c_41]) ).
% 3.19/1.06  
% 3.19/1.06  cnf(c_3871,plain,
% 3.19/1.06      ( r1_tarski(k1_relat_1(k5_relat_1(k6_relat_1(X0),X1)),X0) = iProver_top
% 3.19/1.06      | v1_relat_1(X1) != iProver_top ),
% 3.19/1.06      inference(renaming,[status(thm)],[c_3870]) ).
% 3.19/1.06  
% 3.19/1.06  cnf(c_3878,plain,
% 3.19/1.06      ( r1_tarski(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))),X1) = iProver_top
% 3.19/1.06      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 3.19/1.06      inference(superposition,[status(thm)],[c_1480,c_3871]) ).
% 3.19/1.06  
% 3.19/1.06  cnf(c_4045,plain,
% 3.19/1.06      ( r1_tarski(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))),X1) = iProver_top ),
% 3.19/1.06      inference(global_propositional_subsumption,[status(thm)],[c_3878,c_41]) ).
% 3.19/1.06  
% 3.19/1.06  cnf(c_4052,plain,
% 3.19/1.06      ( r1_tarski(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))),X0) = iProver_top ),
% 3.19/1.06      inference(superposition,[status(thm)],[c_2270,c_4045]) ).
% 3.19/1.06  
% 3.19/1.06  cnf(c_7,plain,
% 3.19/1.06      ( k2_relat_1(k6_relat_1(X0)) = X0 ),
% 3.19/1.06      inference(cnf_transformation,[],[f52]) ).
% 3.19/1.06  
% 3.19/1.06  cnf(c_10,plain,
% 3.19/1.06      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 3.19/1.06      | ~ v1_relat_1(X0)
% 3.19/1.06      | k5_relat_1(X0,k6_relat_1(X1)) = X0 ),
% 3.19/1.06      inference(cnf_transformation,[],[f54]) ).
% 3.19/1.06  
% 3.19/1.06  cnf(c_364,plain,
% 3.19/1.06      ( k5_relat_1(X0,k6_relat_1(X1)) = X0
% 3.19/1.06      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 3.19/1.06      | v1_relat_1(X0) != iProver_top ),
% 3.19/1.06      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.19/1.06  
% 3.19/1.06  cnf(c_1893,plain,
% 3.19/1.06      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k6_relat_1(X0)
% 3.19/1.06      | r1_tarski(X0,X1) != iProver_top
% 3.19/1.06      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 3.19/1.06      inference(superposition,[status(thm)],[c_7,c_364]) ).
% 3.19/1.06  
% 3.19/1.06  cnf(c_1894,plain,
% 3.19/1.06      ( k8_relat_1(X0,k6_relat_1(X1)) = k6_relat_1(X1)
% 3.19/1.06      | r1_tarski(X1,X0) != iProver_top
% 3.19/1.06      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 3.19/1.06      inference(demodulation,[status(thm)],[c_1893,c_1480]) ).
% 3.19/1.06  
% 3.19/1.06  cnf(c_5423,plain,
% 3.19/1.06      ( k8_relat_1(X0,k6_relat_1(X1)) = k6_relat_1(X1)
% 3.19/1.06      | r1_tarski(X1,X0) != iProver_top ),
% 3.19/1.06      inference(forward_subsumption_resolution,[status(thm)],[c_1894,c_369]) ).
% 3.19/1.06  
% 3.19/1.06  cnf(c_5429,plain,
% 3.19/1.06      ( k8_relat_1(X0,k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))))) = k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))) ),
% 3.19/1.06      inference(superposition,[status(thm)],[c_4052,c_5423]) ).
% 3.19/1.06  
% 3.19/1.06  cnf(c_2,plain,
% 3.19/1.06      ( ~ v1_relat_1(X0) | ~ v1_relat_1(X1) | v1_relat_1(k5_relat_1(X1,X0)) ),
% 3.19/1.06      inference(cnf_transformation,[],[f46]) ).
% 3.19/1.06  
% 3.19/1.06  cnf(c_370,plain,
% 3.19/1.06      ( v1_relat_1(X0) != iProver_top
% 3.19/1.06      | v1_relat_1(X1) != iProver_top
% 3.19/1.06      | v1_relat_1(k5_relat_1(X1,X0)) = iProver_top ),
% 3.19/1.06      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.19/1.06  
% 3.19/1.06  cnf(c_2278,plain,
% 3.19/1.06      ( v1_relat_1(k8_relat_1(X0,k6_relat_1(X1))) = iProver_top
% 3.19/1.06      | v1_relat_1(k6_relat_1(X0)) != iProver_top
% 3.19/1.06      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 3.19/1.06      inference(superposition,[status(thm)],[c_1480,c_370]) ).
% 3.19/1.06  
% 3.19/1.06  cnf(c_5506,plain,
% 3.19/1.06      ( v1_relat_1(k8_relat_1(X0,k6_relat_1(X1))) = iProver_top
% 3.19/1.06      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 3.19/1.06      inference(global_propositional_subsumption,[status(thm)],[c_2278,c_41]) ).
% 3.19/1.06  
% 3.19/1.06  cnf(c_5512,plain,
% 3.19/1.06      ( v1_relat_1(k8_relat_1(X0,k6_relat_1(X1))) = iProver_top ),
% 3.19/1.06      inference(forward_subsumption_resolution,[status(thm)],[c_5506,c_369]) ).
% 3.19/1.06  
% 3.19/1.06  cnf(c_9,plain,
% 3.19/1.06      ( ~ v1_relat_1(X0) | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ),
% 3.19/1.06      inference(cnf_transformation,[],[f53]) ).
% 3.19/1.06  
% 3.19/1.06  cnf(c_365,plain,
% 3.19/1.06      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
% 3.19/1.06      | v1_relat_1(X0) != iProver_top ),
% 3.19/1.06      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.19/1.06  
% 3.19/1.06  cnf(c_5521,plain,
% 3.19/1.06      ( k5_relat_1(k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))),k8_relat_1(X0,k6_relat_1(X1))) = k8_relat_1(X0,k6_relat_1(X1)) ),
% 3.19/1.06      inference(superposition,[status(thm)],[c_5512,c_365]) ).
% 3.19/1.06  
% 3.19/1.06  cnf(c_7444,plain,
% 3.19/1.06      ( k5_relat_1(k6_relat_1(k1_relat_1(k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))))),k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))))) = k8_relat_1(X0,k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))))) ),
% 3.19/1.06      inference(superposition,[status(thm)],[c_5429,c_5521]) ).
% 3.19/1.06  
% 3.19/1.06  cnf(c_5,plain,
% 3.19/1.06      ( ~ v1_relat_1(X0)
% 3.19/1.06      | ~ v1_relat_1(X1)
% 3.19/1.06      | k8_relat_1(X2,k5_relat_1(X0,X1)) = k5_relat_1(X0,k8_relat_1(X2,X1)) ),
% 3.19/1.06      inference(cnf_transformation,[],[f49]) ).
% 3.19/1.06  
% 3.19/1.06  cnf(c_367,plain,
% 3.19/1.06      ( k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2))
% 3.19/1.06      | v1_relat_1(X1) != iProver_top
% 3.19/1.06      | v1_relat_1(X2) != iProver_top ),
% 3.19/1.06      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.19/1.06  
% 3.19/1.06  cnf(c_4025,plain,
% 3.19/1.06      ( k8_relat_1(X0,k5_relat_1(k6_relat_1(X1),X2)) = k5_relat_1(k6_relat_1(X1),k8_relat_1(X0,X2))
% 3.19/1.06      | v1_relat_1(X2) != iProver_top ),
% 3.19/1.06      inference(superposition,[status(thm)],[c_369,c_367]) ).
% 3.19/1.06  
% 3.19/1.06  cnf(c_5491,plain,
% 3.19/1.06      ( k8_relat_1(X0,k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) = k5_relat_1(k6_relat_1(X1),k8_relat_1(X0,k6_relat_1(X2))) ),
% 3.19/1.06      inference(superposition,[status(thm)],[c_369,c_4025]) ).
% 3.19/1.06  
% 3.19/1.06  cnf(c_5493,plain,
% 3.19/1.06      ( k5_relat_1(k6_relat_1(X0),k8_relat_1(X1,k6_relat_1(X2))) = k8_relat_1(X1,k8_relat_1(X2,k6_relat_1(X0))) ),
% 3.19/1.06      inference(demodulation,[status(thm)],[c_5491,c_1480]) ).
% 3.19/1.06  
% 3.19/1.06  cnf(c_7452,plain,
% 3.19/1.06      ( k8_relat_1(X0,k8_relat_1(X1,k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))))) = k8_relat_1(X0,k6_relat_1(X1)) ),
% 3.19/1.06      inference(superposition,[status(thm)],[c_5521,c_5493]) ).
% 3.19/1.06  
% 3.19/1.06  cnf(c_5744,plain,
% 3.19/1.06      ( k8_relat_1(X0,k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))))) = k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))) ),
% 3.19/1.06      inference(superposition,[status(thm)],[c_2270,c_5429]) ).
% 3.19/1.06  
% 3.19/1.06  cnf(c_7454,plain,
% 3.19/1.06      ( k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))) = k8_relat_1(X0,k6_relat_1(X1)) ),
% 3.19/1.06      inference(demodulation,[status(thm)],[c_7452,c_5744]) ).
% 3.19/1.06  
% 3.19/1.06  cnf(c_5428,plain,
% 3.19/1.06      ( k8_relat_1(X0,k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))))) = k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0)))) ),
% 3.19/1.06      inference(superposition,[status(thm)],[c_4045,c_5423]) ).
% 3.19/1.06  
% 3.19/1.06  cnf(c_5683,plain,
% 3.19/1.06      ( k8_relat_1(X0,k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))))) = k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0)))) ),
% 3.19/1.06      inference(superposition,[status(thm)],[c_2270,c_5428]) ).
% 3.19/1.06  
% 3.19/1.06  cnf(c_7470,plain,
% 3.19/1.06      ( k8_relat_1(X0,k8_relat_1(X0,k6_relat_1(X1))) = k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0)))) ),
% 3.19/1.06      inference(demodulation,[status(thm)],[c_7454,c_5683]) ).
% 3.19/1.06  
% 3.19/1.06  cnf(c_11,plain,
% 3.19/1.06      ( ~ v1_relat_1(X0) | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ),
% 3.19/1.06      inference(cnf_transformation,[],[f55]) ).
% 3.19/1.06  
% 3.19/1.06  cnf(c_363,plain,
% 3.19/1.06      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
% 3.19/1.06      | v1_relat_1(X0) != iProver_top ),
% 3.19/1.06      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.19/1.06  
% 3.19/1.06  cnf(c_566,plain,
% 3.19/1.06      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(k2_relat_1(k6_relat_1(X0)))) = k6_relat_1(X0) ),
% 3.19/1.06      inference(superposition,[status(thm)],[c_369,c_363]) ).
% 3.19/1.06  
% 3.19/1.06  cnf(c_567,plain,
% 3.19/1.06      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X0)) = k6_relat_1(X0) ),
% 3.19/1.06      inference(light_normalisation,[status(thm)],[c_566,c_7]) ).
% 3.19/1.06  
% 3.19/1.06  cnf(c_1485,plain,
% 3.19/1.06      ( k8_relat_1(X0,k6_relat_1(X0)) = k6_relat_1(X0) ),
% 3.19/1.06      inference(superposition,[status(thm)],[c_567,c_1480]) ).
% 3.19/1.06  
% 3.19/1.06  cnf(c_5616,plain,
% 3.19/1.06      ( k8_relat_1(X0,k8_relat_1(X0,k6_relat_1(X1))) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
% 3.19/1.06      inference(superposition,[status(thm)],[c_1485,c_5493]) ).
% 3.19/1.06  
% 3.19/1.06  cnf(c_5639,plain,
% 3.19/1.06      ( k8_relat_1(X0,k8_relat_1(X0,k6_relat_1(X1))) = k8_relat_1(X0,k6_relat_1(X1)) ),
% 3.19/1.06      inference(demodulation,[status(thm)],[c_5616,c_1480]) ).
% 3.19/1.06  
% 3.19/1.06  cnf(c_7477,plain,
% 3.19/1.06      ( k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))) = k8_relat_1(X1,k6_relat_1(X0)) ),
% 3.19/1.06      inference(light_normalisation,[status(thm)],[c_7470,c_5639]) ).
% 3.19/1.06  
% 3.19/1.06  cnf(c_7489,plain,
% 3.19/1.06      ( k8_relat_1(X0,k8_relat_1(X1,k8_relat_1(X1,k6_relat_1(X0)))) = k8_relat_1(X0,k6_relat_1(X1)) ),
% 3.19/1.06      inference(light_normalisation,[status(thm)],[c_7452,c_7477]) ).
% 3.19/1.06  
% 3.19/1.06  cnf(c_7491,plain,
% 3.19/1.06      ( k8_relat_1(X0,k8_relat_1(X1,k6_relat_1(X0))) = k8_relat_1(X0,k6_relat_1(X1)) ),
% 3.19/1.06      inference(demodulation,[status(thm)],[c_7489,c_5639]) ).
% 3.19/1.06  
% 3.19/1.06  cnf(c_7511,plain,
% 3.19/1.06      ( k5_relat_1(k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))),k8_relat_1(X0,k6_relat_1(X1))) = k8_relat_1(X1,k6_relat_1(X0)) ),
% 3.19/1.06      inference(light_normalisation,[status(thm)],[c_7444,c_7477,c_7491]) ).
% 3.19/1.06  
% 3.19/1.06  cnf(c_7446,plain,
% 3.19/1.06      ( k5_relat_1(k6_relat_1(k1_relat_1(k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))))),k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))))) = k8_relat_1(X1,k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))))) ),
% 3.19/1.06      inference(superposition,[status(thm)],[c_5428,c_5521]) ).
% 3.19/1.06  
% 3.19/1.06  cnf(c_7502,plain,
% 3.19/1.06      ( k5_relat_1(k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))),k8_relat_1(X0,k6_relat_1(X1))) = k8_relat_1(X0,k8_relat_1(X0,k6_relat_1(X1))) ),
% 3.19/1.06      inference(light_normalisation,[status(thm)],[c_7446,c_7477]) ).
% 3.19/1.06  
% 3.19/1.06  cnf(c_7503,plain,
% 3.19/1.06      ( k5_relat_1(k8_relat_1(X0,k6_relat_1(X1)),k8_relat_1(X1,k6_relat_1(X0))) = k8_relat_1(X1,k8_relat_1(X1,k6_relat_1(X0))) ),
% 3.19/1.06      inference(demodulation,[status(thm)],[c_7502,c_7477]) ).
% 3.19/1.06  
% 3.19/1.06  cnf(c_7505,plain,
% 3.19/1.06      ( k5_relat_1(k8_relat_1(X0,k6_relat_1(X1)),k8_relat_1(X1,k6_relat_1(X0))) = k8_relat_1(X1,k6_relat_1(X0)) ),
% 3.19/1.06      inference(demodulation,[status(thm)],[c_7503,c_5639]) ).
% 3.19/1.06  
% 3.19/1.06  cnf(c_7512,plain,
% 3.19/1.06      ( k8_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X1,k6_relat_1(X0)) ),
% 3.19/1.06      inference(demodulation,[status(thm)],[c_7511,c_7477,c_7505]) ).
% 3.19/1.06  
% 3.19/1.06  cnf(c_14,negated_conjecture,
% 3.19/1.06      ( k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
% 3.19/1.06      inference(cnf_transformation,[],[f67]) ).
% 3.19/1.06  
% 3.19/1.06  cnf(c_1016,plain,
% 3.19/1.06      ( k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(sK0),sK1))) != k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) ),
% 3.19/1.06      inference(demodulation,[status(thm)],[c_829,c_14]) ).
% 3.19/1.06  
% 3.19/1.06  cnf(c_1114,plain,
% 3.19/1.06      ( k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(sK0),sK1))) != k7_relat_1(k6_relat_1(sK0),sK1) ),
% 3.19/1.06      inference(demodulation,[status(thm)],[c_695,c_1016]) ).
% 3.19/1.06  
% 3.19/1.06  cnf(c_1686,plain,
% 3.19/1.06      ( k6_relat_1(k1_relat_1(k8_relat_1(sK0,k6_relat_1(sK1)))) != k8_relat_1(sK0,k6_relat_1(sK1)) ),
% 3.19/1.06      inference(demodulation,[status(thm)],[c_1483,c_1114]) ).
% 3.19/1.06  
% 3.19/1.06  cnf(c_3472,plain,
% 3.19/1.06      ( k6_relat_1(k1_relat_1(k8_relat_1(sK1,k6_relat_1(sK0)))) != k8_relat_1(sK0,k6_relat_1(sK1)) ),
% 3.19/1.06      inference(demodulation,[status(thm)],[c_2270,c_1686]) ).
% 3.19/1.06  
% 3.19/1.06  cnf(c_7464,plain,
% 3.19/1.06      ( k8_relat_1(sK1,k6_relat_1(sK0)) != k8_relat_1(sK0,k6_relat_1(sK1)) ),
% 3.19/1.06      inference(demodulation,[status(thm)],[c_7454,c_3472]) ).
% 3.19/1.06  
% 3.19/1.06  cnf(c_7514,plain,
% 3.19/1.06      ( k8_relat_1(sK1,k6_relat_1(sK0)) != k8_relat_1(sK1,k6_relat_1(sK0)) ),
% 3.19/1.06      inference(demodulation,[status(thm)],[c_7512,c_7464]) ).
% 3.19/1.06  
% 3.19/1.06  cnf(c_7516,plain,
% 3.19/1.06      ( $false ),
% 3.19/1.06      inference(equality_resolution_simp,[status(thm)],[c_7514]) ).
% 3.19/1.06  
% 3.19/1.06  
% 3.19/1.06  % SZS output end CNFRefutation for theBenchmark.p
% 3.19/1.06  
% 3.19/1.06  ------                               Statistics
% 3.19/1.06  
% 3.19/1.06  ------ General
% 3.19/1.06  
% 3.19/1.06  abstr_ref_over_cycles:                  0
% 3.19/1.06  abstr_ref_under_cycles:                 0
% 3.19/1.06  gc_basic_clause_elim:                   0
% 3.19/1.06  forced_gc_time:                         0
% 3.19/1.06  parsing_time:                           0.01
% 3.19/1.06  unif_index_cands_time:                  0.
% 3.19/1.06  unif_index_add_time:                    0.
% 3.19/1.06  orderings_time:                         0.
% 3.19/1.06  out_proof_time:                         0.01
% 3.19/1.06  total_time:                             0.216
% 3.19/1.06  num_of_symbols:                         44
% 3.19/1.06  num_of_terms:                           11717
% 3.19/1.06  
% 3.19/1.06  ------ Preprocessing
% 3.19/1.06  
% 3.19/1.06  num_of_splits:                          0
% 3.19/1.06  num_of_split_atoms:                     0
% 3.19/1.06  num_of_reused_defs:                     0
% 3.19/1.06  num_eq_ax_congr_red:                    22
% 3.19/1.06  num_of_sem_filtered_clauses:            1
% 3.19/1.06  num_of_subtypes:                        0
% 3.19/1.06  monotx_restored_types:                  0
% 3.19/1.06  sat_num_of_epr_types:                   0
% 3.19/1.06  sat_num_of_non_cyclic_types:            0
% 3.19/1.06  sat_guarded_non_collapsed_types:        0
% 3.19/1.06  num_pure_diseq_elim:                    0
% 3.19/1.06  simp_replaced_by:                       0
% 3.19/1.06  res_preprocessed:                       68
% 3.19/1.06  prep_upred:                             0
% 3.19/1.06  prep_unflattend:                        1
% 3.19/1.06  smt_new_axioms:                         0
% 3.19/1.06  pred_elim_cands:                        2
% 3.19/1.06  pred_elim:                              0
% 3.19/1.06  pred_elim_cl:                           0
% 3.19/1.06  pred_elim_cycles:                       1
% 3.19/1.06  merged_defs:                            0
% 3.19/1.06  merged_defs_ncl:                        0
% 3.19/1.06  bin_hyper_res:                          0
% 3.19/1.06  prep_cycles:                            3
% 3.19/1.06  pred_elim_time:                         0.
% 3.19/1.06  splitting_time:                         0.
% 3.19/1.06  sem_filter_time:                        0.
% 3.19/1.06  monotx_time:                            0.
% 3.19/1.06  subtype_inf_time:                       0.
% 3.19/1.06  
% 3.19/1.06  ------ Problem properties
% 3.19/1.06  
% 3.19/1.06  clauses:                                15
% 3.19/1.06  conjectures:                            1
% 3.19/1.06  epr:                                    0
% 3.19/1.06  horn:                                   15
% 3.19/1.06  ground:                                 1
% 3.19/1.06  unary:                                  6
% 3.19/1.06  binary:                                 5
% 3.19/1.06  lits:                                   28
% 3.19/1.06  lits_eq:                                12
% 3.19/1.06  fd_pure:                                0
% 3.19/1.06  fd_pseudo:                              0
% 3.19/1.06  fd_cond:                                0
% 3.19/1.06  fd_pseudo_cond:                         0
% 3.19/1.06  ac_symbols:                             0
% 3.19/1.06  
% 3.19/1.06  ------ Propositional Solver
% 3.19/1.06  
% 3.19/1.06  prop_solver_calls:                      24
% 3.19/1.06  prop_fast_solver_calls:                 400
% 3.19/1.06  smt_solver_calls:                       0
% 3.19/1.06  smt_fast_solver_calls:                  0
% 3.19/1.06  prop_num_of_clauses:                    3497
% 3.19/1.06  prop_preprocess_simplified:             6827
% 3.19/1.06  prop_fo_subsumed:                       4
% 3.19/1.06  prop_solver_time:                       0.
% 3.19/1.06  smt_solver_time:                        0.
% 3.19/1.06  smt_fast_solver_time:                   0.
% 3.19/1.06  prop_fast_solver_time:                  0.
% 3.19/1.06  prop_unsat_core_time:                   0.
% 3.19/1.06  
% 3.19/1.06  ------ QBF
% 3.19/1.06  
% 3.19/1.06  qbf_q_res:                              0
% 3.19/1.06  qbf_num_tautologies:                    0
% 3.19/1.06  qbf_prep_cycles:                        0
% 3.19/1.06  
% 3.19/1.06  ------ BMC1
% 3.19/1.06  
% 3.19/1.06  bmc1_current_bound:                     -1
% 3.19/1.06  bmc1_last_solved_bound:                 -1
% 3.19/1.06  bmc1_unsat_core_size:                   -1
% 3.19/1.06  bmc1_unsat_core_parents_size:           -1
% 3.19/1.06  bmc1_merge_next_fun:                    0
% 3.19/1.06  bmc1_unsat_core_clauses_time:           0.
% 3.19/1.06  
% 3.19/1.06  ------ Instantiation
% 3.19/1.06  
% 3.19/1.06  inst_num_of_clauses:                    986
% 3.19/1.06  inst_num_in_passive:                    185
% 3.19/1.06  inst_num_in_active:                     340
% 3.19/1.06  inst_num_in_unprocessed:                461
% 3.19/1.06  inst_num_of_loops:                      380
% 3.19/1.06  inst_num_of_learning_restarts:          0
% 3.19/1.06  inst_num_moves_active_passive:          39
% 3.19/1.06  inst_lit_activity:                      0
% 3.19/1.06  inst_lit_activity_moves:                1
% 3.19/1.06  inst_num_tautologies:                   0
% 3.19/1.06  inst_num_prop_implied:                  0
% 3.19/1.06  inst_num_existing_simplified:           0
% 3.19/1.06  inst_num_eq_res_simplified:             0
% 3.19/1.06  inst_num_child_elim:                    0
% 3.19/1.06  inst_num_of_dismatching_blockings:      256
% 3.19/1.06  inst_num_of_non_proper_insts:           510
% 3.19/1.06  inst_num_of_duplicates:                 0
% 3.19/1.06  inst_inst_num_from_inst_to_res:         0
% 3.19/1.06  inst_dismatching_checking_time:         0.
% 3.19/1.06  
% 3.19/1.06  ------ Resolution
% 3.19/1.06  
% 3.19/1.06  res_num_of_clauses:                     0
% 3.19/1.06  res_num_in_passive:                     0
% 3.19/1.06  res_num_in_active:                      0
% 3.19/1.06  res_num_of_loops:                       71
% 3.19/1.06  res_forward_subset_subsumed:            57
% 3.19/1.06  res_backward_subset_subsumed:           0
% 3.19/1.06  res_forward_subsumed:                   0
% 3.19/1.06  res_backward_subsumed:                  0
% 3.19/1.06  res_forward_subsumption_resolution:     0
% 3.19/1.06  res_backward_subsumption_resolution:    0
% 3.19/1.06  res_clause_to_clause_subsumption:       1002
% 3.19/1.06  res_orphan_elimination:                 0
% 3.19/1.06  res_tautology_del:                      40
% 3.19/1.06  res_num_eq_res_simplified:              0
% 3.19/1.06  res_num_sel_changes:                    0
% 3.19/1.06  res_moves_from_active_to_pass:          0
% 3.19/1.06  
% 3.19/1.06  ------ Superposition
% 3.19/1.06  
% 3.19/1.06  sup_time_total:                         0.
% 3.19/1.06  sup_time_generating:                    0.
% 3.19/1.06  sup_time_sim_full:                      0.
% 3.19/1.06  sup_time_sim_immed:                     0.
% 3.19/1.06  
% 3.19/1.06  sup_num_of_clauses:                     183
% 3.19/1.06  sup_num_in_active:                      52
% 3.19/1.06  sup_num_in_passive:                     131
% 3.19/1.06  sup_num_of_loops:                       75
% 3.19/1.06  sup_fw_superposition:                   389
% 3.19/1.06  sup_bw_superposition:                   373
% 3.19/1.06  sup_immediate_simplified:               345
% 3.19/1.06  sup_given_eliminated:                   1
% 3.19/1.06  comparisons_done:                       0
% 3.19/1.06  comparisons_avoided:                    0
% 3.19/1.06  
% 3.19/1.06  ------ Simplifications
% 3.19/1.06  
% 3.19/1.06  
% 3.19/1.06  sim_fw_subset_subsumed:                 3
% 3.19/1.06  sim_bw_subset_subsumed:                 2
% 3.19/1.06  sim_fw_subsumed:                        70
% 3.19/1.06  sim_bw_subsumed:                        0
% 3.19/1.06  sim_fw_subsumption_res:                 2
% 3.19/1.06  sim_bw_subsumption_res:                 0
% 3.19/1.06  sim_tautology_del:                      2
% 3.19/1.06  sim_eq_tautology_del:                   82
% 3.19/1.06  sim_eq_res_simp:                        0
% 3.19/1.06  sim_fw_demodulated:                     155
% 3.19/1.06  sim_bw_demodulated:                     27
% 3.19/1.06  sim_light_normalised:                   232
% 3.19/1.06  sim_joinable_taut:                      0
% 3.19/1.06  sim_joinable_simp:                      0
% 3.19/1.06  sim_ac_normalised:                      0
% 3.19/1.06  sim_smt_subsumption:                    0
% 3.19/1.06  
%------------------------------------------------------------------------------
