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
% DateTime   : Thu Dec  3 11:50:06 EST 2020

% Result     : Theorem 0.38s
% Output     : CNFRefutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :  165 (10839 expanded)
%              Number of clauses        :   98 (4970 expanded)
%              Number of leaves         :   22 (2235 expanded)
%              Depth                    :   28
%              Number of atoms          :  251 (16788 expanded)
%              Number of equality atoms :  181 (9229 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    7 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f2,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f7])).

fof(f65,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f46,f47])).

fof(f66,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f45,f65])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f44,f66])).

fof(f68,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f43,f67])).

fof(f69,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f42,f68])).

fof(f70,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f48,f69])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k6_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X0)) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f62,f70])).

fof(f16,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f71,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f41,f70])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k5_relat_1(k6_relat_1(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f26,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f17,axiom,(
    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k5_relat_1(X1,k6_relat_1(X0)) = k8_relat_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = k8_relat_1(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = k8_relat_1(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k5_relat_1(X1,k8_relat_1(X0,X2)) = k8_relat_1(X0,k5_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k5_relat_1(X1,k8_relat_1(X0,X2)) = k8_relat_1(X0,k5_relat_1(X1,X2))
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X1,k8_relat_1(X0,X2)) = k8_relat_1(X0,k5_relat_1(X1,X2))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f20,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f61,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f57,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f19,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f60,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f23,conjecture,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f23])).

fof(f38,plain,(
    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f24])).

fof(f39,plain,
    ( ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))
   => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f38,f39])).

fof(f64,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f40])).

fof(f73,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) ),
    inference(definition_unfolding,[],[f64,f70])).

cnf(c_2,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_442,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_14,plain,
    ( ~ v1_relat_1(X0)
    | k1_setfam_1(k6_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_433,plain,
    ( k1_setfam_1(k6_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_796,plain,
    ( k1_setfam_1(k6_enumset1(k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(superposition,[status(thm)],[c_442,c_433])).

cnf(c_9,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_797,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(light_normalisation,[status(thm)],[c_796,c_9])).

cnf(c_0,plain,
    ( r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_444,plain,
    ( r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1199,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_797,c_444])).

cnf(c_11,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k6_relat_1(X1),X0) = X0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_436,plain,
    ( k5_relat_1(k6_relat_1(X0),X1) = X1
    | r1_tarski(k1_relat_1(X1),X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2799,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k6_relat_1(X1)
    | r1_tarski(X1,X0) != iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9,c_436])).

cnf(c_15,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_432,plain,
    ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_802,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(superposition,[status(thm)],[c_442,c_432])).

cnf(c_2803,plain,
    ( k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X0)
    | r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2799,c_802])).

cnf(c_50,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_5501,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2803,c_50])).

cnf(c_5502,plain,
    ( k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X0)
    | r1_tarski(X0,X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_5501])).

cnf(c_5507,plain,
    ( k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X0) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
    inference(superposition,[status(thm)],[c_1199,c_5502])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | v1_relat_1(k5_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_443,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k5_relat_1(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2106,plain,
    ( v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_802,c_443])).

cnf(c_3535,plain,
    ( v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2106,c_50])).

cnf(c_3541,plain,
    ( v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3535,c_442])).

cnf(c_1200,plain,
    ( k1_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(X0)),X1)) = k1_relat_1(k7_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_797,c_433])).

cnf(c_3550,plain,
    ( k1_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X2)) = k1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)) ),
    inference(superposition,[status(thm)],[c_3541,c_1200])).

cnf(c_7046,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0)) = k1_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)))) ),
    inference(superposition,[status(thm)],[c_5507,c_3550])).

cnf(c_2797,plain,
    ( k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X0),X1)) = k7_relat_1(k6_relat_1(X0),X1)
    | v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1199,c_436])).

cnf(c_5488,plain,
    ( k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X0),X1)) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2797,c_3541])).

cnf(c_3547,plain,
    ( k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X1),X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X0) ),
    inference(superposition,[status(thm)],[c_3541,c_432])).

cnf(c_5495,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(superposition,[status(thm)],[c_5488,c_3547])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k5_relat_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k5_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_438,plain,
    ( k5_relat_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k5_relat_1(X1,X0))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2027,plain,
    ( k5_relat_1(k4_relat_1(k6_relat_1(X0)),k4_relat_1(X1)) = k4_relat_1(k5_relat_1(X1,k6_relat_1(X0)))
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_442,c_438])).

cnf(c_10,plain,
    ( k4_relat_1(k6_relat_1(X0)) = k6_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_2028,plain,
    ( k4_relat_1(k5_relat_1(X0,k6_relat_1(X1))) = k5_relat_1(k6_relat_1(X1),k4_relat_1(X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2027,c_10])).

cnf(c_3548,plain,
    ( k4_relat_1(k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X2))) = k5_relat_1(k6_relat_1(X2),k4_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
    inference(superposition,[status(thm)],[c_3541,c_2028])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X1,X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_440,plain,
    ( k5_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X1,X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3551,plain,
    ( k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X2)) = k8_relat_1(X2,k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(superposition,[status(thm)],[c_3541,c_440])).

cnf(c_3571,plain,
    ( k5_relat_1(k6_relat_1(X0),k4_relat_1(k7_relat_1(k6_relat_1(X1),X2))) = k4_relat_1(k8_relat_1(X0,k7_relat_1(k6_relat_1(X1),X2))) ),
    inference(light_normalisation,[status(thm)],[c_3548,c_3551])).

cnf(c_2098,plain,
    ( k4_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k5_relat_1(k6_relat_1(X1),k4_relat_1(k6_relat_1(X0))) ),
    inference(superposition,[status(thm)],[c_442,c_2028])).

cnf(c_2099,plain,
    ( k4_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) ),
    inference(light_normalisation,[status(thm)],[c_2098,c_10,c_802])).

cnf(c_2100,plain,
    ( k4_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(demodulation,[status(thm)],[c_2099,c_802])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k8_relat_1(X2,k5_relat_1(X0,X1)) = k5_relat_1(X0,k8_relat_1(X2,X1)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_439,plain,
    ( k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2))
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2820,plain,
    ( k8_relat_1(X0,k5_relat_1(k6_relat_1(X1),X2)) = k5_relat_1(k6_relat_1(X1),k8_relat_1(X0,X2))
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_442,c_439])).

cnf(c_3348,plain,
    ( k8_relat_1(X0,k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) = k5_relat_1(k6_relat_1(X1),k8_relat_1(X0,k6_relat_1(X2))) ),
    inference(superposition,[status(thm)],[c_442,c_2820])).

cnf(c_1113,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k8_relat_1(X1,k6_relat_1(X0)) ),
    inference(superposition,[status(thm)],[c_442,c_440])).

cnf(c_1852,plain,
    ( k8_relat_1(X0,k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(light_normalisation,[status(thm)],[c_1113,c_802])).

cnf(c_3350,plain,
    ( k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X1),X2)) = k8_relat_1(X1,k7_relat_1(k6_relat_1(X2),X0)) ),
    inference(demodulation,[status(thm)],[c_3348,c_802,c_1852])).

cnf(c_3573,plain,
    ( k4_relat_1(k8_relat_1(X0,k7_relat_1(k6_relat_1(X1),X2))) = k8_relat_1(X2,k7_relat_1(k6_relat_1(X1),X0)) ),
    inference(demodulation,[status(thm)],[c_3571,c_2100,c_3350])).

cnf(c_3666,plain,
    ( k8_relat_1(X0,k7_relat_1(k6_relat_1(X1),X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) ),
    inference(demodulation,[status(thm)],[c_3547,c_3350])).

cnf(c_4739,plain,
    ( k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)) = k8_relat_1(X2,k7_relat_1(k6_relat_1(X1),X0)) ),
    inference(light_normalisation,[status(thm)],[c_3573,c_3666])).

cnf(c_4740,plain,
    ( k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X1),X0) ),
    inference(demodulation,[status(thm)],[c_4739,c_3666])).

cnf(c_5521,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0) = k4_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(superposition,[status(thm)],[c_5495,c_4740])).

cnf(c_5522,plain,
    ( k4_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(light_normalisation,[status(thm)],[c_5521,c_5495])).

cnf(c_5528,plain,
    ( k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(superposition,[status(thm)],[c_5522,c_2100])).

cnf(c_13,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_434,plain,
    ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_619,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(k2_relat_1(k6_relat_1(X0)))) = k6_relat_1(X0) ),
    inference(superposition,[status(thm)],[c_442,c_434])).

cnf(c_8,plain,
    ( k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_620,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X0)) = k6_relat_1(X0) ),
    inference(light_normalisation,[status(thm)],[c_619,c_8])).

cnf(c_1503,plain,
    ( k7_relat_1(k6_relat_1(X0),X0) = k6_relat_1(X0) ),
    inference(superposition,[status(thm)],[c_620,c_802])).

cnf(c_3683,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X1) = k8_relat_1(X0,k6_relat_1(X1)) ),
    inference(superposition,[status(thm)],[c_1503,c_3666])).

cnf(c_3688,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X1) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(light_normalisation,[status(thm)],[c_3683,c_1852])).

cnf(c_5578,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(superposition,[status(thm)],[c_5528,c_3688])).

cnf(c_7048,plain,
    ( k1_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)))) = k1_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
    inference(light_normalisation,[status(thm)],[c_7046,c_5578])).

cnf(c_7171,plain,
    ( k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
    inference(superposition,[status(thm)],[c_7048,c_9])).

cnf(c_3553,plain,
    ( k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)))) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(superposition,[status(thm)],[c_3541,c_434])).

cnf(c_3959,plain,
    ( k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X0),X1) ),
    inference(demodulation,[status(thm)],[c_3551,c_3666])).

cnf(c_4088,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X0),X1) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(superposition,[status(thm)],[c_3553,c_3959])).

cnf(c_5151,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),k2_relat_1(k7_relat_1(k6_relat_1(X1),X0))) = k4_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
    inference(superposition,[status(thm)],[c_4088,c_4740])).

cnf(c_5156,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),k2_relat_1(k7_relat_1(k6_relat_1(X1),X0))) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(demodulation,[status(thm)],[c_5151,c_2100])).

cnf(c_7038,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),k2_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))))) = k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
    inference(superposition,[status(thm)],[c_5507,c_5156])).

cnf(c_5569,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X1) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(superposition,[status(thm)],[c_5528,c_5495])).

cnf(c_7068,plain,
    ( k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X0) ),
    inference(demodulation,[status(thm)],[c_7038,c_8,c_5569])).

cnf(c_7069,plain,
    ( k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
    inference(light_normalisation,[status(thm)],[c_7068,c_5507])).

cnf(c_7423,plain,
    ( k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(k6_relat_1(X1),X0))) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
    inference(superposition,[status(thm)],[c_7171,c_7069])).

cnf(c_12,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_435,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3552,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),k7_relat_1(k6_relat_1(X0),X1)) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(superposition,[status(thm)],[c_3541,c_435])).

cnf(c_3978,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(superposition,[status(thm)],[c_3552,c_3547])).

cnf(c_4752,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X1),X0) = k4_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(superposition,[status(thm)],[c_3978,c_4740])).

cnf(c_4754,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X1),X0) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(light_normalisation,[status(thm)],[c_4752,c_2100])).

cnf(c_5535,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(k6_relat_1(X1),X0))),X1) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(demodulation,[status(thm)],[c_5528,c_4754])).

cnf(c_7680,plain,
    ( k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X1) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(demodulation,[status(thm)],[c_7423,c_5535])).

cnf(c_8149,plain,
    ( k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(k6_relat_1(X1),X0))))) = k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(k6_relat_1(X1),X0))) ),
    inference(superposition,[status(thm)],[c_7680,c_7423])).

cnf(c_8157,plain,
    ( k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(k6_relat_1(X1),X0))) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(superposition,[status(thm)],[c_7680,c_5528])).

cnf(c_8207,plain,
    ( k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(light_normalisation,[status(thm)],[c_8149,c_8157])).

cnf(c_16,negated_conjecture,
    ( k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1201,plain,
    ( k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(sK0),sK1))) != k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) ),
    inference(demodulation,[status(thm)],[c_797,c_16])).

cnf(c_1502,plain,
    ( k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(sK0),sK1))) != k7_relat_1(k6_relat_1(sK0),sK1) ),
    inference(demodulation,[status(thm)],[c_802,c_1201])).

cnf(c_5533,plain,
    ( k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(sK1),sK0))) != k7_relat_1(k6_relat_1(sK1),sK0) ),
    inference(demodulation,[status(thm)],[c_5528,c_1502])).

cnf(c_8223,plain,
    ( k7_relat_1(k6_relat_1(sK1),sK0) != k7_relat_1(k6_relat_1(sK1),sK0) ),
    inference(demodulation,[status(thm)],[c_8207,c_5533])).

cnf(c_8224,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_8223])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:49:59 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 0.38/1.06  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.38/1.06  
% 0.38/1.06  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.38/1.06  
% 0.38/1.06  ------  iProver source info
% 0.38/1.06  
% 0.38/1.06  git: date: 2020-06-30 10:37:57 +0100
% 0.38/1.06  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.38/1.06  git: non_committed_changes: false
% 0.38/1.06  git: last_make_outside_of_git: false
% 0.38/1.06  
% 0.38/1.06  ------ 
% 0.38/1.06  
% 0.38/1.06  ------ Input Options
% 0.38/1.06  
% 0.38/1.06  --out_options                           all
% 0.38/1.06  --tptp_safe_out                         true
% 0.38/1.06  --problem_path                          ""
% 0.38/1.06  --include_path                          ""
% 0.38/1.06  --clausifier                            res/vclausify_rel
% 0.38/1.06  --clausifier_options                    --mode clausify
% 0.38/1.06  --stdin                                 false
% 0.38/1.06  --stats_out                             all
% 0.38/1.06  
% 0.38/1.06  ------ General Options
% 0.38/1.06  
% 0.38/1.06  --fof                                   false
% 0.38/1.06  --time_out_real                         305.
% 0.38/1.06  --time_out_virtual                      -1.
% 0.38/1.06  --symbol_type_check                     false
% 0.38/1.06  --clausify_out                          false
% 0.38/1.06  --sig_cnt_out                           false
% 0.38/1.06  --trig_cnt_out                          false
% 0.38/1.06  --trig_cnt_out_tolerance                1.
% 0.38/1.06  --trig_cnt_out_sk_spl                   false
% 0.38/1.06  --abstr_cl_out                          false
% 0.38/1.06  
% 0.38/1.06  ------ Global Options
% 0.38/1.06  
% 0.38/1.06  --schedule                              default
% 0.38/1.06  --add_important_lit                     false
% 0.38/1.06  --prop_solver_per_cl                    1000
% 0.38/1.06  --min_unsat_core                        false
% 0.38/1.06  --soft_assumptions                      false
% 0.38/1.06  --soft_lemma_size                       3
% 0.38/1.06  --prop_impl_unit_size                   0
% 0.38/1.06  --prop_impl_unit                        []
% 0.38/1.06  --share_sel_clauses                     true
% 0.38/1.06  --reset_solvers                         false
% 0.38/1.06  --bc_imp_inh                            [conj_cone]
% 0.38/1.06  --conj_cone_tolerance                   3.
% 0.38/1.06  --extra_neg_conj                        none
% 0.38/1.06  --large_theory_mode                     true
% 0.38/1.06  --prolific_symb_bound                   200
% 0.38/1.06  --lt_threshold                          2000
% 0.38/1.06  --clause_weak_htbl                      true
% 0.38/1.06  --gc_record_bc_elim                     false
% 0.38/1.06  
% 0.38/1.06  ------ Preprocessing Options
% 0.38/1.06  
% 0.38/1.06  --preprocessing_flag                    true
% 0.38/1.06  --time_out_prep_mult                    0.1
% 0.38/1.06  --splitting_mode                        input
% 0.38/1.06  --splitting_grd                         true
% 0.38/1.06  --splitting_cvd                         false
% 0.38/1.06  --splitting_cvd_svl                     false
% 0.38/1.06  --splitting_nvd                         32
% 0.38/1.06  --sub_typing                            true
% 0.38/1.06  --prep_gs_sim                           true
% 0.38/1.06  --prep_unflatten                        true
% 0.38/1.06  --prep_res_sim                          true
% 0.38/1.06  --prep_upred                            true
% 0.38/1.06  --prep_sem_filter                       exhaustive
% 0.38/1.06  --prep_sem_filter_out                   false
% 0.38/1.06  --pred_elim                             true
% 0.38/1.06  --res_sim_input                         true
% 0.38/1.06  --eq_ax_congr_red                       true
% 0.38/1.06  --pure_diseq_elim                       true
% 0.38/1.06  --brand_transform                       false
% 0.38/1.06  --non_eq_to_eq                          false
% 0.38/1.06  --prep_def_merge                        true
% 0.38/1.06  --prep_def_merge_prop_impl              false
% 0.38/1.06  --prep_def_merge_mbd                    true
% 0.38/1.06  --prep_def_merge_tr_red                 false
% 0.38/1.06  --prep_def_merge_tr_cl                  false
% 0.38/1.06  --smt_preprocessing                     true
% 0.38/1.06  --smt_ac_axioms                         fast
% 0.38/1.06  --preprocessed_out                      false
% 0.38/1.06  --preprocessed_stats                    false
% 0.38/1.06  
% 0.38/1.06  ------ Abstraction refinement Options
% 0.38/1.06  
% 0.38/1.06  --abstr_ref                             []
% 0.38/1.06  --abstr_ref_prep                        false
% 0.38/1.06  --abstr_ref_until_sat                   false
% 0.38/1.06  --abstr_ref_sig_restrict                funpre
% 0.38/1.06  --abstr_ref_af_restrict_to_split_sk     false
% 0.38/1.06  --abstr_ref_under                       []
% 0.38/1.06  
% 0.38/1.06  ------ SAT Options
% 0.38/1.06  
% 0.38/1.06  --sat_mode                              false
% 0.38/1.06  --sat_fm_restart_options                ""
% 0.38/1.06  --sat_gr_def                            false
% 0.38/1.06  --sat_epr_types                         true
% 0.38/1.06  --sat_non_cyclic_types                  false
% 0.38/1.06  --sat_finite_models                     false
% 0.38/1.06  --sat_fm_lemmas                         false
% 0.38/1.06  --sat_fm_prep                           false
% 0.38/1.06  --sat_fm_uc_incr                        true
% 0.38/1.06  --sat_out_model                         small
% 0.38/1.06  --sat_out_clauses                       false
% 0.38/1.06  
% 0.38/1.06  ------ QBF Options
% 0.38/1.06  
% 0.38/1.06  --qbf_mode                              false
% 0.38/1.06  --qbf_elim_univ                         false
% 0.38/1.06  --qbf_dom_inst                          none
% 0.38/1.06  --qbf_dom_pre_inst                      false
% 0.38/1.06  --qbf_sk_in                             false
% 0.38/1.06  --qbf_pred_elim                         true
% 0.38/1.06  --qbf_split                             512
% 0.38/1.06  
% 0.38/1.06  ------ BMC1 Options
% 0.38/1.06  
% 0.38/1.06  --bmc1_incremental                      false
% 0.38/1.06  --bmc1_axioms                           reachable_all
% 0.38/1.06  --bmc1_min_bound                        0
% 0.38/1.06  --bmc1_max_bound                        -1
% 0.38/1.06  --bmc1_max_bound_default                -1
% 0.38/1.06  --bmc1_symbol_reachability              true
% 0.38/1.06  --bmc1_property_lemmas                  false
% 0.38/1.06  --bmc1_k_induction                      false
% 0.38/1.06  --bmc1_non_equiv_states                 false
% 0.38/1.06  --bmc1_deadlock                         false
% 0.38/1.06  --bmc1_ucm                              false
% 0.38/1.06  --bmc1_add_unsat_core                   none
% 0.38/1.06  --bmc1_unsat_core_children              false
% 0.38/1.06  --bmc1_unsat_core_extrapolate_axioms    false
% 0.38/1.06  --bmc1_out_stat                         full
% 0.38/1.06  --bmc1_ground_init                      false
% 0.38/1.06  --bmc1_pre_inst_next_state              false
% 0.38/1.06  --bmc1_pre_inst_state                   false
% 0.38/1.06  --bmc1_pre_inst_reach_state             false
% 0.38/1.06  --bmc1_out_unsat_core                   false
% 0.38/1.06  --bmc1_aig_witness_out                  false
% 0.38/1.06  --bmc1_verbose                          false
% 0.38/1.06  --bmc1_dump_clauses_tptp                false
% 0.38/1.06  --bmc1_dump_unsat_core_tptp             false
% 0.38/1.06  --bmc1_dump_file                        -
% 0.38/1.06  --bmc1_ucm_expand_uc_limit              128
% 0.38/1.06  --bmc1_ucm_n_expand_iterations          6
% 0.38/1.06  --bmc1_ucm_extend_mode                  1
% 0.38/1.06  --bmc1_ucm_init_mode                    2
% 0.38/1.06  --bmc1_ucm_cone_mode                    none
% 0.38/1.06  --bmc1_ucm_reduced_relation_type        0
% 0.38/1.06  --bmc1_ucm_relax_model                  4
% 0.38/1.06  --bmc1_ucm_full_tr_after_sat            true
% 0.38/1.06  --bmc1_ucm_expand_neg_assumptions       false
% 0.38/1.06  --bmc1_ucm_layered_model                none
% 0.38/1.06  --bmc1_ucm_max_lemma_size               10
% 0.38/1.06  
% 0.38/1.06  ------ AIG Options
% 0.38/1.06  
% 0.38/1.06  --aig_mode                              false
% 0.38/1.06  
% 0.38/1.06  ------ Instantiation Options
% 0.38/1.06  
% 0.38/1.06  --instantiation_flag                    true
% 0.38/1.06  --inst_sos_flag                         false
% 0.38/1.06  --inst_sos_phase                        true
% 0.38/1.06  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.38/1.06  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.38/1.06  --inst_lit_sel_side                     num_symb
% 0.38/1.06  --inst_solver_per_active                1400
% 0.38/1.06  --inst_solver_calls_frac                1.
% 0.38/1.06  --inst_passive_queue_type               priority_queues
% 0.38/1.06  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.38/1.06  --inst_passive_queues_freq              [25;2]
% 0.38/1.06  --inst_dismatching                      true
% 0.38/1.06  --inst_eager_unprocessed_to_passive     true
% 0.38/1.06  --inst_prop_sim_given                   true
% 0.38/1.06  --inst_prop_sim_new                     false
% 0.38/1.06  --inst_subs_new                         false
% 0.38/1.06  --inst_eq_res_simp                      false
% 0.38/1.06  --inst_subs_given                       false
% 0.38/1.06  --inst_orphan_elimination               true
% 0.38/1.06  --inst_learning_loop_flag               true
% 0.38/1.06  --inst_learning_start                   3000
% 0.38/1.06  --inst_learning_factor                  2
% 0.38/1.06  --inst_start_prop_sim_after_learn       3
% 0.38/1.06  --inst_sel_renew                        solver
% 0.38/1.06  --inst_lit_activity_flag                true
% 0.38/1.06  --inst_restr_to_given                   false
% 0.38/1.06  --inst_activity_threshold               500
% 0.38/1.06  --inst_out_proof                        true
% 0.38/1.06  
% 0.38/1.06  ------ Resolution Options
% 0.38/1.06  
% 0.38/1.06  --resolution_flag                       true
% 0.38/1.06  --res_lit_sel                           adaptive
% 0.38/1.06  --res_lit_sel_side                      none
% 0.38/1.06  --res_ordering                          kbo
% 0.38/1.06  --res_to_prop_solver                    active
% 0.38/1.06  --res_prop_simpl_new                    false
% 0.38/1.06  --res_prop_simpl_given                  true
% 0.38/1.06  --res_passive_queue_type                priority_queues
% 0.38/1.06  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.38/1.06  --res_passive_queues_freq               [15;5]
% 0.38/1.06  --res_forward_subs                      full
% 0.38/1.06  --res_backward_subs                     full
% 0.38/1.06  --res_forward_subs_resolution           true
% 0.38/1.06  --res_backward_subs_resolution          true
% 0.38/1.06  --res_orphan_elimination                true
% 0.38/1.06  --res_time_limit                        2.
% 0.38/1.06  --res_out_proof                         true
% 0.38/1.06  
% 0.38/1.06  ------ Superposition Options
% 0.38/1.06  
% 0.38/1.06  --superposition_flag                    true
% 0.38/1.06  --sup_passive_queue_type                priority_queues
% 0.38/1.06  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.38/1.06  --sup_passive_queues_freq               [8;1;4]
% 0.38/1.06  --demod_completeness_check              fast
% 0.38/1.06  --demod_use_ground                      true
% 0.38/1.06  --sup_to_prop_solver                    passive
% 0.38/1.06  --sup_prop_simpl_new                    true
% 0.38/1.06  --sup_prop_simpl_given                  true
% 0.38/1.06  --sup_fun_splitting                     false
% 0.38/1.06  --sup_smt_interval                      50000
% 0.38/1.06  
% 0.38/1.06  ------ Superposition Simplification Setup
% 0.38/1.06  
% 0.38/1.06  --sup_indices_passive                   []
% 0.38/1.06  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.38/1.06  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.38/1.06  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.38/1.06  --sup_full_triv                         [TrivRules;PropSubs]
% 0.38/1.06  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.38/1.06  --sup_full_bw                           [BwDemod]
% 0.38/1.06  --sup_immed_triv                        [TrivRules]
% 0.38/1.06  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.38/1.06  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.38/1.06  --sup_immed_bw_main                     []
% 0.38/1.06  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.38/1.06  --sup_input_triv                        [Unflattening;TrivRules]
% 0.38/1.06  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.38/1.06  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.38/1.06  
% 0.38/1.06  ------ Combination Options
% 0.38/1.06  
% 0.38/1.06  --comb_res_mult                         3
% 0.38/1.06  --comb_sup_mult                         2
% 0.38/1.06  --comb_inst_mult                        10
% 0.38/1.06  
% 0.38/1.06  ------ Debug Options
% 0.38/1.06  
% 0.38/1.06  --dbg_backtrace                         false
% 0.38/1.06  --dbg_dump_prop_clauses                 false
% 0.38/1.06  --dbg_dump_prop_clauses_file            -
% 0.38/1.06  --dbg_out_stat                          false
% 0.38/1.06  ------ Parsing...
% 0.38/1.06  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.38/1.06  
% 0.38/1.06  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 0.38/1.06  
% 0.38/1.06  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.38/1.06  
% 0.38/1.06  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 0.38/1.06  ------ Proving...
% 0.38/1.06  ------ Problem Properties 
% 0.38/1.06  
% 0.38/1.06  
% 0.38/1.06  clauses                                 17
% 0.38/1.06  conjectures                             1
% 0.38/1.06  EPR                                     0
% 0.38/1.06  Horn                                    17
% 0.38/1.06  unary                                   6
% 0.38/1.06  binary                                  5
% 0.38/1.06  lits                                    35
% 0.38/1.06  lits eq                                 14
% 0.38/1.06  fd_pure                                 0
% 0.38/1.06  fd_pseudo                               0
% 0.38/1.06  fd_cond                                 0
% 0.38/1.06  fd_pseudo_cond                          0
% 0.38/1.06  AC symbols                              0
% 0.38/1.06  
% 0.38/1.06  ------ Schedule dynamic 5 is on 
% 0.38/1.06  
% 0.38/1.06  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 0.38/1.06  
% 0.38/1.06  
% 0.38/1.06  ------ 
% 0.38/1.06  Current options:
% 0.38/1.06  ------ 
% 0.38/1.06  
% 0.38/1.06  ------ Input Options
% 0.38/1.06  
% 0.38/1.06  --out_options                           all
% 0.38/1.06  --tptp_safe_out                         true
% 0.38/1.06  --problem_path                          ""
% 0.38/1.06  --include_path                          ""
% 0.38/1.06  --clausifier                            res/vclausify_rel
% 0.38/1.06  --clausifier_options                    --mode clausify
% 0.38/1.06  --stdin                                 false
% 0.38/1.06  --stats_out                             all
% 0.38/1.06  
% 0.38/1.06  ------ General Options
% 0.38/1.06  
% 0.38/1.06  --fof                                   false
% 0.38/1.06  --time_out_real                         305.
% 0.38/1.06  --time_out_virtual                      -1.
% 0.38/1.06  --symbol_type_check                     false
% 0.38/1.06  --clausify_out                          false
% 0.38/1.06  --sig_cnt_out                           false
% 0.38/1.06  --trig_cnt_out                          false
% 0.38/1.06  --trig_cnt_out_tolerance                1.
% 0.38/1.06  --trig_cnt_out_sk_spl                   false
% 0.38/1.06  --abstr_cl_out                          false
% 0.38/1.06  
% 0.38/1.06  ------ Global Options
% 0.38/1.06  
% 0.38/1.06  --schedule                              default
% 0.38/1.06  --add_important_lit                     false
% 0.38/1.06  --prop_solver_per_cl                    1000
% 0.38/1.06  --min_unsat_core                        false
% 0.38/1.06  --soft_assumptions                      false
% 0.38/1.06  --soft_lemma_size                       3
% 0.38/1.06  --prop_impl_unit_size                   0
% 0.38/1.06  --prop_impl_unit                        []
% 0.38/1.06  --share_sel_clauses                     true
% 0.38/1.06  --reset_solvers                         false
% 0.38/1.06  --bc_imp_inh                            [conj_cone]
% 0.38/1.06  --conj_cone_tolerance                   3.
% 0.38/1.06  --extra_neg_conj                        none
% 0.38/1.06  --large_theory_mode                     true
% 0.38/1.06  --prolific_symb_bound                   200
% 0.38/1.06  --lt_threshold                          2000
% 0.38/1.06  --clause_weak_htbl                      true
% 0.38/1.06  --gc_record_bc_elim                     false
% 0.38/1.06  
% 0.38/1.06  ------ Preprocessing Options
% 0.38/1.06  
% 0.38/1.06  --preprocessing_flag                    true
% 0.38/1.06  --time_out_prep_mult                    0.1
% 0.38/1.06  --splitting_mode                        input
% 0.38/1.06  --splitting_grd                         true
% 0.38/1.06  --splitting_cvd                         false
% 0.38/1.06  --splitting_cvd_svl                     false
% 0.38/1.06  --splitting_nvd                         32
% 0.38/1.06  --sub_typing                            true
% 0.38/1.06  --prep_gs_sim                           true
% 0.38/1.06  --prep_unflatten                        true
% 0.38/1.06  --prep_res_sim                          true
% 0.38/1.06  --prep_upred                            true
% 0.38/1.06  --prep_sem_filter                       exhaustive
% 0.38/1.06  --prep_sem_filter_out                   false
% 0.38/1.06  --pred_elim                             true
% 0.38/1.06  --res_sim_input                         true
% 0.38/1.06  --eq_ax_congr_red                       true
% 0.38/1.06  --pure_diseq_elim                       true
% 0.38/1.06  --brand_transform                       false
% 0.38/1.06  --non_eq_to_eq                          false
% 0.38/1.06  --prep_def_merge                        true
% 0.38/1.06  --prep_def_merge_prop_impl              false
% 0.38/1.06  --prep_def_merge_mbd                    true
% 0.38/1.06  --prep_def_merge_tr_red                 false
% 0.38/1.06  --prep_def_merge_tr_cl                  false
% 0.38/1.06  --smt_preprocessing                     true
% 0.38/1.06  --smt_ac_axioms                         fast
% 0.38/1.06  --preprocessed_out                      false
% 0.38/1.06  --preprocessed_stats                    false
% 0.38/1.06  
% 0.38/1.06  ------ Abstraction refinement Options
% 0.38/1.06  
% 0.38/1.06  --abstr_ref                             []
% 0.38/1.06  --abstr_ref_prep                        false
% 0.38/1.06  --abstr_ref_until_sat                   false
% 0.38/1.06  --abstr_ref_sig_restrict                funpre
% 0.38/1.06  --abstr_ref_af_restrict_to_split_sk     false
% 0.38/1.06  --abstr_ref_under                       []
% 0.38/1.06  
% 0.38/1.06  ------ SAT Options
% 0.38/1.06  
% 0.38/1.06  --sat_mode                              false
% 0.38/1.06  --sat_fm_restart_options                ""
% 0.38/1.06  --sat_gr_def                            false
% 0.38/1.06  --sat_epr_types                         true
% 0.38/1.06  --sat_non_cyclic_types                  false
% 0.38/1.06  --sat_finite_models                     false
% 0.38/1.06  --sat_fm_lemmas                         false
% 0.38/1.06  --sat_fm_prep                           false
% 0.38/1.06  --sat_fm_uc_incr                        true
% 0.38/1.06  --sat_out_model                         small
% 0.38/1.06  --sat_out_clauses                       false
% 0.38/1.06  
% 0.38/1.06  ------ QBF Options
% 0.38/1.06  
% 0.38/1.06  --qbf_mode                              false
% 0.38/1.06  --qbf_elim_univ                         false
% 0.38/1.06  --qbf_dom_inst                          none
% 0.38/1.06  --qbf_dom_pre_inst                      false
% 0.38/1.06  --qbf_sk_in                             false
% 0.38/1.06  --qbf_pred_elim                         true
% 0.38/1.06  --qbf_split                             512
% 0.38/1.06  
% 0.38/1.06  ------ BMC1 Options
% 0.38/1.06  
% 0.38/1.06  --bmc1_incremental                      false
% 0.38/1.06  --bmc1_axioms                           reachable_all
% 0.38/1.06  --bmc1_min_bound                        0
% 0.38/1.06  --bmc1_max_bound                        -1
% 0.38/1.06  --bmc1_max_bound_default                -1
% 0.38/1.06  --bmc1_symbol_reachability              true
% 0.38/1.06  --bmc1_property_lemmas                  false
% 0.38/1.06  --bmc1_k_induction                      false
% 0.38/1.06  --bmc1_non_equiv_states                 false
% 0.38/1.06  --bmc1_deadlock                         false
% 0.38/1.06  --bmc1_ucm                              false
% 0.38/1.06  --bmc1_add_unsat_core                   none
% 0.38/1.06  --bmc1_unsat_core_children              false
% 0.38/1.06  --bmc1_unsat_core_extrapolate_axioms    false
% 0.38/1.06  --bmc1_out_stat                         full
% 0.38/1.06  --bmc1_ground_init                      false
% 0.38/1.06  --bmc1_pre_inst_next_state              false
% 0.38/1.06  --bmc1_pre_inst_state                   false
% 0.38/1.06  --bmc1_pre_inst_reach_state             false
% 0.38/1.06  --bmc1_out_unsat_core                   false
% 0.38/1.06  --bmc1_aig_witness_out                  false
% 0.38/1.06  --bmc1_verbose                          false
% 0.38/1.06  --bmc1_dump_clauses_tptp                false
% 0.38/1.06  --bmc1_dump_unsat_core_tptp             false
% 0.38/1.06  --bmc1_dump_file                        -
% 0.38/1.06  --bmc1_ucm_expand_uc_limit              128
% 0.38/1.06  --bmc1_ucm_n_expand_iterations          6
% 0.38/1.06  --bmc1_ucm_extend_mode                  1
% 0.38/1.06  --bmc1_ucm_init_mode                    2
% 0.38/1.06  --bmc1_ucm_cone_mode                    none
% 0.38/1.06  --bmc1_ucm_reduced_relation_type        0
% 0.38/1.06  --bmc1_ucm_relax_model                  4
% 0.38/1.06  --bmc1_ucm_full_tr_after_sat            true
% 0.38/1.06  --bmc1_ucm_expand_neg_assumptions       false
% 0.38/1.06  --bmc1_ucm_layered_model                none
% 0.38/1.06  --bmc1_ucm_max_lemma_size               10
% 0.38/1.06  
% 0.38/1.06  ------ AIG Options
% 0.38/1.06  
% 0.38/1.06  --aig_mode                              false
% 0.38/1.06  
% 0.38/1.06  ------ Instantiation Options
% 0.38/1.06  
% 0.38/1.06  --instantiation_flag                    true
% 0.38/1.06  --inst_sos_flag                         false
% 0.38/1.06  --inst_sos_phase                        true
% 0.38/1.06  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.38/1.06  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.38/1.06  --inst_lit_sel_side                     none
% 0.38/1.06  --inst_solver_per_active                1400
% 0.38/1.06  --inst_solver_calls_frac                1.
% 0.38/1.06  --inst_passive_queue_type               priority_queues
% 0.38/1.06  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.38/1.06  --inst_passive_queues_freq              [25;2]
% 0.38/1.06  --inst_dismatching                      true
% 0.38/1.06  --inst_eager_unprocessed_to_passive     true
% 0.38/1.06  --inst_prop_sim_given                   true
% 0.38/1.06  --inst_prop_sim_new                     false
% 0.38/1.06  --inst_subs_new                         false
% 0.38/1.06  --inst_eq_res_simp                      false
% 0.38/1.06  --inst_subs_given                       false
% 0.38/1.06  --inst_orphan_elimination               true
% 0.38/1.06  --inst_learning_loop_flag               true
% 0.38/1.06  --inst_learning_start                   3000
% 0.38/1.06  --inst_learning_factor                  2
% 0.38/1.06  --inst_start_prop_sim_after_learn       3
% 0.38/1.06  --inst_sel_renew                        solver
% 0.38/1.06  --inst_lit_activity_flag                true
% 0.38/1.06  --inst_restr_to_given                   false
% 0.38/1.06  --inst_activity_threshold               500
% 0.38/1.06  --inst_out_proof                        true
% 0.38/1.06  
% 0.38/1.06  ------ Resolution Options
% 0.38/1.06  
% 0.38/1.06  --resolution_flag                       false
% 0.38/1.06  --res_lit_sel                           adaptive
% 0.38/1.06  --res_lit_sel_side                      none
% 0.38/1.06  --res_ordering                          kbo
% 0.38/1.06  --res_to_prop_solver                    active
% 0.38/1.06  --res_prop_simpl_new                    false
% 0.38/1.06  --res_prop_simpl_given                  true
% 0.38/1.06  --res_passive_queue_type                priority_queues
% 0.38/1.06  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.38/1.06  --res_passive_queues_freq               [15;5]
% 0.38/1.06  --res_forward_subs                      full
% 0.38/1.06  --res_backward_subs                     full
% 0.38/1.06  --res_forward_subs_resolution           true
% 0.38/1.06  --res_backward_subs_resolution          true
% 0.38/1.06  --res_orphan_elimination                true
% 0.38/1.06  --res_time_limit                        2.
% 0.38/1.06  --res_out_proof                         true
% 0.38/1.06  
% 0.38/1.06  ------ Superposition Options
% 0.38/1.06  
% 0.38/1.06  --superposition_flag                    true
% 0.38/1.06  --sup_passive_queue_type                priority_queues
% 0.38/1.06  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.38/1.06  --sup_passive_queues_freq               [8;1;4]
% 0.38/1.06  --demod_completeness_check              fast
% 0.38/1.06  --demod_use_ground                      true
% 0.38/1.06  --sup_to_prop_solver                    passive
% 0.38/1.06  --sup_prop_simpl_new                    true
% 0.38/1.06  --sup_prop_simpl_given                  true
% 0.38/1.06  --sup_fun_splitting                     false
% 0.38/1.06  --sup_smt_interval                      50000
% 0.38/1.06  
% 0.38/1.06  ------ Superposition Simplification Setup
% 0.38/1.06  
% 0.38/1.06  --sup_indices_passive                   []
% 0.38/1.06  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.38/1.06  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.38/1.06  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.38/1.06  --sup_full_triv                         [TrivRules;PropSubs]
% 0.38/1.06  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.38/1.06  --sup_full_bw                           [BwDemod]
% 0.38/1.06  --sup_immed_triv                        [TrivRules]
% 0.38/1.06  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.38/1.06  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.38/1.06  --sup_immed_bw_main                     []
% 0.38/1.06  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.38/1.06  --sup_input_triv                        [Unflattening;TrivRules]
% 0.38/1.06  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.38/1.06  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.38/1.06  
% 0.38/1.06  ------ Combination Options
% 0.38/1.06  
% 0.38/1.06  --comb_res_mult                         3
% 0.38/1.06  --comb_sup_mult                         2
% 0.38/1.06  --comb_inst_mult                        10
% 0.38/1.06  
% 0.38/1.06  ------ Debug Options
% 0.38/1.06  
% 0.38/1.06  --dbg_backtrace                         false
% 0.38/1.06  --dbg_dump_prop_clauses                 false
% 0.38/1.06  --dbg_dump_prop_clauses_file            -
% 0.38/1.06  --dbg_out_stat                          false
% 0.38/1.06  
% 0.38/1.06  
% 0.38/1.06  
% 0.38/1.06  
% 0.38/1.06  ------ Proving...
% 0.38/1.06  
% 0.38/1.06  
% 0.38/1.06  % SZS status Theorem for theBenchmark.p
% 0.38/1.06  
% 0.38/1.06   Resolution empty clause
% 0.38/1.06  
% 0.38/1.06  % SZS output start CNFRefutation for theBenchmark.p
% 0.38/1.06  
% 0.38/1.06  fof(f10,axiom,(
% 0.38/1.06    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.38/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.38/1.06  
% 0.38/1.06  fof(f50,plain,(
% 0.38/1.06    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.38/1.06    inference(cnf_transformation,[],[f10])).
% 0.38/1.06  
% 0.38/1.06  fof(f21,axiom,(
% 0.38/1.06    ! [X0,X1] : (v1_relat_1(X1) => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)))),
% 0.38/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.38/1.06  
% 0.38/1.06  fof(f36,plain,(
% 0.38/1.06    ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 0.38/1.06    inference(ennf_transformation,[],[f21])).
% 0.38/1.06  
% 0.38/1.06  fof(f62,plain,(
% 0.38/1.06    ( ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 0.38/1.06    inference(cnf_transformation,[],[f36])).
% 0.38/1.06  
% 0.38/1.06  fof(f8,axiom,(
% 0.38/1.06    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.38/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.38/1.06  
% 0.38/1.06  fof(f48,plain,(
% 0.38/1.06    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.38/1.06    inference(cnf_transformation,[],[f8])).
% 0.38/1.06  
% 0.38/1.06  fof(f2,axiom,(
% 0.38/1.06    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.38/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.38/1.06  
% 0.38/1.06  fof(f42,plain,(
% 0.38/1.06    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.38/1.06    inference(cnf_transformation,[],[f2])).
% 0.38/1.06  
% 0.38/1.06  fof(f3,axiom,(
% 0.38/1.06    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.38/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.38/1.06  
% 0.38/1.06  fof(f43,plain,(
% 0.38/1.06    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.38/1.06    inference(cnf_transformation,[],[f3])).
% 0.38/1.06  
% 0.38/1.06  fof(f4,axiom,(
% 0.38/1.06    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 0.38/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.38/1.06  
% 0.38/1.06  fof(f44,plain,(
% 0.38/1.06    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 0.38/1.06    inference(cnf_transformation,[],[f4])).
% 0.38/1.06  
% 0.38/1.06  fof(f5,axiom,(
% 0.38/1.06    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 0.38/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.38/1.06  
% 0.38/1.06  fof(f45,plain,(
% 0.38/1.06    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 0.38/1.06    inference(cnf_transformation,[],[f5])).
% 0.38/1.06  
% 0.38/1.06  fof(f6,axiom,(
% 0.38/1.06    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 0.38/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.38/1.06  
% 0.38/1.06  fof(f46,plain,(
% 0.38/1.06    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 0.38/1.06    inference(cnf_transformation,[],[f6])).
% 0.38/1.06  
% 0.38/1.06  fof(f7,axiom,(
% 0.38/1.06    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 0.38/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.38/1.06  
% 0.38/1.06  fof(f47,plain,(
% 0.38/1.06    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 0.38/1.06    inference(cnf_transformation,[],[f7])).
% 0.38/1.06  
% 0.38/1.06  fof(f65,plain,(
% 0.38/1.06    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.38/1.06    inference(definition_unfolding,[],[f46,f47])).
% 0.38/1.06  
% 0.38/1.06  fof(f66,plain,(
% 0.38/1.06    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.38/1.06    inference(definition_unfolding,[],[f45,f65])).
% 0.38/1.06  
% 0.38/1.06  fof(f67,plain,(
% 0.38/1.06    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.38/1.06    inference(definition_unfolding,[],[f44,f66])).
% 0.38/1.06  
% 0.38/1.06  fof(f68,plain,(
% 0.38/1.06    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.38/1.06    inference(definition_unfolding,[],[f43,f67])).
% 0.38/1.06  
% 0.38/1.06  fof(f69,plain,(
% 0.38/1.06    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.38/1.06    inference(definition_unfolding,[],[f42,f68])).
% 0.38/1.06  
% 0.38/1.06  fof(f70,plain,(
% 0.38/1.06    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 0.38/1.06    inference(definition_unfolding,[],[f48,f69])).
% 0.38/1.06  
% 0.38/1.06  fof(f72,plain,(
% 0.38/1.06    ( ! [X0,X1] : (k1_setfam_1(k6_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X0)) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 0.38/1.06    inference(definition_unfolding,[],[f62,f70])).
% 0.38/1.06  
% 0.38/1.06  fof(f16,axiom,(
% 0.38/1.06    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.38/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.38/1.06  
% 0.38/1.06  fof(f56,plain,(
% 0.38/1.06    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.38/1.06    inference(cnf_transformation,[],[f16])).
% 0.38/1.06  
% 0.38/1.06  fof(f1,axiom,(
% 0.38/1.06    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.38/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.38/1.06  
% 0.38/1.06  fof(f41,plain,(
% 0.38/1.06    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.38/1.06    inference(cnf_transformation,[],[f1])).
% 0.38/1.06  
% 0.38/1.06  fof(f71,plain,(
% 0.38/1.06    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0)) )),
% 0.38/1.06    inference(definition_unfolding,[],[f41,f70])).
% 0.38/1.06  
% 0.38/1.06  fof(f18,axiom,(
% 0.38/1.06    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k5_relat_1(k6_relat_1(X0),X1) = X1))),
% 0.38/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.38/1.06  
% 0.38/1.06  fof(f32,plain,(
% 0.38/1.06    ! [X0,X1] : ((k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.38/1.06    inference(ennf_transformation,[],[f18])).
% 0.38/1.06  
% 0.38/1.06  fof(f33,plain,(
% 0.38/1.06    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.38/1.06    inference(flattening,[],[f32])).
% 0.38/1.06  
% 0.38/1.06  fof(f59,plain,(
% 0.38/1.06    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.38/1.06    inference(cnf_transformation,[],[f33])).
% 0.38/1.06  
% 0.38/1.06  fof(f22,axiom,(
% 0.38/1.06    ! [X0,X1] : (v1_relat_1(X1) => k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0))),
% 0.38/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.38/1.06  
% 0.38/1.06  fof(f37,plain,(
% 0.38/1.06    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.38/1.06    inference(ennf_transformation,[],[f22])).
% 0.38/1.06  
% 0.38/1.06  fof(f63,plain,(
% 0.38/1.06    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.38/1.06    inference(cnf_transformation,[],[f37])).
% 0.38/1.06  
% 0.38/1.06  fof(f9,axiom,(
% 0.38/1.06    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 0.38/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.38/1.06  
% 0.38/1.06  fof(f25,plain,(
% 0.38/1.06    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 0.38/1.06    inference(ennf_transformation,[],[f9])).
% 0.38/1.06  
% 0.38/1.06  fof(f26,plain,(
% 0.38/1.06    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.38/1.06    inference(flattening,[],[f25])).
% 0.38/1.06  
% 0.38/1.06  fof(f49,plain,(
% 0.38/1.06    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.38/1.06    inference(cnf_transformation,[],[f26])).
% 0.38/1.06  
% 0.38/1.06  fof(f14,axiom,(
% 0.38/1.06    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,X1))))),
% 0.38/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.38/1.06  
% 0.38/1.06  fof(f30,plain,(
% 0.38/1.06    ! [X0] : (! [X1] : (k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.38/1.06    inference(ennf_transformation,[],[f14])).
% 0.38/1.06  
% 0.38/1.06  fof(f54,plain,(
% 0.38/1.06    ( ! [X0,X1] : (k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.38/1.06    inference(cnf_transformation,[],[f30])).
% 0.38/1.06  
% 0.38/1.06  fof(f17,axiom,(
% 0.38/1.06    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))),
% 0.38/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.38/1.06  
% 0.38/1.06  fof(f58,plain,(
% 0.38/1.06    ( ! [X0] : (k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))) )),
% 0.38/1.06    inference(cnf_transformation,[],[f17])).
% 0.38/1.06  
% 0.38/1.06  fof(f12,axiom,(
% 0.38/1.06    ! [X0,X1] : (v1_relat_1(X1) => k5_relat_1(X1,k6_relat_1(X0)) = k8_relat_1(X0,X1))),
% 0.38/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.38/1.06  
% 0.38/1.06  fof(f28,plain,(
% 0.38/1.06    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = k8_relat_1(X0,X1) | ~v1_relat_1(X1))),
% 0.38/1.06    inference(ennf_transformation,[],[f12])).
% 0.38/1.06  
% 0.38/1.06  fof(f52,plain,(
% 0.38/1.06    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = k8_relat_1(X0,X1) | ~v1_relat_1(X1)) )),
% 0.38/1.06    inference(cnf_transformation,[],[f28])).
% 0.38/1.06  
% 0.38/1.06  fof(f13,axiom,(
% 0.38/1.06    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(X1,k8_relat_1(X0,X2)) = k8_relat_1(X0,k5_relat_1(X1,X2))))),
% 0.38/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.38/1.06  
% 0.38/1.06  fof(f29,plain,(
% 0.38/1.06    ! [X0,X1] : (! [X2] : (k5_relat_1(X1,k8_relat_1(X0,X2)) = k8_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.38/1.06    inference(ennf_transformation,[],[f13])).
% 0.38/1.06  
% 0.38/1.06  fof(f53,plain,(
% 0.38/1.06    ( ! [X2,X0,X1] : (k5_relat_1(X1,k8_relat_1(X0,X2)) = k8_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 0.38/1.06    inference(cnf_transformation,[],[f29])).
% 0.38/1.06  
% 0.38/1.06  fof(f20,axiom,(
% 0.38/1.06    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 0.38/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.38/1.06  
% 0.38/1.06  fof(f35,plain,(
% 0.38/1.06    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 0.38/1.06    inference(ennf_transformation,[],[f20])).
% 0.38/1.06  
% 0.38/1.06  fof(f61,plain,(
% 0.38/1.06    ( ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 0.38/1.06    inference(cnf_transformation,[],[f35])).
% 0.38/1.06  
% 0.38/1.06  fof(f57,plain,(
% 0.38/1.06    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.38/1.06    inference(cnf_transformation,[],[f16])).
% 0.38/1.06  
% 0.38/1.06  fof(f19,axiom,(
% 0.38/1.06    ! [X0] : (v1_relat_1(X0) => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0)),
% 0.38/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.38/1.06  
% 0.38/1.06  fof(f34,plain,(
% 0.38/1.06    ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0))),
% 0.38/1.06    inference(ennf_transformation,[],[f19])).
% 0.38/1.06  
% 0.38/1.06  fof(f60,plain,(
% 0.38/1.06    ( ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0)) )),
% 0.38/1.06    inference(cnf_transformation,[],[f34])).
% 0.38/1.06  
% 0.38/1.06  fof(f23,conjecture,(
% 0.38/1.06    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 0.38/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.38/1.06  
% 0.38/1.06  fof(f24,negated_conjecture,(
% 0.38/1.06    ~! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 0.38/1.06    inference(negated_conjecture,[],[f23])).
% 0.38/1.06  
% 0.38/1.06  fof(f38,plain,(
% 0.38/1.06    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))),
% 0.38/1.06    inference(ennf_transformation,[],[f24])).
% 0.38/1.06  
% 0.38/1.06  fof(f39,plain,(
% 0.38/1.06    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 0.38/1.06    introduced(choice_axiom,[])).
% 0.38/1.06  
% 0.38/1.06  fof(f40,plain,(
% 0.38/1.06    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 0.38/1.06    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f38,f39])).
% 0.38/1.06  
% 0.38/1.06  fof(f64,plain,(
% 0.38/1.06    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 0.38/1.06    inference(cnf_transformation,[],[f40])).
% 0.38/1.06  
% 0.38/1.06  fof(f73,plain,(
% 0.38/1.06    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))),
% 0.38/1.06    inference(definition_unfolding,[],[f64,f70])).
% 0.38/1.06  
% 0.38/1.06  cnf(c_2,plain,
% 0.38/1.06      ( v1_relat_1(k6_relat_1(X0)) ),
% 0.38/1.06      inference(cnf_transformation,[],[f50]) ).
% 0.38/1.06  
% 0.38/1.06  cnf(c_442,plain,
% 0.38/1.06      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 0.38/1.06      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 0.38/1.06  
% 0.38/1.06  cnf(c_14,plain,
% 0.38/1.06      ( ~ v1_relat_1(X0)
% 0.38/1.06      | k1_setfam_1(k6_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1)) ),
% 0.38/1.06      inference(cnf_transformation,[],[f72]) ).
% 0.38/1.06  
% 0.38/1.06  cnf(c_433,plain,
% 0.38/1.06      ( k1_setfam_1(k6_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1))
% 0.38/1.06      | v1_relat_1(X0) != iProver_top ),
% 0.38/1.06      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 0.38/1.06  
% 0.38/1.06  cnf(c_796,plain,
% 0.38/1.06      ( k1_setfam_1(k6_enumset1(k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
% 0.38/1.06      inference(superposition,[status(thm)],[c_442,c_433]) ).
% 0.38/1.06  
% 0.38/1.06  cnf(c_9,plain,
% 0.38/1.06      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 0.38/1.06      inference(cnf_transformation,[],[f56]) ).
% 0.38/1.06  
% 0.38/1.06  cnf(c_797,plain,
% 0.38/1.06      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
% 0.38/1.06      inference(light_normalisation,[status(thm)],[c_796,c_9]) ).
% 0.38/1.06  
% 0.38/1.06  cnf(c_0,plain,
% 0.38/1.06      ( r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0) ),
% 0.38/1.06      inference(cnf_transformation,[],[f71]) ).
% 0.38/1.06  
% 0.38/1.06  cnf(c_444,plain,
% 0.38/1.06      ( r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0) = iProver_top ),
% 0.38/1.06      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 0.38/1.06  
% 0.38/1.06  cnf(c_1199,plain,
% 0.38/1.06      ( r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X0) = iProver_top ),
% 0.38/1.06      inference(demodulation,[status(thm)],[c_797,c_444]) ).
% 0.38/1.06  
% 0.38/1.06  cnf(c_11,plain,
% 0.38/1.06      ( ~ r1_tarski(k1_relat_1(X0),X1)
% 0.38/1.06      | ~ v1_relat_1(X0)
% 0.38/1.06      | k5_relat_1(k6_relat_1(X1),X0) = X0 ),
% 0.38/1.06      inference(cnf_transformation,[],[f59]) ).
% 0.38/1.06  
% 0.38/1.06  cnf(c_436,plain,
% 0.38/1.06      ( k5_relat_1(k6_relat_1(X0),X1) = X1
% 0.38/1.06      | r1_tarski(k1_relat_1(X1),X0) != iProver_top
% 0.38/1.06      | v1_relat_1(X1) != iProver_top ),
% 0.38/1.06      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 0.38/1.06  
% 0.38/1.06  cnf(c_2799,plain,
% 0.38/1.06      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k6_relat_1(X1)
% 0.38/1.06      | r1_tarski(X1,X0) != iProver_top
% 0.38/1.06      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 0.38/1.06      inference(superposition,[status(thm)],[c_9,c_436]) ).
% 0.38/1.06  
% 0.38/1.06  cnf(c_15,plain,
% 0.38/1.06      ( ~ v1_relat_1(X0) | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
% 0.38/1.06      inference(cnf_transformation,[],[f63]) ).
% 0.38/1.06  
% 0.38/1.06  cnf(c_432,plain,
% 0.38/1.06      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
% 0.38/1.06      | v1_relat_1(X1) != iProver_top ),
% 0.38/1.06      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 0.38/1.06  
% 0.38/1.06  cnf(c_802,plain,
% 0.38/1.06      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
% 0.38/1.06      inference(superposition,[status(thm)],[c_442,c_432]) ).
% 0.38/1.06  
% 0.38/1.06  cnf(c_2803,plain,
% 0.38/1.06      ( k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X0)
% 0.38/1.06      | r1_tarski(X0,X1) != iProver_top
% 0.38/1.06      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 0.38/1.06      inference(demodulation,[status(thm)],[c_2799,c_802]) ).
% 0.38/1.06  
% 0.38/1.06  cnf(c_50,plain,
% 0.38/1.06      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 0.38/1.06      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 0.38/1.06  
% 0.38/1.06  cnf(c_5501,plain,
% 0.38/1.06      ( r1_tarski(X0,X1) != iProver_top
% 0.38/1.06      | k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X0) ),
% 0.38/1.06      inference(global_propositional_subsumption,[status(thm)],[c_2803,c_50]) ).
% 0.38/1.06  
% 0.38/1.06  cnf(c_5502,plain,
% 0.38/1.06      ( k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X0)
% 0.38/1.06      | r1_tarski(X0,X1) != iProver_top ),
% 0.38/1.06      inference(renaming,[status(thm)],[c_5501]) ).
% 0.38/1.06  
% 0.38/1.06  cnf(c_5507,plain,
% 0.38/1.06      ( k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X0) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
% 0.38/1.06      inference(superposition,[status(thm)],[c_1199,c_5502]) ).
% 0.38/1.06  
% 0.38/1.06  cnf(c_1,plain,
% 0.38/1.06      ( ~ v1_relat_1(X0) | ~ v1_relat_1(X1) | v1_relat_1(k5_relat_1(X1,X0)) ),
% 0.38/1.06      inference(cnf_transformation,[],[f49]) ).
% 0.38/1.06  
% 0.38/1.06  cnf(c_443,plain,
% 0.38/1.06      ( v1_relat_1(X0) != iProver_top
% 0.38/1.06      | v1_relat_1(X1) != iProver_top
% 0.38/1.06      | v1_relat_1(k5_relat_1(X1,X0)) = iProver_top ),
% 0.38/1.06      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 0.38/1.06  
% 0.38/1.06  cnf(c_2106,plain,
% 0.38/1.06      ( v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = iProver_top
% 0.38/1.06      | v1_relat_1(k6_relat_1(X0)) != iProver_top
% 0.38/1.06      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 0.38/1.06      inference(superposition,[status(thm)],[c_802,c_443]) ).
% 0.38/1.06  
% 0.38/1.06  cnf(c_3535,plain,
% 0.38/1.06      ( v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = iProver_top
% 0.38/1.06      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 0.38/1.06      inference(global_propositional_subsumption,[status(thm)],[c_2106,c_50]) ).
% 0.38/1.06  
% 0.38/1.06  cnf(c_3541,plain,
% 0.38/1.06      ( v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = iProver_top ),
% 0.38/1.06      inference(forward_subsumption_resolution,[status(thm)],[c_3535,c_442]) ).
% 0.38/1.06  
% 0.38/1.06  cnf(c_1200,plain,
% 0.38/1.06      ( k1_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(X0)),X1)) = k1_relat_1(k7_relat_1(X0,X1))
% 0.38/1.06      | v1_relat_1(X0) != iProver_top ),
% 0.38/1.06      inference(demodulation,[status(thm)],[c_797,c_433]) ).
% 0.38/1.06  
% 0.38/1.06  cnf(c_3550,plain,
% 0.38/1.06      ( k1_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X2)) = k1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)) ),
% 0.38/1.06      inference(superposition,[status(thm)],[c_3541,c_1200]) ).
% 0.38/1.06  
% 0.38/1.06  cnf(c_7046,plain,
% 0.38/1.06      ( k1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0)) = k1_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)))) ),
% 0.38/1.06      inference(superposition,[status(thm)],[c_5507,c_3550]) ).
% 0.38/1.06  
% 0.38/1.06  cnf(c_2797,plain,
% 0.38/1.06      ( k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X0),X1)) = k7_relat_1(k6_relat_1(X0),X1)
% 0.38/1.06      | v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) != iProver_top ),
% 0.38/1.06      inference(superposition,[status(thm)],[c_1199,c_436]) ).
% 0.38/1.06  
% 0.38/1.06  cnf(c_5488,plain,
% 0.38/1.06      ( k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X0),X1)) = k7_relat_1(k6_relat_1(X0),X1) ),
% 0.38/1.06      inference(global_propositional_subsumption,[status(thm)],[c_2797,c_3541]) ).
% 0.38/1.06  
% 0.38/1.06  cnf(c_3547,plain,
% 0.38/1.06      ( k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X1),X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X0) ),
% 0.38/1.06      inference(superposition,[status(thm)],[c_3541,c_432]) ).
% 0.38/1.06  
% 0.38/1.06  cnf(c_5495,plain,
% 0.38/1.06      ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0) = k7_relat_1(k6_relat_1(X0),X1) ),
% 0.38/1.06      inference(superposition,[status(thm)],[c_5488,c_3547]) ).
% 0.38/1.06  
% 0.38/1.06  cnf(c_6,plain,
% 0.38/1.06      ( ~ v1_relat_1(X0)
% 0.38/1.06      | ~ v1_relat_1(X1)
% 0.38/1.06      | k5_relat_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k5_relat_1(X1,X0)) ),
% 0.38/1.06      inference(cnf_transformation,[],[f54]) ).
% 0.38/1.06  
% 0.38/1.06  cnf(c_438,plain,
% 0.38/1.06      ( k5_relat_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k5_relat_1(X1,X0))
% 0.38/1.06      | v1_relat_1(X0) != iProver_top
% 0.38/1.06      | v1_relat_1(X1) != iProver_top ),
% 0.38/1.06      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 0.38/1.06  
% 0.38/1.06  cnf(c_2027,plain,
% 0.38/1.06      ( k5_relat_1(k4_relat_1(k6_relat_1(X0)),k4_relat_1(X1)) = k4_relat_1(k5_relat_1(X1,k6_relat_1(X0)))
% 0.38/1.06      | v1_relat_1(X1) != iProver_top ),
% 0.38/1.06      inference(superposition,[status(thm)],[c_442,c_438]) ).
% 0.38/1.06  
% 0.38/1.06  cnf(c_10,plain,
% 0.38/1.06      ( k4_relat_1(k6_relat_1(X0)) = k6_relat_1(X0) ),
% 0.38/1.06      inference(cnf_transformation,[],[f58]) ).
% 0.38/1.06  
% 0.38/1.06  cnf(c_2028,plain,
% 0.38/1.06      ( k4_relat_1(k5_relat_1(X0,k6_relat_1(X1))) = k5_relat_1(k6_relat_1(X1),k4_relat_1(X0))
% 0.38/1.06      | v1_relat_1(X0) != iProver_top ),
% 0.38/1.06      inference(light_normalisation,[status(thm)],[c_2027,c_10]) ).
% 0.38/1.06  
% 0.38/1.06  cnf(c_3548,plain,
% 0.38/1.06      ( k4_relat_1(k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X2))) = k5_relat_1(k6_relat_1(X2),k4_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
% 0.38/1.06      inference(superposition,[status(thm)],[c_3541,c_2028]) ).
% 0.38/1.06  
% 0.38/1.06  cnf(c_4,plain,
% 0.38/1.06      ( ~ v1_relat_1(X0) | k5_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X1,X0) ),
% 0.38/1.06      inference(cnf_transformation,[],[f52]) ).
% 0.38/1.06  
% 0.38/1.06  cnf(c_440,plain,
% 0.38/1.06      ( k5_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X1,X0)
% 0.38/1.06      | v1_relat_1(X0) != iProver_top ),
% 0.38/1.06      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 0.38/1.06  
% 0.38/1.06  cnf(c_3551,plain,
% 0.38/1.06      ( k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X2)) = k8_relat_1(X2,k7_relat_1(k6_relat_1(X0),X1)) ),
% 0.38/1.06      inference(superposition,[status(thm)],[c_3541,c_440]) ).
% 0.38/1.06  
% 0.38/1.06  cnf(c_3571,plain,
% 0.38/1.06      ( k5_relat_1(k6_relat_1(X0),k4_relat_1(k7_relat_1(k6_relat_1(X1),X2))) = k4_relat_1(k8_relat_1(X0,k7_relat_1(k6_relat_1(X1),X2))) ),
% 0.38/1.06      inference(light_normalisation,[status(thm)],[c_3548,c_3551]) ).
% 0.38/1.06  
% 0.38/1.06  cnf(c_2098,plain,
% 0.38/1.06      ( k4_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k5_relat_1(k6_relat_1(X1),k4_relat_1(k6_relat_1(X0))) ),
% 0.38/1.06      inference(superposition,[status(thm)],[c_442,c_2028]) ).
% 0.38/1.06  
% 0.38/1.06  cnf(c_2099,plain,
% 0.38/1.06      ( k4_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) ),
% 0.38/1.06      inference(light_normalisation,[status(thm)],[c_2098,c_10,c_802]) ).
% 0.38/1.06  
% 0.38/1.06  cnf(c_2100,plain,
% 0.38/1.06      ( k4_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
% 0.38/1.06      inference(demodulation,[status(thm)],[c_2099,c_802]) ).
% 0.38/1.06  
% 0.38/1.06  cnf(c_5,plain,
% 0.38/1.06      ( ~ v1_relat_1(X0)
% 0.38/1.06      | ~ v1_relat_1(X1)
% 0.38/1.06      | k8_relat_1(X2,k5_relat_1(X0,X1)) = k5_relat_1(X0,k8_relat_1(X2,X1)) ),
% 0.38/1.06      inference(cnf_transformation,[],[f53]) ).
% 0.38/1.06  
% 0.38/1.06  cnf(c_439,plain,
% 0.38/1.06      ( k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2))
% 0.38/1.06      | v1_relat_1(X1) != iProver_top
% 0.38/1.06      | v1_relat_1(X2) != iProver_top ),
% 0.38/1.06      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 0.38/1.06  
% 0.38/1.06  cnf(c_2820,plain,
% 0.38/1.06      ( k8_relat_1(X0,k5_relat_1(k6_relat_1(X1),X2)) = k5_relat_1(k6_relat_1(X1),k8_relat_1(X0,X2))
% 0.38/1.06      | v1_relat_1(X2) != iProver_top ),
% 0.38/1.06      inference(superposition,[status(thm)],[c_442,c_439]) ).
% 0.38/1.06  
% 0.38/1.06  cnf(c_3348,plain,
% 0.38/1.06      ( k8_relat_1(X0,k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) = k5_relat_1(k6_relat_1(X1),k8_relat_1(X0,k6_relat_1(X2))) ),
% 0.38/1.06      inference(superposition,[status(thm)],[c_442,c_2820]) ).
% 0.38/1.06  
% 0.38/1.06  cnf(c_1113,plain,
% 0.38/1.06      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k8_relat_1(X1,k6_relat_1(X0)) ),
% 0.38/1.06      inference(superposition,[status(thm)],[c_442,c_440]) ).
% 0.38/1.06  
% 0.38/1.06  cnf(c_1852,plain,
% 0.38/1.06      ( k8_relat_1(X0,k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X0),X1) ),
% 0.38/1.06      inference(light_normalisation,[status(thm)],[c_1113,c_802]) ).
% 0.38/1.06  
% 0.38/1.06  cnf(c_3350,plain,
% 0.38/1.06      ( k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X1),X2)) = k8_relat_1(X1,k7_relat_1(k6_relat_1(X2),X0)) ),
% 0.38/1.06      inference(demodulation,[status(thm)],[c_3348,c_802,c_1852]) ).
% 0.38/1.06  
% 0.38/1.06  cnf(c_3573,plain,
% 0.38/1.06      ( k4_relat_1(k8_relat_1(X0,k7_relat_1(k6_relat_1(X1),X2))) = k8_relat_1(X2,k7_relat_1(k6_relat_1(X1),X0)) ),
% 0.38/1.06      inference(demodulation,[status(thm)],[c_3571,c_2100,c_3350]) ).
% 0.38/1.06  
% 0.38/1.06  cnf(c_3666,plain,
% 0.38/1.06      ( k8_relat_1(X0,k7_relat_1(k6_relat_1(X1),X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) ),
% 0.38/1.06      inference(demodulation,[status(thm)],[c_3547,c_3350]) ).
% 0.38/1.06  
% 0.38/1.06  cnf(c_4739,plain,
% 0.38/1.06      ( k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)) = k8_relat_1(X2,k7_relat_1(k6_relat_1(X1),X0)) ),
% 0.38/1.06      inference(light_normalisation,[status(thm)],[c_3573,c_3666]) ).
% 0.38/1.06  
% 0.38/1.06  cnf(c_4740,plain,
% 0.38/1.06      ( k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X1),X0) ),
% 0.38/1.06      inference(demodulation,[status(thm)],[c_4739,c_3666]) ).
% 0.38/1.06  
% 0.38/1.06  cnf(c_5521,plain,
% 0.38/1.06      ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0) = k4_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
% 0.38/1.06      inference(superposition,[status(thm)],[c_5495,c_4740]) ).
% 0.38/1.06  
% 0.38/1.06  cnf(c_5522,plain,
% 0.38/1.06      ( k4_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k7_relat_1(k6_relat_1(X0),X1) ),
% 0.38/1.06      inference(light_normalisation,[status(thm)],[c_5521,c_5495]) ).
% 0.38/1.06  
% 0.38/1.06  cnf(c_5528,plain,
% 0.38/1.06      ( k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X1),X0) ),
% 0.38/1.06      inference(superposition,[status(thm)],[c_5522,c_2100]) ).
% 0.38/1.06  
% 0.38/1.06  cnf(c_13,plain,
% 0.38/1.06      ( ~ v1_relat_1(X0) | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ),
% 0.38/1.06      inference(cnf_transformation,[],[f61]) ).
% 0.38/1.06  
% 0.38/1.06  cnf(c_434,plain,
% 0.38/1.06      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
% 0.38/1.06      | v1_relat_1(X0) != iProver_top ),
% 0.38/1.06      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 0.38/1.06  
% 0.38/1.06  cnf(c_619,plain,
% 0.38/1.06      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(k2_relat_1(k6_relat_1(X0)))) = k6_relat_1(X0) ),
% 0.38/1.06      inference(superposition,[status(thm)],[c_442,c_434]) ).
% 0.38/1.06  
% 0.38/1.06  cnf(c_8,plain,
% 0.38/1.06      ( k2_relat_1(k6_relat_1(X0)) = X0 ),
% 0.38/1.06      inference(cnf_transformation,[],[f57]) ).
% 0.38/1.06  
% 0.38/1.06  cnf(c_620,plain,
% 0.38/1.06      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X0)) = k6_relat_1(X0) ),
% 0.38/1.06      inference(light_normalisation,[status(thm)],[c_619,c_8]) ).
% 0.38/1.06  
% 0.38/1.06  cnf(c_1503,plain,
% 0.38/1.06      ( k7_relat_1(k6_relat_1(X0),X0) = k6_relat_1(X0) ),
% 0.38/1.06      inference(superposition,[status(thm)],[c_620,c_802]) ).
% 0.38/1.06  
% 0.38/1.06  cnf(c_3683,plain,
% 0.38/1.06      ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X1) = k8_relat_1(X0,k6_relat_1(X1)) ),
% 0.38/1.06      inference(superposition,[status(thm)],[c_1503,c_3666]) ).
% 0.38/1.06  
% 0.38/1.06  cnf(c_3688,plain,
% 0.38/1.06      ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X1) = k7_relat_1(k6_relat_1(X0),X1) ),
% 0.38/1.06      inference(light_normalisation,[status(thm)],[c_3683,c_1852]) ).
% 0.38/1.06  
% 0.38/1.06  cnf(c_5578,plain,
% 0.38/1.06      ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0) = k7_relat_1(k6_relat_1(X1),X0) ),
% 0.38/1.06      inference(superposition,[status(thm)],[c_5528,c_3688]) ).
% 0.38/1.06  
% 0.38/1.06  cnf(c_7048,plain,
% 0.38/1.06      ( k1_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)))) = k1_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
% 0.38/1.06      inference(light_normalisation,[status(thm)],[c_7046,c_5578]) ).
% 0.38/1.06  
% 0.38/1.06  cnf(c_7171,plain,
% 0.38/1.06      ( k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
% 0.38/1.06      inference(superposition,[status(thm)],[c_7048,c_9]) ).
% 0.38/1.06  
% 0.38/1.06  cnf(c_3553,plain,
% 0.38/1.06      ( k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)))) = k7_relat_1(k6_relat_1(X0),X1) ),
% 0.38/1.06      inference(superposition,[status(thm)],[c_3541,c_434]) ).
% 0.38/1.06  
% 0.38/1.06  cnf(c_3959,plain,
% 0.38/1.06      ( k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X0),X1) ),
% 0.38/1.06      inference(demodulation,[status(thm)],[c_3551,c_3666]) ).
% 0.38/1.06  
% 0.38/1.06  cnf(c_4088,plain,
% 0.38/1.06      ( k7_relat_1(k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X0),X1) = k7_relat_1(k6_relat_1(X0),X1) ),
% 0.38/1.06      inference(superposition,[status(thm)],[c_3553,c_3959]) ).
% 0.38/1.06  
% 0.38/1.06  cnf(c_5151,plain,
% 0.38/1.06      ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),k2_relat_1(k7_relat_1(k6_relat_1(X1),X0))) = k4_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
% 0.38/1.06      inference(superposition,[status(thm)],[c_4088,c_4740]) ).
% 0.38/1.06  
% 0.38/1.06  cnf(c_5156,plain,
% 0.38/1.06      ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),k2_relat_1(k7_relat_1(k6_relat_1(X1),X0))) = k7_relat_1(k6_relat_1(X0),X1) ),
% 0.38/1.06      inference(demodulation,[status(thm)],[c_5151,c_2100]) ).
% 0.38/1.06  
% 0.38/1.06  cnf(c_7038,plain,
% 0.38/1.06      ( k7_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),k2_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))))) = k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
% 0.38/1.06      inference(superposition,[status(thm)],[c_5507,c_5156]) ).
% 0.38/1.06  
% 0.38/1.06  cnf(c_5569,plain,
% 0.38/1.06      ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X1) = k7_relat_1(k6_relat_1(X1),X0) ),
% 0.38/1.06      inference(superposition,[status(thm)],[c_5528,c_5495]) ).
% 0.38/1.06  
% 0.38/1.06  cnf(c_7068,plain,
% 0.38/1.06      ( k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X0) ),
% 0.38/1.06      inference(demodulation,[status(thm)],[c_7038,c_8,c_5569]) ).
% 0.38/1.06  
% 0.38/1.06  cnf(c_7069,plain,
% 0.38/1.06      ( k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
% 0.38/1.06      inference(light_normalisation,[status(thm)],[c_7068,c_5507]) ).
% 0.38/1.06  
% 0.38/1.06  cnf(c_7423,plain,
% 0.38/1.06      ( k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(k6_relat_1(X1),X0))) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
% 0.38/1.06      inference(superposition,[status(thm)],[c_7171,c_7069]) ).
% 0.38/1.06  
% 0.38/1.06  cnf(c_12,plain,
% 0.38/1.06      ( ~ v1_relat_1(X0) | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ),
% 0.38/1.06      inference(cnf_transformation,[],[f60]) ).
% 0.38/1.06  
% 0.38/1.06  cnf(c_435,plain,
% 0.38/1.06      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
% 0.38/1.06      | v1_relat_1(X0) != iProver_top ),
% 0.38/1.06      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 0.38/1.06  
% 0.38/1.06  cnf(c_3552,plain,
% 0.38/1.06      ( k5_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),k7_relat_1(k6_relat_1(X0),X1)) = k7_relat_1(k6_relat_1(X0),X1) ),
% 0.38/1.06      inference(superposition,[status(thm)],[c_3541,c_435]) ).
% 0.38/1.06  
% 0.38/1.06  cnf(c_3978,plain,
% 0.38/1.06      ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k7_relat_1(k6_relat_1(X0),X1) ),
% 0.38/1.06      inference(superposition,[status(thm)],[c_3552,c_3547]) ).
% 0.38/1.06  
% 0.38/1.06  cnf(c_4752,plain,
% 0.38/1.06      ( k7_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X1),X0) = k4_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
% 0.38/1.06      inference(superposition,[status(thm)],[c_3978,c_4740]) ).
% 0.38/1.06  
% 0.38/1.06  cnf(c_4754,plain,
% 0.38/1.06      ( k7_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X1),X0) = k7_relat_1(k6_relat_1(X1),X0) ),
% 0.38/1.06      inference(light_normalisation,[status(thm)],[c_4752,c_2100]) ).
% 0.38/1.06  
% 0.38/1.06  cnf(c_5535,plain,
% 0.38/1.06      ( k7_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(k6_relat_1(X1),X0))),X1) = k7_relat_1(k6_relat_1(X0),X1) ),
% 0.38/1.06      inference(demodulation,[status(thm)],[c_5528,c_4754]) ).
% 0.38/1.06  
% 0.38/1.06  cnf(c_7680,plain,
% 0.38/1.06      ( k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X1) = k7_relat_1(k6_relat_1(X0),X1) ),
% 0.38/1.06      inference(demodulation,[status(thm)],[c_7423,c_5535]) ).
% 0.38/1.06  
% 0.38/1.06  cnf(c_8149,plain,
% 0.38/1.06      ( k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(k6_relat_1(X1),X0))))) = k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(k6_relat_1(X1),X0))) ),
% 0.38/1.06      inference(superposition,[status(thm)],[c_7680,c_7423]) ).
% 0.38/1.06  
% 0.38/1.06  cnf(c_8157,plain,
% 0.38/1.06      ( k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(k6_relat_1(X1),X0))) = k7_relat_1(k6_relat_1(X1),X0) ),
% 0.38/1.06      inference(superposition,[status(thm)],[c_7680,c_5528]) ).
% 0.38/1.06  
% 0.38/1.06  cnf(c_8207,plain,
% 0.38/1.06      ( k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k7_relat_1(k6_relat_1(X0),X1) ),
% 0.38/1.06      inference(light_normalisation,[status(thm)],[c_8149,c_8157]) ).
% 0.38/1.06  
% 0.38/1.06  cnf(c_16,negated_conjecture,
% 0.38/1.06      ( k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) ),
% 0.38/1.06      inference(cnf_transformation,[],[f73]) ).
% 0.38/1.06  
% 0.38/1.06  cnf(c_1201,plain,
% 0.38/1.06      ( k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(sK0),sK1))) != k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) ),
% 0.38/1.06      inference(demodulation,[status(thm)],[c_797,c_16]) ).
% 0.38/1.06  
% 0.38/1.06  cnf(c_1502,plain,
% 0.38/1.06      ( k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(sK0),sK1))) != k7_relat_1(k6_relat_1(sK0),sK1) ),
% 0.38/1.06      inference(demodulation,[status(thm)],[c_802,c_1201]) ).
% 0.38/1.06  
% 0.38/1.06  cnf(c_5533,plain,
% 0.38/1.06      ( k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(sK1),sK0))) != k7_relat_1(k6_relat_1(sK1),sK0) ),
% 0.38/1.06      inference(demodulation,[status(thm)],[c_5528,c_1502]) ).
% 0.38/1.06  
% 0.38/1.06  cnf(c_8223,plain,
% 0.38/1.06      ( k7_relat_1(k6_relat_1(sK1),sK0) != k7_relat_1(k6_relat_1(sK1),sK0) ),
% 0.38/1.06      inference(demodulation,[status(thm)],[c_8207,c_5533]) ).
% 0.38/1.06  
% 0.38/1.06  cnf(c_8224,plain,
% 0.38/1.06      ( $false ),
% 0.38/1.06      inference(equality_resolution_simp,[status(thm)],[c_8223]) ).
% 0.38/1.06  
% 0.38/1.06  
% 0.38/1.06  % SZS output end CNFRefutation for theBenchmark.p
% 0.38/1.06  
% 0.38/1.06  ------                               Statistics
% 0.38/1.06  
% 0.38/1.06  ------ General
% 0.38/1.06  
% 0.38/1.06  abstr_ref_over_cycles:                  0
% 0.38/1.06  abstr_ref_under_cycles:                 0
% 0.38/1.06  gc_basic_clause_elim:                   0
% 0.38/1.06  forced_gc_time:                         0
% 0.38/1.06  parsing_time:                           0.007
% 0.38/1.06  unif_index_cands_time:                  0.
% 0.38/1.06  unif_index_add_time:                    0.
% 0.38/1.06  orderings_time:                         0.
% 0.38/1.06  out_proof_time:                         0.009
% 0.38/1.06  total_time:                             0.246
% 0.38/1.06  num_of_symbols:                         44
% 0.38/1.06  num_of_terms:                           12544
% 0.38/1.06  
% 0.38/1.06  ------ Preprocessing
% 0.38/1.06  
% 0.38/1.06  num_of_splits:                          0
% 0.38/1.06  num_of_split_atoms:                     0
% 0.38/1.06  num_of_reused_defs:                     0
% 0.38/1.06  num_eq_ax_congr_red:                    6
% 0.38/1.06  num_of_sem_filtered_clauses:            1
% 0.38/1.06  num_of_subtypes:                        0
% 0.38/1.06  monotx_restored_types:                  0
% 0.38/1.06  sat_num_of_epr_types:                   0
% 0.38/1.06  sat_num_of_non_cyclic_types:            0
% 0.38/1.06  sat_guarded_non_collapsed_types:        0
% 0.38/1.06  num_pure_diseq_elim:                    0
% 0.38/1.06  simp_replaced_by:                       0
% 0.38/1.06  res_preprocessed:                       78
% 0.38/1.06  prep_upred:                             0
% 0.38/1.06  prep_unflattend:                        1
% 0.38/1.06  smt_new_axioms:                         0
% 0.38/1.06  pred_elim_cands:                        2
% 0.38/1.06  pred_elim:                              0
% 0.38/1.06  pred_elim_cl:                           0
% 0.38/1.06  pred_elim_cycles:                       1
% 0.38/1.06  merged_defs:                            0
% 0.38/1.06  merged_defs_ncl:                        0
% 0.38/1.06  bin_hyper_res:                          0
% 0.38/1.06  prep_cycles:                            3
% 0.38/1.06  pred_elim_time:                         0.
% 0.38/1.06  splitting_time:                         0.
% 0.38/1.06  sem_filter_time:                        0.
% 0.38/1.06  monotx_time:                            0.
% 0.38/1.06  subtype_inf_time:                       0.
% 0.38/1.06  
% 0.38/1.06  ------ Problem properties
% 0.38/1.06  
% 0.38/1.06  clauses:                                17
% 0.38/1.06  conjectures:                            1
% 0.38/1.06  epr:                                    0
% 0.38/1.06  horn:                                   17
% 0.38/1.06  ground:                                 1
% 0.38/1.06  unary:                                  6
% 0.38/1.06  binary:                                 5
% 0.38/1.06  lits:                                   35
% 0.38/1.06  lits_eq:                                14
% 0.38/1.06  fd_pure:                                0
% 0.38/1.06  fd_pseudo:                              0
% 0.38/1.06  fd_cond:                                0
% 0.38/1.06  fd_pseudo_cond:                         0
% 0.38/1.06  ac_symbols:                             0
% 0.38/1.06  
% 0.38/1.06  ------ Propositional Solver
% 0.38/1.06  
% 0.38/1.06  prop_solver_calls:                      24
% 0.38/1.06  prop_fast_solver_calls:                 532
% 0.38/1.06  smt_solver_calls:                       0
% 0.38/1.06  smt_fast_solver_calls:                  0
% 0.38/1.06  prop_num_of_clauses:                    3538
% 0.38/1.06  prop_preprocess_simplified:             6918
% 0.38/1.06  prop_fo_subsumed:                       4
% 0.38/1.06  prop_solver_time:                       0.
% 0.38/1.06  smt_solver_time:                        0.
% 0.38/1.06  smt_fast_solver_time:                   0.
% 0.38/1.06  prop_fast_solver_time:                  0.
% 0.38/1.06  prop_unsat_core_time:                   0.
% 0.38/1.06  
% 0.38/1.06  ------ QBF
% 0.38/1.06  
% 0.38/1.06  qbf_q_res:                              0
% 0.38/1.06  qbf_num_tautologies:                    0
% 0.38/1.06  qbf_prep_cycles:                        0
% 0.38/1.06  
% 0.38/1.06  ------ BMC1
% 0.38/1.06  
% 0.38/1.06  bmc1_current_bound:                     -1
% 0.38/1.06  bmc1_last_solved_bound:                 -1
% 0.38/1.06  bmc1_unsat_core_size:                   -1
% 0.38/1.06  bmc1_unsat_core_parents_size:           -1
% 0.38/1.06  bmc1_merge_next_fun:                    0
% 0.38/1.06  bmc1_unsat_core_clauses_time:           0.
% 0.38/1.06  
% 0.38/1.06  ------ Instantiation
% 0.38/1.06  
% 0.38/1.06  inst_num_of_clauses:                    984
% 0.38/1.06  inst_num_in_passive:                    16
% 0.38/1.06  inst_num_in_active:                     506
% 0.38/1.06  inst_num_in_unprocessed:                462
% 0.38/1.06  inst_num_of_loops:                      530
% 0.38/1.06  inst_num_of_learning_restarts:          0
% 0.38/1.06  inst_num_moves_active_passive:          23
% 0.38/1.06  inst_lit_activity:                      0
% 0.38/1.06  inst_lit_activity_moves:                1
% 0.38/1.06  inst_num_tautologies:                   0
% 0.38/1.06  inst_num_prop_implied:                  0
% 0.38/1.06  inst_num_existing_simplified:           0
% 0.38/1.06  inst_num_eq_res_simplified:             0
% 0.38/1.06  inst_num_child_elim:                    0
% 0.38/1.06  inst_num_of_dismatching_blockings:      226
% 0.38/1.06  inst_num_of_non_proper_insts:           442
% 0.38/1.06  inst_num_of_duplicates:                 0
% 0.38/1.06  inst_inst_num_from_inst_to_res:         0
% 0.38/1.06  inst_dismatching_checking_time:         0.
% 0.38/1.06  
% 0.38/1.06  ------ Resolution
% 0.38/1.06  
% 0.38/1.06  res_num_of_clauses:                     0
% 0.38/1.06  res_num_in_passive:                     0
% 0.38/1.06  res_num_in_active:                      0
% 0.38/1.06  res_num_of_loops:                       81
% 0.38/1.06  res_forward_subset_subsumed:            62
% 0.38/1.06  res_backward_subset_subsumed:           2
% 0.38/1.06  res_forward_subsumed:                   0
% 0.38/1.06  res_backward_subsumed:                  0
% 0.38/1.06  res_forward_subsumption_resolution:     0
% 0.38/1.06  res_backward_subsumption_resolution:    0
% 0.38/1.06  res_clause_to_clause_subsumption:       1338
% 0.38/1.06  res_orphan_elimination:                 0
% 0.38/1.06  res_tautology_del:                      46
% 0.38/1.06  res_num_eq_res_simplified:              0
% 0.38/1.06  res_num_sel_changes:                    0
% 0.38/1.06  res_moves_from_active_to_pass:          0
% 0.38/1.06  
% 0.38/1.06  ------ Superposition
% 0.38/1.06  
% 0.38/1.06  sup_time_total:                         0.
% 0.38/1.06  sup_time_generating:                    0.
% 0.38/1.06  sup_time_sim_full:                      0.
% 0.38/1.06  sup_time_sim_immed:                     0.
% 0.38/1.06  
% 0.38/1.06  sup_num_of_clauses:                     269
% 0.38/1.06  sup_num_in_active:                      87
% 0.38/1.06  sup_num_in_passive:                     182
% 0.38/1.06  sup_num_of_loops:                       105
% 0.38/1.06  sup_fw_superposition:                   527
% 0.38/1.06  sup_bw_superposition:                   664
% 0.38/1.06  sup_immediate_simplified:               341
% 0.38/1.06  sup_given_eliminated:                   1
% 0.38/1.06  comparisons_done:                       0
% 0.38/1.06  comparisons_avoided:                    0
% 0.38/1.06  
% 0.38/1.06  ------ Simplifications
% 0.38/1.06  
% 0.38/1.06  
% 0.38/1.06  sim_fw_subset_subsumed:                 1
% 0.38/1.06  sim_bw_subset_subsumed:                 5
% 0.38/1.06  sim_fw_subsumed:                        43
% 0.38/1.06  sim_bw_subsumed:                        0
% 0.38/1.06  sim_fw_subsumption_res:                 2
% 0.38/1.06  sim_bw_subsumption_res:                 0
% 0.38/1.06  sim_tautology_del:                      4
% 0.38/1.06  sim_eq_tautology_del:                   45
% 0.38/1.06  sim_eq_res_simp:                        0
% 0.38/1.06  sim_fw_demodulated:                     74
% 0.38/1.06  sim_bw_demodulated:                     24
% 0.38/1.06  sim_light_normalised:                   266
% 0.38/1.06  sim_joinable_taut:                      0
% 0.38/1.06  sim_joinable_simp:                      0
% 0.38/1.06  sim_ac_normalised:                      0
% 0.38/1.06  sim_smt_subsumption:                    0
% 0.38/1.06  
%------------------------------------------------------------------------------
