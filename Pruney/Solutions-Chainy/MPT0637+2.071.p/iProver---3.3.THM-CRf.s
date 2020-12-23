%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:50:07 EST 2020

% Result     : Theorem 7.67s
% Output     : CNFRefutation 7.67s
% Verified   : 
% Statistics : Number of formulae       :  178 (7501 expanded)
%              Number of clauses        :  105 (2910 expanded)
%              Number of leaves         :   22 (1568 expanded)
%              Depth                    :   39
%              Number of atoms          :  310 (11873 expanded)
%              Number of equality atoms :  195 (6299 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    5 (   2 average)
%              Maximal term depth       :   10 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f21,axiom,(
    ! [X0] :
      ( v5_relat_1(k6_relat_1(X0),X0)
      & v4_relat_1(k6_relat_1(X0),X0)
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( v4_relat_1(k6_relat_1(X0),X0)
      & v1_relat_1(k6_relat_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f21])).

fof(f68,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f5,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f1,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f4])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f47,f48])).

fof(f72,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f46,f71])).

fof(f73,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f45,f72])).

fof(f74,plain,(
    ! [X0,X1] : k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f49,f73])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k7_relat_1(X1,k1_setfam_1(k4_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f56,f74])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k3_xboole_0(k2_relat_1(X1),X0) = k2_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k2_relat_1(X1),X0) = k2_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k2_relat_1(X1),X0) = k2_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k4_enumset1(k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),X0)) = k2_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f53,f74])).

fof(f16,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k5_relat_1(X1,k6_relat_1(X0)) = k8_relat_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = k8_relat_1(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = k8_relat_1(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f61,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f17,axiom,(
    ! [X0] : k4_relat_1(k6_relat_1(X0)) = k6_relat_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0] : k4_relat_1(k6_relat_1(X0)) = k6_relat_1(X0) ),
    inference(cnf_transformation,[],[f17])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f52,f74])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f69,plain,(
    ! [X0] : v4_relat_1(k6_relat_1(X0),X0) ),
    inference(cnf_transformation,[],[f24])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f26,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f35])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f39])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f22,conjecture,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f22])).

fof(f42,plain,(
    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f23])).

fof(f43,plain,
    ( ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))
   => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f42,f43])).

fof(f70,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f44])).

fof(f78,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))) ),
    inference(definition_unfolding,[],[f70,f74])).

cnf(c_19,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_607,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(X0,k1_setfam_1(k4_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),X1))) = k7_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_615,plain,
    ( k7_relat_1(X0,k1_setfam_1(k4_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),X1))) = k7_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | k1_setfam_1(k4_enumset1(k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X0),X1)) = k2_relat_1(k8_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_618,plain,
    ( k1_setfam_1(k4_enumset1(k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X0),X1)) = k2_relat_1(k8_relat_1(X1,X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1311,plain,
    ( k1_setfam_1(k4_enumset1(k2_relat_1(k6_relat_1(X0)),k2_relat_1(k6_relat_1(X0)),k2_relat_1(k6_relat_1(X0)),k2_relat_1(k6_relat_1(X0)),k2_relat_1(k6_relat_1(X0)),X1)) = k2_relat_1(k8_relat_1(X1,k6_relat_1(X0))) ),
    inference(superposition,[status(thm)],[c_607,c_618])).

cnf(c_11,plain,
    ( k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1312,plain,
    ( k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)) = k2_relat_1(k8_relat_1(X1,k6_relat_1(X0))) ),
    inference(light_normalisation,[status(thm)],[c_1311,c_11])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X1,X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_617,plain,
    ( k5_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X1,X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_930,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k8_relat_1(X1,k6_relat_1(X0)) ),
    inference(superposition,[status(thm)],[c_607,c_617])).

cnf(c_17,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_608,plain,
    ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_818,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(superposition,[status(thm)],[c_607,c_608])).

cnf(c_931,plain,
    ( k8_relat_1(X0,k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(light_normalisation,[status(thm)],[c_930,c_818])).

cnf(c_1313,plain,
    ( k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)) = k2_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
    inference(demodulation,[status(thm)],[c_1312,c_931])).

cnf(c_1667,plain,
    ( k7_relat_1(X0,k2_relat_1(k7_relat_1(k6_relat_1(X1),k1_relat_1(X0)))) = k7_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_615,c_1313])).

cnf(c_1672,plain,
    ( k7_relat_1(k6_relat_1(X0),k2_relat_1(k7_relat_1(k6_relat_1(X1),k1_relat_1(k6_relat_1(X0))))) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(superposition,[status(thm)],[c_607,c_1667])).

cnf(c_12,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1673,plain,
    ( k7_relat_1(k6_relat_1(X0),k2_relat_1(k7_relat_1(k6_relat_1(X1),X0))) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(light_normalisation,[status(thm)],[c_1672,c_12])).

cnf(c_10,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k5_relat_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k5_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_612,plain,
    ( k5_relat_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k5_relat_1(X1,X0))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1201,plain,
    ( k5_relat_1(k4_relat_1(k6_relat_1(X0)),k4_relat_1(X1)) = k4_relat_1(k5_relat_1(X1,k6_relat_1(X0)))
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_607,c_612])).

cnf(c_13,plain,
    ( k4_relat_1(k6_relat_1(X0)) = k6_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1202,plain,
    ( k4_relat_1(k5_relat_1(X0,k6_relat_1(X1))) = k5_relat_1(k6_relat_1(X1),k4_relat_1(X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1201,c_13])).

cnf(c_1236,plain,
    ( k4_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k5_relat_1(k6_relat_1(X1),k4_relat_1(k6_relat_1(X0))) ),
    inference(superposition,[status(thm)],[c_607,c_1202])).

cnf(c_1237,plain,
    ( k4_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) ),
    inference(light_normalisation,[status(thm)],[c_1236,c_13,c_818])).

cnf(c_1238,plain,
    ( k4_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(demodulation,[status(thm)],[c_1237,c_818])).

cnf(c_1686,plain,
    ( k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X1) = k4_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
    inference(superposition,[status(thm)],[c_1673,c_1238])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(X0,k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X2))) = k7_relat_1(k7_relat_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_619,plain,
    ( k7_relat_1(X0,k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X2))) = k7_relat_1(k7_relat_1(X0,X1),X2)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1304,plain,
    ( k7_relat_1(k6_relat_1(X0),k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X2))) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) ),
    inference(superposition,[status(thm)],[c_607,c_619])).

cnf(c_1505,plain,
    ( k7_relat_1(k6_relat_1(X0),k2_relat_1(k7_relat_1(k6_relat_1(X1),X2))) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X2),X1) ),
    inference(demodulation,[status(thm)],[c_1304,c_1313])).

cnf(c_1511,plain,
    ( k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X2) = k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X2),X1),X0)) ),
    inference(superposition,[status(thm)],[c_1505,c_1238])).

cnf(c_1698,plain,
    ( k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X1) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(demodulation,[status(thm)],[c_1686,c_1238,c_1511])).

cnf(c_7,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_18,plain,
    ( v4_relat_1(k6_relat_1(X0),X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_218,plain,
    ( ~ v1_relat_1(X0)
    | X1 != X2
    | k7_relat_1(X0,X2) = X0
    | k6_relat_1(X1) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_18])).

cnf(c_219,plain,
    ( ~ v1_relat_1(k6_relat_1(X0))
    | k7_relat_1(k6_relat_1(X0),X0) = k6_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_218])).

cnf(c_223,plain,
    ( k7_relat_1(k6_relat_1(X0),X0) = k6_relat_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_219,c_19])).

cnf(c_1510,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X1),X0) = k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
    inference(superposition,[status(thm)],[c_1505,c_223])).

cnf(c_1519,plain,
    ( k7_relat_1(k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X0),X1)),X1) = k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X1),X0))) ),
    inference(demodulation,[status(thm)],[c_1510,c_1511])).

cnf(c_1520,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0) = k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
    inference(light_normalisation,[status(thm)],[c_1519,c_223,c_1238])).

cnf(c_2007,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X1))) ),
    inference(superposition,[status(thm)],[c_1698,c_1520])).

cnf(c_2021,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
    inference(demodulation,[status(thm)],[c_2007,c_1698])).

cnf(c_0,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | v1_relat_1(k5_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_621,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k5_relat_1(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1241,plain,
    ( v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_818,c_621])).

cnf(c_21,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2837,plain,
    ( v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1241,c_21])).

cnf(c_2844,plain,
    ( v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = iProver_top
    | v1_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X1),X0)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1673,c_2837])).

cnf(c_3141,plain,
    ( v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_607,c_2844])).

cnf(c_3158,plain,
    ( v1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1505,c_3141])).

cnf(c_3163,plain,
    ( k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X1),X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X0) ),
    inference(superposition,[status(thm)],[c_3141,c_608])).

cnf(c_3166,plain,
    ( k4_relat_1(k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X2))) = k5_relat_1(k6_relat_1(X2),k4_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
    inference(superposition,[status(thm)],[c_3141,c_1202])).

cnf(c_3168,plain,
    ( k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X2)) = k8_relat_1(X2,k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(superposition,[status(thm)],[c_3141,c_617])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | k8_relat_1(X1,k7_relat_1(X0,X2)) = k7_relat_1(k8_relat_1(X1,X0),X2) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_616,plain,
    ( k8_relat_1(X0,k7_relat_1(X1,X2)) = k7_relat_1(k8_relat_1(X0,X1),X2)
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_985,plain,
    ( k8_relat_1(X0,k7_relat_1(k6_relat_1(X1),X2)) = k7_relat_1(k8_relat_1(X0,k6_relat_1(X1)),X2) ),
    inference(superposition,[status(thm)],[c_607,c_616])).

cnf(c_986,plain,
    ( k8_relat_1(X0,k7_relat_1(k6_relat_1(X1),X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) ),
    inference(light_normalisation,[status(thm)],[c_985,c_931])).

cnf(c_3171,plain,
    ( k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X0),X1) ),
    inference(demodulation,[status(thm)],[c_3168,c_986])).

cnf(c_3173,plain,
    ( k5_relat_1(k6_relat_1(X0),k4_relat_1(k7_relat_1(k6_relat_1(X1),X2))) = k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)) ),
    inference(demodulation,[status(thm)],[c_3166,c_3171])).

cnf(c_3174,plain,
    ( k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)) = k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X2),X1)) ),
    inference(demodulation,[status(thm)],[c_3173,c_1238])).

cnf(c_3175,plain,
    ( k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X1),X0) ),
    inference(demodulation,[status(thm)],[c_3163,c_3174])).

cnf(c_4794,plain,
    ( k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X2) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) ),
    inference(demodulation,[status(thm)],[c_1511,c_3175])).

cnf(c_15,plain,
    ( r1_tarski(k5_relat_1(X0,k6_relat_1(X1)),X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_610,plain,
    ( r1_tarski(k5_relat_1(X0,k6_relat_1(X1)),X0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1030,plain,
    ( r1_tarski(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X1)) = iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_818,c_610])).

cnf(c_4843,plain,
    ( r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2),k6_relat_1(X2)) = iProver_top
    | v1_relat_1(k6_relat_1(X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4794,c_1030])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_614,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_16,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_relat_1(X1)) = X0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_609,plain,
    ( k5_relat_1(X0,k6_relat_1(X1)) = X0
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1795,plain,
    ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X1))) = X0
    | r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_614,c_609])).

cnf(c_17896,plain,
    ( k5_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2),k6_relat_1(k2_relat_1(k6_relat_1(X2)))) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)
    | v1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)) != iProver_top
    | v1_relat_1(k6_relat_1(X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4843,c_1795])).

cnf(c_4821,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X0),k2_relat_1(k7_relat_1(k6_relat_1(X1),X2))),X3) = k5_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X3),k6_relat_1(X0)) ),
    inference(superposition,[status(thm)],[c_4794,c_3171])).

cnf(c_4872,plain,
    ( k5_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2),k6_relat_1(X3)) = k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X3),X1),X0),X2) ),
    inference(light_normalisation,[status(thm)],[c_4821,c_1505])).

cnf(c_1079,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X1) = k8_relat_1(X0,k6_relat_1(X1)) ),
    inference(superposition,[status(thm)],[c_223,c_986])).

cnf(c_1080,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X1) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(light_normalisation,[status(thm)],[c_1079,c_931])).

cnf(c_4844,plain,
    ( k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2),X2) = k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X2) ),
    inference(superposition,[status(thm)],[c_4794,c_1080])).

cnf(c_4865,plain,
    ( k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2),X2) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) ),
    inference(demodulation,[status(thm)],[c_4844,c_4794])).

cnf(c_5023,plain,
    ( k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X0) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0) ),
    inference(superposition,[status(thm)],[c_1520,c_4865])).

cnf(c_5049,plain,
    ( k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X0) = k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
    inference(light_normalisation,[status(thm)],[c_5023,c_1520])).

cnf(c_5104,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X2))),X1),X0) = k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X2))) ),
    inference(superposition,[status(thm)],[c_5049,c_1505])).

cnf(c_5112,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2))),X1),X0) = k6_relat_1(k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2))) ),
    inference(light_normalisation,[status(thm)],[c_5104,c_4794])).

cnf(c_4808,plain,
    ( k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2))),X3) = k7_relat_1(k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X2),X3) ),
    inference(superposition,[status(thm)],[c_4794,c_4794])).

cnf(c_4876,plain,
    ( k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2))),X3) = k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2),X3) ),
    inference(demodulation,[status(thm)],[c_4808,c_4794])).

cnf(c_5113,plain,
    ( k7_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2),X1),X0) = k6_relat_1(k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2))) ),
    inference(demodulation,[status(thm)],[c_5112,c_4876])).

cnf(c_1690,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X0),k2_relat_1(k7_relat_1(k6_relat_1(X1),X2))),X2) = k7_relat_1(k6_relat_1(X0),k2_relat_1(k7_relat_1(k6_relat_1(X2),X1))) ),
    inference(superposition,[status(thm)],[c_1673,c_1505])).

cnf(c_1695,plain,
    ( k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2),X1) = k7_relat_1(k6_relat_1(X0),k2_relat_1(k7_relat_1(k6_relat_1(X1),X2))) ),
    inference(light_normalisation,[status(thm)],[c_1690,c_1505])).

cnf(c_1696,plain,
    ( k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2),X1) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X2),X1) ),
    inference(demodulation,[status(thm)],[c_1695,c_1505])).

cnf(c_5114,plain,
    ( k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2),X0) = k6_relat_1(k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X2),X1))) ),
    inference(light_normalisation,[status(thm)],[c_5113,c_1696])).

cnf(c_17900,plain,
    ( k6_relat_1(k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2))) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X0)
    | v1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X0)) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_17896,c_11,c_4872,c_5114])).

cnf(c_18382,plain,
    ( v1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X0)) != iProver_top
    | k6_relat_1(k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2))) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_17900,c_21])).

cnf(c_18383,plain,
    ( k6_relat_1(k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2))) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X0)
    | v1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_18382])).

cnf(c_18388,plain,
    ( k6_relat_1(k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2))) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X0) ),
    inference(superposition,[status(thm)],[c_3158,c_18383])).

cnf(c_19063,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X0),k2_relat_1(k7_relat_1(k6_relat_1(X1),X0))),X1) = k6_relat_1(k2_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X1),X0))))) ),
    inference(superposition,[status(thm)],[c_2021,c_18388])).

cnf(c_19440,plain,
    ( k6_relat_1(k2_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))))) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(light_normalisation,[status(thm)],[c_19063,c_1080,c_1673])).

cnf(c_19441,plain,
    ( k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(demodulation,[status(thm)],[c_19440,c_11])).

cnf(c_20,negated_conjecture,
    ( k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1029,plain,
    ( k6_relat_1(k1_setfam_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))) != k7_relat_1(k6_relat_1(sK0),sK1) ),
    inference(demodulation,[status(thm)],[c_818,c_20])).

cnf(c_1401,plain,
    ( k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(sK1),sK0))) != k7_relat_1(k6_relat_1(sK0),sK1) ),
    inference(demodulation,[status(thm)],[c_1313,c_1029])).

cnf(c_19761,plain,
    ( k7_relat_1(k6_relat_1(sK0),sK1) != k7_relat_1(k6_relat_1(sK0),sK1) ),
    inference(demodulation,[status(thm)],[c_19441,c_1401])).

cnf(c_19795,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_19761])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n014.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:15:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 7.67/1.44  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.67/1.44  
% 7.67/1.44  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.67/1.44  
% 7.67/1.44  ------  iProver source info
% 7.67/1.44  
% 7.67/1.44  git: date: 2020-06-30 10:37:57 +0100
% 7.67/1.44  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.67/1.44  git: non_committed_changes: false
% 7.67/1.44  git: last_make_outside_of_git: false
% 7.67/1.44  
% 7.67/1.44  ------ 
% 7.67/1.44  
% 7.67/1.44  ------ Input Options
% 7.67/1.44  
% 7.67/1.44  --out_options                           all
% 7.67/1.44  --tptp_safe_out                         true
% 7.67/1.44  --problem_path                          ""
% 7.67/1.44  --include_path                          ""
% 7.67/1.44  --clausifier                            res/vclausify_rel
% 7.67/1.44  --clausifier_options                    ""
% 7.67/1.44  --stdin                                 false
% 7.67/1.44  --stats_out                             all
% 7.67/1.44  
% 7.67/1.44  ------ General Options
% 7.67/1.44  
% 7.67/1.44  --fof                                   false
% 7.67/1.44  --time_out_real                         305.
% 7.67/1.44  --time_out_virtual                      -1.
% 7.67/1.44  --symbol_type_check                     false
% 7.67/1.44  --clausify_out                          false
% 7.67/1.44  --sig_cnt_out                           false
% 7.67/1.44  --trig_cnt_out                          false
% 7.67/1.44  --trig_cnt_out_tolerance                1.
% 7.67/1.44  --trig_cnt_out_sk_spl                   false
% 7.67/1.44  --abstr_cl_out                          false
% 7.67/1.44  
% 7.67/1.44  ------ Global Options
% 7.67/1.44  
% 7.67/1.44  --schedule                              default
% 7.67/1.44  --add_important_lit                     false
% 7.67/1.44  --prop_solver_per_cl                    1000
% 7.67/1.44  --min_unsat_core                        false
% 7.67/1.44  --soft_assumptions                      false
% 7.67/1.44  --soft_lemma_size                       3
% 7.67/1.44  --prop_impl_unit_size                   0
% 7.67/1.44  --prop_impl_unit                        []
% 7.67/1.44  --share_sel_clauses                     true
% 7.67/1.44  --reset_solvers                         false
% 7.67/1.44  --bc_imp_inh                            [conj_cone]
% 7.67/1.44  --conj_cone_tolerance                   3.
% 7.67/1.44  --extra_neg_conj                        none
% 7.67/1.44  --large_theory_mode                     true
% 7.67/1.44  --prolific_symb_bound                   200
% 7.67/1.44  --lt_threshold                          2000
% 7.67/1.44  --clause_weak_htbl                      true
% 7.67/1.44  --gc_record_bc_elim                     false
% 7.67/1.44  
% 7.67/1.44  ------ Preprocessing Options
% 7.67/1.44  
% 7.67/1.44  --preprocessing_flag                    true
% 7.67/1.44  --time_out_prep_mult                    0.1
% 7.67/1.44  --splitting_mode                        input
% 7.67/1.44  --splitting_grd                         true
% 7.67/1.44  --splitting_cvd                         false
% 7.67/1.44  --splitting_cvd_svl                     false
% 7.67/1.44  --splitting_nvd                         32
% 7.67/1.44  --sub_typing                            true
% 7.67/1.44  --prep_gs_sim                           true
% 7.67/1.44  --prep_unflatten                        true
% 7.67/1.44  --prep_res_sim                          true
% 7.67/1.44  --prep_upred                            true
% 7.67/1.44  --prep_sem_filter                       exhaustive
% 7.67/1.44  --prep_sem_filter_out                   false
% 7.67/1.44  --pred_elim                             true
% 7.67/1.44  --res_sim_input                         true
% 7.67/1.44  --eq_ax_congr_red                       true
% 7.67/1.44  --pure_diseq_elim                       true
% 7.67/1.44  --brand_transform                       false
% 7.67/1.44  --non_eq_to_eq                          false
% 7.67/1.44  --prep_def_merge                        true
% 7.67/1.44  --prep_def_merge_prop_impl              false
% 7.67/1.44  --prep_def_merge_mbd                    true
% 7.67/1.44  --prep_def_merge_tr_red                 false
% 7.67/1.44  --prep_def_merge_tr_cl                  false
% 7.67/1.44  --smt_preprocessing                     true
% 7.67/1.44  --smt_ac_axioms                         fast
% 7.67/1.44  --preprocessed_out                      false
% 7.67/1.44  --preprocessed_stats                    false
% 7.67/1.44  
% 7.67/1.44  ------ Abstraction refinement Options
% 7.67/1.44  
% 7.67/1.44  --abstr_ref                             []
% 7.67/1.44  --abstr_ref_prep                        false
% 7.67/1.44  --abstr_ref_until_sat                   false
% 7.67/1.44  --abstr_ref_sig_restrict                funpre
% 7.67/1.44  --abstr_ref_af_restrict_to_split_sk     false
% 7.67/1.44  --abstr_ref_under                       []
% 7.67/1.44  
% 7.67/1.44  ------ SAT Options
% 7.67/1.44  
% 7.67/1.44  --sat_mode                              false
% 7.67/1.44  --sat_fm_restart_options                ""
% 7.67/1.44  --sat_gr_def                            false
% 7.67/1.44  --sat_epr_types                         true
% 7.67/1.44  --sat_non_cyclic_types                  false
% 7.67/1.44  --sat_finite_models                     false
% 7.67/1.44  --sat_fm_lemmas                         false
% 7.67/1.44  --sat_fm_prep                           false
% 7.67/1.44  --sat_fm_uc_incr                        true
% 7.67/1.44  --sat_out_model                         small
% 7.67/1.44  --sat_out_clauses                       false
% 7.67/1.44  
% 7.67/1.44  ------ QBF Options
% 7.67/1.44  
% 7.67/1.44  --qbf_mode                              false
% 7.67/1.44  --qbf_elim_univ                         false
% 7.67/1.44  --qbf_dom_inst                          none
% 7.67/1.44  --qbf_dom_pre_inst                      false
% 7.67/1.44  --qbf_sk_in                             false
% 7.67/1.44  --qbf_pred_elim                         true
% 7.67/1.44  --qbf_split                             512
% 7.67/1.44  
% 7.67/1.44  ------ BMC1 Options
% 7.67/1.44  
% 7.67/1.44  --bmc1_incremental                      false
% 7.67/1.44  --bmc1_axioms                           reachable_all
% 7.67/1.44  --bmc1_min_bound                        0
% 7.67/1.44  --bmc1_max_bound                        -1
% 7.67/1.44  --bmc1_max_bound_default                -1
% 7.67/1.44  --bmc1_symbol_reachability              true
% 7.67/1.44  --bmc1_property_lemmas                  false
% 7.67/1.44  --bmc1_k_induction                      false
% 7.67/1.44  --bmc1_non_equiv_states                 false
% 7.67/1.44  --bmc1_deadlock                         false
% 7.67/1.44  --bmc1_ucm                              false
% 7.67/1.44  --bmc1_add_unsat_core                   none
% 7.67/1.44  --bmc1_unsat_core_children              false
% 7.67/1.44  --bmc1_unsat_core_extrapolate_axioms    false
% 7.67/1.44  --bmc1_out_stat                         full
% 7.67/1.44  --bmc1_ground_init                      false
% 7.67/1.44  --bmc1_pre_inst_next_state              false
% 7.67/1.44  --bmc1_pre_inst_state                   false
% 7.67/1.44  --bmc1_pre_inst_reach_state             false
% 7.67/1.44  --bmc1_out_unsat_core                   false
% 7.67/1.44  --bmc1_aig_witness_out                  false
% 7.67/1.44  --bmc1_verbose                          false
% 7.67/1.44  --bmc1_dump_clauses_tptp                false
% 7.67/1.44  --bmc1_dump_unsat_core_tptp             false
% 7.67/1.44  --bmc1_dump_file                        -
% 7.67/1.44  --bmc1_ucm_expand_uc_limit              128
% 7.67/1.44  --bmc1_ucm_n_expand_iterations          6
% 7.67/1.44  --bmc1_ucm_extend_mode                  1
% 7.67/1.44  --bmc1_ucm_init_mode                    2
% 7.67/1.44  --bmc1_ucm_cone_mode                    none
% 7.67/1.44  --bmc1_ucm_reduced_relation_type        0
% 7.67/1.44  --bmc1_ucm_relax_model                  4
% 7.67/1.44  --bmc1_ucm_full_tr_after_sat            true
% 7.67/1.44  --bmc1_ucm_expand_neg_assumptions       false
% 7.67/1.44  --bmc1_ucm_layered_model                none
% 7.67/1.44  --bmc1_ucm_max_lemma_size               10
% 7.67/1.44  
% 7.67/1.44  ------ AIG Options
% 7.67/1.44  
% 7.67/1.44  --aig_mode                              false
% 7.67/1.44  
% 7.67/1.44  ------ Instantiation Options
% 7.67/1.44  
% 7.67/1.44  --instantiation_flag                    true
% 7.67/1.44  --inst_sos_flag                         true
% 7.67/1.44  --inst_sos_phase                        true
% 7.67/1.44  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.67/1.44  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.67/1.44  --inst_lit_sel_side                     num_symb
% 7.67/1.44  --inst_solver_per_active                1400
% 7.67/1.44  --inst_solver_calls_frac                1.
% 7.67/1.44  --inst_passive_queue_type               priority_queues
% 7.67/1.44  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.67/1.44  --inst_passive_queues_freq              [25;2]
% 7.67/1.44  --inst_dismatching                      true
% 7.67/1.44  --inst_eager_unprocessed_to_passive     true
% 7.67/1.44  --inst_prop_sim_given                   true
% 7.67/1.44  --inst_prop_sim_new                     false
% 7.67/1.44  --inst_subs_new                         false
% 7.67/1.44  --inst_eq_res_simp                      false
% 7.67/1.44  --inst_subs_given                       false
% 7.67/1.44  --inst_orphan_elimination               true
% 7.67/1.44  --inst_learning_loop_flag               true
% 7.67/1.44  --inst_learning_start                   3000
% 7.67/1.44  --inst_learning_factor                  2
% 7.67/1.44  --inst_start_prop_sim_after_learn       3
% 7.67/1.44  --inst_sel_renew                        solver
% 7.67/1.44  --inst_lit_activity_flag                true
% 7.67/1.44  --inst_restr_to_given                   false
% 7.67/1.44  --inst_activity_threshold               500
% 7.67/1.44  --inst_out_proof                        true
% 7.67/1.44  
% 7.67/1.44  ------ Resolution Options
% 7.67/1.44  
% 7.67/1.44  --resolution_flag                       true
% 7.67/1.44  --res_lit_sel                           adaptive
% 7.67/1.44  --res_lit_sel_side                      none
% 7.67/1.44  --res_ordering                          kbo
% 7.67/1.44  --res_to_prop_solver                    active
% 7.67/1.44  --res_prop_simpl_new                    false
% 7.67/1.44  --res_prop_simpl_given                  true
% 7.67/1.44  --res_passive_queue_type                priority_queues
% 7.67/1.44  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.67/1.44  --res_passive_queues_freq               [15;5]
% 7.67/1.44  --res_forward_subs                      full
% 7.67/1.44  --res_backward_subs                     full
% 7.67/1.44  --res_forward_subs_resolution           true
% 7.67/1.44  --res_backward_subs_resolution          true
% 7.67/1.44  --res_orphan_elimination                true
% 7.67/1.44  --res_time_limit                        2.
% 7.67/1.44  --res_out_proof                         true
% 7.67/1.44  
% 7.67/1.44  ------ Superposition Options
% 7.67/1.44  
% 7.67/1.44  --superposition_flag                    true
% 7.67/1.44  --sup_passive_queue_type                priority_queues
% 7.67/1.44  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.67/1.44  --sup_passive_queues_freq               [8;1;4]
% 7.67/1.44  --demod_completeness_check              fast
% 7.67/1.44  --demod_use_ground                      true
% 7.67/1.44  --sup_to_prop_solver                    passive
% 7.67/1.44  --sup_prop_simpl_new                    true
% 7.67/1.44  --sup_prop_simpl_given                  true
% 7.67/1.44  --sup_fun_splitting                     true
% 7.67/1.44  --sup_smt_interval                      50000
% 7.67/1.44  
% 7.67/1.44  ------ Superposition Simplification Setup
% 7.67/1.44  
% 7.67/1.44  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.67/1.44  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.67/1.44  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.67/1.44  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.67/1.44  --sup_full_triv                         [TrivRules;PropSubs]
% 7.67/1.44  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.67/1.44  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.67/1.44  --sup_immed_triv                        [TrivRules]
% 7.67/1.44  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.67/1.44  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.67/1.44  --sup_immed_bw_main                     []
% 7.67/1.44  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.67/1.44  --sup_input_triv                        [Unflattening;TrivRules]
% 7.67/1.44  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.67/1.44  --sup_input_bw                          []
% 7.67/1.44  
% 7.67/1.44  ------ Combination Options
% 7.67/1.44  
% 7.67/1.44  --comb_res_mult                         3
% 7.67/1.44  --comb_sup_mult                         2
% 7.67/1.44  --comb_inst_mult                        10
% 7.67/1.44  
% 7.67/1.44  ------ Debug Options
% 7.67/1.44  
% 7.67/1.44  --dbg_backtrace                         false
% 7.67/1.44  --dbg_dump_prop_clauses                 false
% 7.67/1.44  --dbg_dump_prop_clauses_file            -
% 7.67/1.44  --dbg_out_stat                          false
% 7.67/1.44  ------ Parsing...
% 7.67/1.44  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.67/1.44  
% 7.67/1.44  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.67/1.44  
% 7.67/1.44  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.67/1.44  
% 7.67/1.44  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.67/1.44  ------ Proving...
% 7.67/1.44  ------ Problem Properties 
% 7.67/1.44  
% 7.67/1.44  
% 7.67/1.44  clauses                                 20
% 7.67/1.44  conjectures                             1
% 7.67/1.44  EPR                                     0
% 7.67/1.44  Horn                                    20
% 7.67/1.44  unary                                   6
% 7.67/1.44  binary                                  9
% 7.67/1.44  lits                                    41
% 7.67/1.44  lits eq                                 14
% 7.67/1.44  fd_pure                                 0
% 7.67/1.44  fd_pseudo                               0
% 7.67/1.44  fd_cond                                 0
% 7.67/1.44  fd_pseudo_cond                          0
% 7.67/1.44  AC symbols                              0
% 7.67/1.44  
% 7.67/1.44  ------ Schedule dynamic 5 is on 
% 7.67/1.44  
% 7.67/1.44  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.67/1.44  
% 7.67/1.44  
% 7.67/1.44  ------ 
% 7.67/1.44  Current options:
% 7.67/1.44  ------ 
% 7.67/1.44  
% 7.67/1.44  ------ Input Options
% 7.67/1.44  
% 7.67/1.44  --out_options                           all
% 7.67/1.44  --tptp_safe_out                         true
% 7.67/1.44  --problem_path                          ""
% 7.67/1.44  --include_path                          ""
% 7.67/1.44  --clausifier                            res/vclausify_rel
% 7.67/1.44  --clausifier_options                    ""
% 7.67/1.44  --stdin                                 false
% 7.67/1.44  --stats_out                             all
% 7.67/1.44  
% 7.67/1.44  ------ General Options
% 7.67/1.44  
% 7.67/1.44  --fof                                   false
% 7.67/1.44  --time_out_real                         305.
% 7.67/1.44  --time_out_virtual                      -1.
% 7.67/1.44  --symbol_type_check                     false
% 7.67/1.44  --clausify_out                          false
% 7.67/1.44  --sig_cnt_out                           false
% 7.67/1.44  --trig_cnt_out                          false
% 7.67/1.44  --trig_cnt_out_tolerance                1.
% 7.67/1.44  --trig_cnt_out_sk_spl                   false
% 7.67/1.44  --abstr_cl_out                          false
% 7.67/1.44  
% 7.67/1.44  ------ Global Options
% 7.67/1.44  
% 7.67/1.44  --schedule                              default
% 7.67/1.44  --add_important_lit                     false
% 7.67/1.44  --prop_solver_per_cl                    1000
% 7.67/1.44  --min_unsat_core                        false
% 7.67/1.44  --soft_assumptions                      false
% 7.67/1.44  --soft_lemma_size                       3
% 7.67/1.44  --prop_impl_unit_size                   0
% 7.67/1.44  --prop_impl_unit                        []
% 7.67/1.44  --share_sel_clauses                     true
% 7.67/1.44  --reset_solvers                         false
% 7.67/1.44  --bc_imp_inh                            [conj_cone]
% 7.67/1.44  --conj_cone_tolerance                   3.
% 7.67/1.44  --extra_neg_conj                        none
% 7.67/1.44  --large_theory_mode                     true
% 7.67/1.44  --prolific_symb_bound                   200
% 7.67/1.44  --lt_threshold                          2000
% 7.67/1.44  --clause_weak_htbl                      true
% 7.67/1.44  --gc_record_bc_elim                     false
% 7.67/1.44  
% 7.67/1.44  ------ Preprocessing Options
% 7.67/1.44  
% 7.67/1.44  --preprocessing_flag                    true
% 7.67/1.44  --time_out_prep_mult                    0.1
% 7.67/1.44  --splitting_mode                        input
% 7.67/1.44  --splitting_grd                         true
% 7.67/1.44  --splitting_cvd                         false
% 7.67/1.44  --splitting_cvd_svl                     false
% 7.67/1.44  --splitting_nvd                         32
% 7.67/1.44  --sub_typing                            true
% 7.67/1.44  --prep_gs_sim                           true
% 7.67/1.44  --prep_unflatten                        true
% 7.67/1.44  --prep_res_sim                          true
% 7.67/1.44  --prep_upred                            true
% 7.67/1.44  --prep_sem_filter                       exhaustive
% 7.67/1.44  --prep_sem_filter_out                   false
% 7.67/1.44  --pred_elim                             true
% 7.67/1.44  --res_sim_input                         true
% 7.67/1.44  --eq_ax_congr_red                       true
% 7.67/1.44  --pure_diseq_elim                       true
% 7.67/1.44  --brand_transform                       false
% 7.67/1.44  --non_eq_to_eq                          false
% 7.67/1.44  --prep_def_merge                        true
% 7.67/1.44  --prep_def_merge_prop_impl              false
% 7.67/1.44  --prep_def_merge_mbd                    true
% 7.67/1.44  --prep_def_merge_tr_red                 false
% 7.67/1.44  --prep_def_merge_tr_cl                  false
% 7.67/1.44  --smt_preprocessing                     true
% 7.67/1.44  --smt_ac_axioms                         fast
% 7.67/1.44  --preprocessed_out                      false
% 7.67/1.44  --preprocessed_stats                    false
% 7.67/1.44  
% 7.67/1.44  ------ Abstraction refinement Options
% 7.67/1.44  
% 7.67/1.44  --abstr_ref                             []
% 7.67/1.44  --abstr_ref_prep                        false
% 7.67/1.44  --abstr_ref_until_sat                   false
% 7.67/1.44  --abstr_ref_sig_restrict                funpre
% 7.67/1.44  --abstr_ref_af_restrict_to_split_sk     false
% 7.67/1.44  --abstr_ref_under                       []
% 7.67/1.44  
% 7.67/1.44  ------ SAT Options
% 7.67/1.44  
% 7.67/1.44  --sat_mode                              false
% 7.67/1.44  --sat_fm_restart_options                ""
% 7.67/1.44  --sat_gr_def                            false
% 7.67/1.44  --sat_epr_types                         true
% 7.67/1.44  --sat_non_cyclic_types                  false
% 7.67/1.44  --sat_finite_models                     false
% 7.67/1.44  --sat_fm_lemmas                         false
% 7.67/1.44  --sat_fm_prep                           false
% 7.67/1.44  --sat_fm_uc_incr                        true
% 7.67/1.44  --sat_out_model                         small
% 7.67/1.44  --sat_out_clauses                       false
% 7.67/1.44  
% 7.67/1.44  ------ QBF Options
% 7.67/1.44  
% 7.67/1.44  --qbf_mode                              false
% 7.67/1.44  --qbf_elim_univ                         false
% 7.67/1.44  --qbf_dom_inst                          none
% 7.67/1.44  --qbf_dom_pre_inst                      false
% 7.67/1.44  --qbf_sk_in                             false
% 7.67/1.44  --qbf_pred_elim                         true
% 7.67/1.44  --qbf_split                             512
% 7.67/1.44  
% 7.67/1.44  ------ BMC1 Options
% 7.67/1.44  
% 7.67/1.44  --bmc1_incremental                      false
% 7.67/1.44  --bmc1_axioms                           reachable_all
% 7.67/1.44  --bmc1_min_bound                        0
% 7.67/1.44  --bmc1_max_bound                        -1
% 7.67/1.44  --bmc1_max_bound_default                -1
% 7.67/1.44  --bmc1_symbol_reachability              true
% 7.67/1.44  --bmc1_property_lemmas                  false
% 7.67/1.44  --bmc1_k_induction                      false
% 7.67/1.44  --bmc1_non_equiv_states                 false
% 7.67/1.44  --bmc1_deadlock                         false
% 7.67/1.44  --bmc1_ucm                              false
% 7.67/1.44  --bmc1_add_unsat_core                   none
% 7.67/1.44  --bmc1_unsat_core_children              false
% 7.67/1.44  --bmc1_unsat_core_extrapolate_axioms    false
% 7.67/1.44  --bmc1_out_stat                         full
% 7.67/1.44  --bmc1_ground_init                      false
% 7.67/1.44  --bmc1_pre_inst_next_state              false
% 7.67/1.44  --bmc1_pre_inst_state                   false
% 7.67/1.44  --bmc1_pre_inst_reach_state             false
% 7.67/1.44  --bmc1_out_unsat_core                   false
% 7.67/1.44  --bmc1_aig_witness_out                  false
% 7.67/1.44  --bmc1_verbose                          false
% 7.67/1.44  --bmc1_dump_clauses_tptp                false
% 7.67/1.44  --bmc1_dump_unsat_core_tptp             false
% 7.67/1.44  --bmc1_dump_file                        -
% 7.67/1.44  --bmc1_ucm_expand_uc_limit              128
% 7.67/1.44  --bmc1_ucm_n_expand_iterations          6
% 7.67/1.44  --bmc1_ucm_extend_mode                  1
% 7.67/1.44  --bmc1_ucm_init_mode                    2
% 7.67/1.44  --bmc1_ucm_cone_mode                    none
% 7.67/1.44  --bmc1_ucm_reduced_relation_type        0
% 7.67/1.44  --bmc1_ucm_relax_model                  4
% 7.67/1.44  --bmc1_ucm_full_tr_after_sat            true
% 7.67/1.44  --bmc1_ucm_expand_neg_assumptions       false
% 7.67/1.44  --bmc1_ucm_layered_model                none
% 7.67/1.44  --bmc1_ucm_max_lemma_size               10
% 7.67/1.44  
% 7.67/1.44  ------ AIG Options
% 7.67/1.44  
% 7.67/1.44  --aig_mode                              false
% 7.67/1.44  
% 7.67/1.44  ------ Instantiation Options
% 7.67/1.44  
% 7.67/1.44  --instantiation_flag                    true
% 7.67/1.44  --inst_sos_flag                         true
% 7.67/1.44  --inst_sos_phase                        true
% 7.67/1.44  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.67/1.44  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.67/1.44  --inst_lit_sel_side                     none
% 7.67/1.44  --inst_solver_per_active                1400
% 7.67/1.44  --inst_solver_calls_frac                1.
% 7.67/1.44  --inst_passive_queue_type               priority_queues
% 7.67/1.44  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.67/1.44  --inst_passive_queues_freq              [25;2]
% 7.67/1.44  --inst_dismatching                      true
% 7.67/1.44  --inst_eager_unprocessed_to_passive     true
% 7.67/1.44  --inst_prop_sim_given                   true
% 7.67/1.44  --inst_prop_sim_new                     false
% 7.67/1.44  --inst_subs_new                         false
% 7.67/1.44  --inst_eq_res_simp                      false
% 7.67/1.44  --inst_subs_given                       false
% 7.67/1.44  --inst_orphan_elimination               true
% 7.67/1.44  --inst_learning_loop_flag               true
% 7.67/1.44  --inst_learning_start                   3000
% 7.67/1.44  --inst_learning_factor                  2
% 7.67/1.44  --inst_start_prop_sim_after_learn       3
% 7.67/1.44  --inst_sel_renew                        solver
% 7.67/1.44  --inst_lit_activity_flag                true
% 7.67/1.44  --inst_restr_to_given                   false
% 7.67/1.44  --inst_activity_threshold               500
% 7.67/1.44  --inst_out_proof                        true
% 7.67/1.44  
% 7.67/1.44  ------ Resolution Options
% 7.67/1.44  
% 7.67/1.44  --resolution_flag                       false
% 7.67/1.44  --res_lit_sel                           adaptive
% 7.67/1.44  --res_lit_sel_side                      none
% 7.67/1.44  --res_ordering                          kbo
% 7.67/1.44  --res_to_prop_solver                    active
% 7.67/1.44  --res_prop_simpl_new                    false
% 7.67/1.44  --res_prop_simpl_given                  true
% 7.67/1.44  --res_passive_queue_type                priority_queues
% 7.67/1.44  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.67/1.44  --res_passive_queues_freq               [15;5]
% 7.67/1.44  --res_forward_subs                      full
% 7.67/1.44  --res_backward_subs                     full
% 7.67/1.44  --res_forward_subs_resolution           true
% 7.67/1.44  --res_backward_subs_resolution          true
% 7.67/1.44  --res_orphan_elimination                true
% 7.67/1.44  --res_time_limit                        2.
% 7.67/1.44  --res_out_proof                         true
% 7.67/1.44  
% 7.67/1.44  ------ Superposition Options
% 7.67/1.44  
% 7.67/1.44  --superposition_flag                    true
% 7.67/1.44  --sup_passive_queue_type                priority_queues
% 7.67/1.44  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.67/1.44  --sup_passive_queues_freq               [8;1;4]
% 7.67/1.44  --demod_completeness_check              fast
% 7.67/1.44  --demod_use_ground                      true
% 7.67/1.44  --sup_to_prop_solver                    passive
% 7.67/1.44  --sup_prop_simpl_new                    true
% 7.67/1.44  --sup_prop_simpl_given                  true
% 7.67/1.44  --sup_fun_splitting                     true
% 7.67/1.44  --sup_smt_interval                      50000
% 7.67/1.44  
% 7.67/1.44  ------ Superposition Simplification Setup
% 7.67/1.44  
% 7.67/1.44  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.67/1.44  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.67/1.44  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.67/1.44  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.67/1.44  --sup_full_triv                         [TrivRules;PropSubs]
% 7.67/1.44  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.67/1.44  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.67/1.44  --sup_immed_triv                        [TrivRules]
% 7.67/1.44  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.67/1.44  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.67/1.44  --sup_immed_bw_main                     []
% 7.67/1.44  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.67/1.44  --sup_input_triv                        [Unflattening;TrivRules]
% 7.67/1.44  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.67/1.44  --sup_input_bw                          []
% 7.67/1.44  
% 7.67/1.44  ------ Combination Options
% 7.67/1.44  
% 7.67/1.44  --comb_res_mult                         3
% 7.67/1.44  --comb_sup_mult                         2
% 7.67/1.44  --comb_inst_mult                        10
% 7.67/1.44  
% 7.67/1.44  ------ Debug Options
% 7.67/1.44  
% 7.67/1.44  --dbg_backtrace                         false
% 7.67/1.44  --dbg_dump_prop_clauses                 false
% 7.67/1.44  --dbg_dump_prop_clauses_file            -
% 7.67/1.44  --dbg_out_stat                          false
% 7.67/1.44  
% 7.67/1.44  
% 7.67/1.44  
% 7.67/1.44  
% 7.67/1.44  ------ Proving...
% 7.67/1.44  
% 7.67/1.44  
% 7.67/1.44  % SZS status Theorem for theBenchmark.p
% 7.67/1.44  
% 7.67/1.44   Resolution empty clause
% 7.67/1.44  
% 7.67/1.44  % SZS output start CNFRefutation for theBenchmark.p
% 7.67/1.44  
% 7.67/1.44  fof(f21,axiom,(
% 7.67/1.44    ! [X0] : (v5_relat_1(k6_relat_1(X0),X0) & v4_relat_1(k6_relat_1(X0),X0) & v1_relat_1(k6_relat_1(X0)))),
% 7.67/1.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.67/1.44  
% 7.67/1.44  fof(f24,plain,(
% 7.67/1.44    ! [X0] : (v4_relat_1(k6_relat_1(X0),X0) & v1_relat_1(k6_relat_1(X0)))),
% 7.67/1.44    inference(pure_predicate_removal,[],[f21])).
% 7.67/1.44  
% 7.67/1.44  fof(f68,plain,(
% 7.67/1.44    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 7.67/1.44    inference(cnf_transformation,[],[f24])).
% 7.67/1.44  
% 7.67/1.44  fof(f12,axiom,(
% 7.67/1.44    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)))),
% 7.67/1.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.67/1.44  
% 7.67/1.44  fof(f32,plain,(
% 7.67/1.44    ! [X0,X1] : (k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.67/1.44    inference(ennf_transformation,[],[f12])).
% 7.67/1.44  
% 7.67/1.44  fof(f56,plain,(
% 7.67/1.44    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 7.67/1.44    inference(cnf_transformation,[],[f32])).
% 7.67/1.44  
% 7.67/1.44  fof(f5,axiom,(
% 7.67/1.44    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 7.67/1.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.67/1.44  
% 7.67/1.44  fof(f49,plain,(
% 7.67/1.44    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 7.67/1.44    inference(cnf_transformation,[],[f5])).
% 7.67/1.44  
% 7.67/1.44  fof(f1,axiom,(
% 7.67/1.44    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 7.67/1.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.67/1.44  
% 7.67/1.44  fof(f45,plain,(
% 7.67/1.44    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 7.67/1.44    inference(cnf_transformation,[],[f1])).
% 7.67/1.44  
% 7.67/1.44  fof(f2,axiom,(
% 7.67/1.44    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 7.67/1.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.67/1.44  
% 7.67/1.44  fof(f46,plain,(
% 7.67/1.44    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 7.67/1.44    inference(cnf_transformation,[],[f2])).
% 7.67/1.44  
% 7.67/1.44  fof(f3,axiom,(
% 7.67/1.44    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 7.67/1.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.67/1.44  
% 7.67/1.44  fof(f47,plain,(
% 7.67/1.44    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 7.67/1.44    inference(cnf_transformation,[],[f3])).
% 7.67/1.44  
% 7.67/1.44  fof(f4,axiom,(
% 7.67/1.44    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 7.67/1.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.67/1.44  
% 7.67/1.44  fof(f48,plain,(
% 7.67/1.44    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 7.67/1.44    inference(cnf_transformation,[],[f4])).
% 7.67/1.44  
% 7.67/1.44  fof(f71,plain,(
% 7.67/1.44    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 7.67/1.44    inference(definition_unfolding,[],[f47,f48])).
% 7.67/1.44  
% 7.67/1.44  fof(f72,plain,(
% 7.67/1.44    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 7.67/1.44    inference(definition_unfolding,[],[f46,f71])).
% 7.67/1.44  
% 7.67/1.44  fof(f73,plain,(
% 7.67/1.44    ( ! [X0,X1] : (k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1)) )),
% 7.67/1.44    inference(definition_unfolding,[],[f45,f72])).
% 7.67/1.44  
% 7.67/1.44  fof(f74,plain,(
% 7.67/1.44    ( ! [X0,X1] : (k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)) = k3_xboole_0(X0,X1)) )),
% 7.67/1.44    inference(definition_unfolding,[],[f49,f73])).
% 7.67/1.44  
% 7.67/1.44  fof(f77,plain,(
% 7.67/1.44    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k7_relat_1(X1,k1_setfam_1(k4_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X0))) | ~v1_relat_1(X1)) )),
% 7.67/1.44    inference(definition_unfolding,[],[f56,f74])).
% 7.67/1.44  
% 7.67/1.44  fof(f9,axiom,(
% 7.67/1.44    ! [X0,X1] : (v1_relat_1(X1) => k3_xboole_0(k2_relat_1(X1),X0) = k2_relat_1(k8_relat_1(X0,X1)))),
% 7.67/1.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.67/1.44  
% 7.67/1.44  fof(f29,plain,(
% 7.67/1.44    ! [X0,X1] : (k3_xboole_0(k2_relat_1(X1),X0) = k2_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1))),
% 7.67/1.44    inference(ennf_transformation,[],[f9])).
% 7.67/1.44  
% 7.67/1.44  fof(f53,plain,(
% 7.67/1.44    ( ! [X0,X1] : (k3_xboole_0(k2_relat_1(X1),X0) = k2_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1)) )),
% 7.67/1.44    inference(cnf_transformation,[],[f29])).
% 7.67/1.44  
% 7.67/1.44  fof(f76,plain,(
% 7.67/1.44    ( ! [X0,X1] : (k1_setfam_1(k4_enumset1(k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),X0)) = k2_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1)) )),
% 7.67/1.44    inference(definition_unfolding,[],[f53,f74])).
% 7.67/1.44  
% 7.67/1.44  fof(f16,axiom,(
% 7.67/1.44    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 7.67/1.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.67/1.44  
% 7.67/1.44  fof(f62,plain,(
% 7.67/1.44    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 7.67/1.44    inference(cnf_transformation,[],[f16])).
% 7.67/1.44  
% 7.67/1.44  fof(f10,axiom,(
% 7.67/1.44    ! [X0,X1] : (v1_relat_1(X1) => k5_relat_1(X1,k6_relat_1(X0)) = k8_relat_1(X0,X1))),
% 7.67/1.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.67/1.44  
% 7.67/1.44  fof(f30,plain,(
% 7.67/1.44    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = k8_relat_1(X0,X1) | ~v1_relat_1(X1))),
% 7.67/1.44    inference(ennf_transformation,[],[f10])).
% 7.67/1.44  
% 7.67/1.44  fof(f54,plain,(
% 7.67/1.44    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = k8_relat_1(X0,X1) | ~v1_relat_1(X1)) )),
% 7.67/1.44    inference(cnf_transformation,[],[f30])).
% 7.67/1.44  
% 7.67/1.44  fof(f20,axiom,(
% 7.67/1.44    ! [X0,X1] : (v1_relat_1(X1) => k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0))),
% 7.67/1.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.67/1.44  
% 7.67/1.44  fof(f41,plain,(
% 7.67/1.44    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.67/1.44    inference(ennf_transformation,[],[f20])).
% 7.67/1.44  
% 7.67/1.44  fof(f67,plain,(
% 7.67/1.44    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.67/1.44    inference(cnf_transformation,[],[f41])).
% 7.67/1.44  
% 7.67/1.44  fof(f61,plain,(
% 7.67/1.44    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 7.67/1.44    inference(cnf_transformation,[],[f16])).
% 7.67/1.44  
% 7.67/1.44  fof(f15,axiom,(
% 7.67/1.44    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,X1))))),
% 7.67/1.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.67/1.44  
% 7.67/1.44  fof(f37,plain,(
% 7.67/1.44    ! [X0] : (! [X1] : (k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 7.67/1.44    inference(ennf_transformation,[],[f15])).
% 7.67/1.44  
% 7.67/1.44  fof(f60,plain,(
% 7.67/1.44    ( ! [X0,X1] : (k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 7.67/1.44    inference(cnf_transformation,[],[f37])).
% 7.67/1.44  
% 7.67/1.44  fof(f17,axiom,(
% 7.67/1.44    ! [X0] : k4_relat_1(k6_relat_1(X0)) = k6_relat_1(X0)),
% 7.67/1.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.67/1.44  
% 7.67/1.44  fof(f63,plain,(
% 7.67/1.44    ( ! [X0] : (k4_relat_1(k6_relat_1(X0)) = k6_relat_1(X0)) )),
% 7.67/1.44    inference(cnf_transformation,[],[f17])).
% 7.67/1.44  
% 7.67/1.44  fof(f8,axiom,(
% 7.67/1.44    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1))),
% 7.67/1.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.67/1.44  
% 7.67/1.44  fof(f28,plain,(
% 7.67/1.44    ! [X0,X1,X2] : (k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2))),
% 7.67/1.44    inference(ennf_transformation,[],[f8])).
% 7.67/1.44  
% 7.67/1.44  fof(f52,plain,(
% 7.67/1.44    ( ! [X2,X0,X1] : (k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 7.67/1.44    inference(cnf_transformation,[],[f28])).
% 7.67/1.44  
% 7.67/1.44  fof(f75,plain,(
% 7.67/1.44    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))) | ~v1_relat_1(X2)) )),
% 7.67/1.44    inference(definition_unfolding,[],[f52,f74])).
% 7.67/1.44  
% 7.67/1.44  fof(f13,axiom,(
% 7.67/1.44    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 7.67/1.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.67/1.44  
% 7.67/1.44  fof(f33,plain,(
% 7.67/1.44    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 7.67/1.44    inference(ennf_transformation,[],[f13])).
% 7.67/1.44  
% 7.67/1.44  fof(f34,plain,(
% 7.67/1.44    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.67/1.44    inference(flattening,[],[f33])).
% 7.67/1.44  
% 7.67/1.44  fof(f57,plain,(
% 7.67/1.44    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.67/1.44    inference(cnf_transformation,[],[f34])).
% 7.67/1.44  
% 7.67/1.44  fof(f69,plain,(
% 7.67/1.44    ( ! [X0] : (v4_relat_1(k6_relat_1(X0),X0)) )),
% 7.67/1.44    inference(cnf_transformation,[],[f24])).
% 7.67/1.44  
% 7.67/1.44  fof(f6,axiom,(
% 7.67/1.44    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 7.67/1.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.67/1.44  
% 7.67/1.44  fof(f25,plain,(
% 7.67/1.44    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 7.67/1.44    inference(ennf_transformation,[],[f6])).
% 7.67/1.44  
% 7.67/1.44  fof(f26,plain,(
% 7.67/1.44    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 7.67/1.44    inference(flattening,[],[f25])).
% 7.67/1.44  
% 7.67/1.44  fof(f50,plain,(
% 7.67/1.44    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 7.67/1.44    inference(cnf_transformation,[],[f26])).
% 7.67/1.44  
% 7.67/1.44  fof(f11,axiom,(
% 7.67/1.44    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)))),
% 7.67/1.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.67/1.44  
% 7.67/1.44  fof(f31,plain,(
% 7.67/1.44    ! [X0,X1,X2] : (k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 7.67/1.44    inference(ennf_transformation,[],[f11])).
% 7.67/1.44  
% 7.67/1.44  fof(f55,plain,(
% 7.67/1.44    ( ! [X2,X0,X1] : (k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 7.67/1.44    inference(cnf_transformation,[],[f31])).
% 7.67/1.44  
% 7.67/1.44  fof(f18,axiom,(
% 7.67/1.44    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)))),
% 7.67/1.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.67/1.44  
% 7.67/1.44  fof(f38,plain,(
% 7.67/1.44    ! [X0,X1] : ((r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)) | ~v1_relat_1(X1))),
% 7.67/1.44    inference(ennf_transformation,[],[f18])).
% 7.67/1.44  
% 7.67/1.44  fof(f64,plain,(
% 7.67/1.44    ( ! [X0,X1] : (r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) | ~v1_relat_1(X1)) )),
% 7.67/1.44    inference(cnf_transformation,[],[f38])).
% 7.67/1.44  
% 7.67/1.44  fof(f14,axiom,(
% 7.67/1.44    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 7.67/1.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.67/1.44  
% 7.67/1.44  fof(f35,plain,(
% 7.67/1.44    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 7.67/1.44    inference(ennf_transformation,[],[f14])).
% 7.67/1.44  
% 7.67/1.44  fof(f36,plain,(
% 7.67/1.44    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 7.67/1.44    inference(flattening,[],[f35])).
% 7.67/1.44  
% 7.67/1.44  fof(f59,plain,(
% 7.67/1.44    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 7.67/1.44    inference(cnf_transformation,[],[f36])).
% 7.67/1.44  
% 7.67/1.44  fof(f19,axiom,(
% 7.67/1.44    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 7.67/1.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.67/1.44  
% 7.67/1.44  fof(f39,plain,(
% 7.67/1.44    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.67/1.44    inference(ennf_transformation,[],[f19])).
% 7.67/1.44  
% 7.67/1.44  fof(f40,plain,(
% 7.67/1.44    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 7.67/1.44    inference(flattening,[],[f39])).
% 7.67/1.44  
% 7.67/1.44  fof(f66,plain,(
% 7.67/1.44    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 7.67/1.44    inference(cnf_transformation,[],[f40])).
% 7.67/1.44  
% 7.67/1.44  fof(f22,conjecture,(
% 7.67/1.44    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 7.67/1.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.67/1.44  
% 7.67/1.44  fof(f23,negated_conjecture,(
% 7.67/1.44    ~! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 7.67/1.44    inference(negated_conjecture,[],[f22])).
% 7.67/1.44  
% 7.67/1.44  fof(f42,plain,(
% 7.67/1.44    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))),
% 7.67/1.44    inference(ennf_transformation,[],[f23])).
% 7.67/1.44  
% 7.67/1.44  fof(f43,plain,(
% 7.67/1.44    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 7.67/1.44    introduced(choice_axiom,[])).
% 7.67/1.44  
% 7.67/1.44  fof(f44,plain,(
% 7.67/1.44    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 7.67/1.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f42,f43])).
% 7.67/1.44  
% 7.67/1.44  fof(f70,plain,(
% 7.67/1.44    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 7.67/1.44    inference(cnf_transformation,[],[f44])).
% 7.67/1.44  
% 7.67/1.44  fof(f78,plain,(
% 7.67/1.44    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1)))),
% 7.67/1.44    inference(definition_unfolding,[],[f70,f74])).
% 7.67/1.44  
% 7.67/1.44  cnf(c_19,plain,
% 7.67/1.44      ( v1_relat_1(k6_relat_1(X0)) ),
% 7.67/1.44      inference(cnf_transformation,[],[f68]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_607,plain,
% 7.67/1.44      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 7.67/1.44      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_6,plain,
% 7.67/1.44      ( ~ v1_relat_1(X0)
% 7.67/1.44      | k7_relat_1(X0,k1_setfam_1(k4_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),X1))) = k7_relat_1(X0,X1) ),
% 7.67/1.44      inference(cnf_transformation,[],[f77]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_615,plain,
% 7.67/1.44      ( k7_relat_1(X0,k1_setfam_1(k4_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),X1))) = k7_relat_1(X0,X1)
% 7.67/1.44      | v1_relat_1(X0) != iProver_top ),
% 7.67/1.44      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_3,plain,
% 7.67/1.44      ( ~ v1_relat_1(X0)
% 7.67/1.44      | k1_setfam_1(k4_enumset1(k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X0),X1)) = k2_relat_1(k8_relat_1(X1,X0)) ),
% 7.67/1.44      inference(cnf_transformation,[],[f76]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_618,plain,
% 7.67/1.44      ( k1_setfam_1(k4_enumset1(k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X0),X1)) = k2_relat_1(k8_relat_1(X1,X0))
% 7.67/1.44      | v1_relat_1(X0) != iProver_top ),
% 7.67/1.44      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_1311,plain,
% 7.67/1.44      ( k1_setfam_1(k4_enumset1(k2_relat_1(k6_relat_1(X0)),k2_relat_1(k6_relat_1(X0)),k2_relat_1(k6_relat_1(X0)),k2_relat_1(k6_relat_1(X0)),k2_relat_1(k6_relat_1(X0)),X1)) = k2_relat_1(k8_relat_1(X1,k6_relat_1(X0))) ),
% 7.67/1.44      inference(superposition,[status(thm)],[c_607,c_618]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_11,plain,
% 7.67/1.44      ( k2_relat_1(k6_relat_1(X0)) = X0 ),
% 7.67/1.44      inference(cnf_transformation,[],[f62]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_1312,plain,
% 7.67/1.44      ( k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)) = k2_relat_1(k8_relat_1(X1,k6_relat_1(X0))) ),
% 7.67/1.44      inference(light_normalisation,[status(thm)],[c_1311,c_11]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_4,plain,
% 7.67/1.44      ( ~ v1_relat_1(X0) | k5_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X1,X0) ),
% 7.67/1.44      inference(cnf_transformation,[],[f54]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_617,plain,
% 7.67/1.44      ( k5_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X1,X0)
% 7.67/1.44      | v1_relat_1(X0) != iProver_top ),
% 7.67/1.44      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_930,plain,
% 7.67/1.44      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k8_relat_1(X1,k6_relat_1(X0)) ),
% 7.67/1.44      inference(superposition,[status(thm)],[c_607,c_617]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_17,plain,
% 7.67/1.44      ( ~ v1_relat_1(X0) | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
% 7.67/1.44      inference(cnf_transformation,[],[f67]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_608,plain,
% 7.67/1.44      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
% 7.67/1.44      | v1_relat_1(X1) != iProver_top ),
% 7.67/1.44      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_818,plain,
% 7.67/1.44      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
% 7.67/1.44      inference(superposition,[status(thm)],[c_607,c_608]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_931,plain,
% 7.67/1.44      ( k8_relat_1(X0,k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X0),X1) ),
% 7.67/1.44      inference(light_normalisation,[status(thm)],[c_930,c_818]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_1313,plain,
% 7.67/1.44      ( k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)) = k2_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
% 7.67/1.44      inference(demodulation,[status(thm)],[c_1312,c_931]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_1667,plain,
% 7.67/1.44      ( k7_relat_1(X0,k2_relat_1(k7_relat_1(k6_relat_1(X1),k1_relat_1(X0)))) = k7_relat_1(X0,X1)
% 7.67/1.44      | v1_relat_1(X0) != iProver_top ),
% 7.67/1.44      inference(demodulation,[status(thm)],[c_615,c_1313]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_1672,plain,
% 7.67/1.44      ( k7_relat_1(k6_relat_1(X0),k2_relat_1(k7_relat_1(k6_relat_1(X1),k1_relat_1(k6_relat_1(X0))))) = k7_relat_1(k6_relat_1(X0),X1) ),
% 7.67/1.44      inference(superposition,[status(thm)],[c_607,c_1667]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_12,plain,
% 7.67/1.44      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 7.67/1.44      inference(cnf_transformation,[],[f61]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_1673,plain,
% 7.67/1.44      ( k7_relat_1(k6_relat_1(X0),k2_relat_1(k7_relat_1(k6_relat_1(X1),X0))) = k7_relat_1(k6_relat_1(X0),X1) ),
% 7.67/1.44      inference(light_normalisation,[status(thm)],[c_1672,c_12]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_10,plain,
% 7.67/1.44      ( ~ v1_relat_1(X0)
% 7.67/1.44      | ~ v1_relat_1(X1)
% 7.67/1.44      | k5_relat_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k5_relat_1(X1,X0)) ),
% 7.67/1.44      inference(cnf_transformation,[],[f60]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_612,plain,
% 7.67/1.44      ( k5_relat_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k5_relat_1(X1,X0))
% 7.67/1.44      | v1_relat_1(X0) != iProver_top
% 7.67/1.44      | v1_relat_1(X1) != iProver_top ),
% 7.67/1.44      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_1201,plain,
% 7.67/1.44      ( k5_relat_1(k4_relat_1(k6_relat_1(X0)),k4_relat_1(X1)) = k4_relat_1(k5_relat_1(X1,k6_relat_1(X0)))
% 7.67/1.44      | v1_relat_1(X1) != iProver_top ),
% 7.67/1.44      inference(superposition,[status(thm)],[c_607,c_612]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_13,plain,
% 7.67/1.44      ( k4_relat_1(k6_relat_1(X0)) = k6_relat_1(X0) ),
% 7.67/1.44      inference(cnf_transformation,[],[f63]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_1202,plain,
% 7.67/1.44      ( k4_relat_1(k5_relat_1(X0,k6_relat_1(X1))) = k5_relat_1(k6_relat_1(X1),k4_relat_1(X0))
% 7.67/1.44      | v1_relat_1(X0) != iProver_top ),
% 7.67/1.44      inference(light_normalisation,[status(thm)],[c_1201,c_13]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_1236,plain,
% 7.67/1.44      ( k4_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k5_relat_1(k6_relat_1(X1),k4_relat_1(k6_relat_1(X0))) ),
% 7.67/1.44      inference(superposition,[status(thm)],[c_607,c_1202]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_1237,plain,
% 7.67/1.44      ( k4_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) ),
% 7.67/1.44      inference(light_normalisation,[status(thm)],[c_1236,c_13,c_818]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_1238,plain,
% 7.67/1.44      ( k4_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
% 7.67/1.44      inference(demodulation,[status(thm)],[c_1237,c_818]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_1686,plain,
% 7.67/1.44      ( k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X1) = k4_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
% 7.67/1.44      inference(superposition,[status(thm)],[c_1673,c_1238]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_2,plain,
% 7.67/1.44      ( ~ v1_relat_1(X0)
% 7.67/1.44      | k7_relat_1(X0,k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X2))) = k7_relat_1(k7_relat_1(X0,X1),X2) ),
% 7.67/1.44      inference(cnf_transformation,[],[f75]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_619,plain,
% 7.67/1.44      ( k7_relat_1(X0,k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X2))) = k7_relat_1(k7_relat_1(X0,X1),X2)
% 7.67/1.44      | v1_relat_1(X0) != iProver_top ),
% 7.67/1.44      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_1304,plain,
% 7.67/1.44      ( k7_relat_1(k6_relat_1(X0),k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X2))) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) ),
% 7.67/1.44      inference(superposition,[status(thm)],[c_607,c_619]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_1505,plain,
% 7.67/1.44      ( k7_relat_1(k6_relat_1(X0),k2_relat_1(k7_relat_1(k6_relat_1(X1),X2))) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X2),X1) ),
% 7.67/1.44      inference(demodulation,[status(thm)],[c_1304,c_1313]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_1511,plain,
% 7.67/1.44      ( k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X2) = k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X2),X1),X0)) ),
% 7.67/1.44      inference(superposition,[status(thm)],[c_1505,c_1238]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_1698,plain,
% 7.67/1.44      ( k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X1) = k7_relat_1(k6_relat_1(X0),X1) ),
% 7.67/1.44      inference(demodulation,[status(thm)],[c_1686,c_1238,c_1511]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_7,plain,
% 7.67/1.44      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 7.67/1.44      inference(cnf_transformation,[],[f57]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_18,plain,
% 7.67/1.44      ( v4_relat_1(k6_relat_1(X0),X0) ),
% 7.67/1.44      inference(cnf_transformation,[],[f69]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_218,plain,
% 7.67/1.44      ( ~ v1_relat_1(X0)
% 7.67/1.44      | X1 != X2
% 7.67/1.44      | k7_relat_1(X0,X2) = X0
% 7.67/1.44      | k6_relat_1(X1) != X0 ),
% 7.67/1.44      inference(resolution_lifted,[status(thm)],[c_7,c_18]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_219,plain,
% 7.67/1.44      ( ~ v1_relat_1(k6_relat_1(X0))
% 7.67/1.44      | k7_relat_1(k6_relat_1(X0),X0) = k6_relat_1(X0) ),
% 7.67/1.44      inference(unflattening,[status(thm)],[c_218]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_223,plain,
% 7.67/1.44      ( k7_relat_1(k6_relat_1(X0),X0) = k6_relat_1(X0) ),
% 7.67/1.44      inference(global_propositional_subsumption,[status(thm)],[c_219,c_19]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_1510,plain,
% 7.67/1.44      ( k7_relat_1(k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X1),X0) = k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
% 7.67/1.44      inference(superposition,[status(thm)],[c_1505,c_223]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_1519,plain,
% 7.67/1.44      ( k7_relat_1(k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X0),X1)),X1) = k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X1),X0))) ),
% 7.67/1.44      inference(demodulation,[status(thm)],[c_1510,c_1511]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_1520,plain,
% 7.67/1.44      ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0) = k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
% 7.67/1.44      inference(light_normalisation,[status(thm)],[c_1519,c_223,c_1238]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_2007,plain,
% 7.67/1.44      ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X1))) ),
% 7.67/1.44      inference(superposition,[status(thm)],[c_1698,c_1520]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_2021,plain,
% 7.67/1.44      ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
% 7.67/1.44      inference(demodulation,[status(thm)],[c_2007,c_1698]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_0,plain,
% 7.67/1.44      ( ~ v1_relat_1(X0) | ~ v1_relat_1(X1) | v1_relat_1(k5_relat_1(X1,X0)) ),
% 7.67/1.44      inference(cnf_transformation,[],[f50]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_621,plain,
% 7.67/1.44      ( v1_relat_1(X0) != iProver_top
% 7.67/1.44      | v1_relat_1(X1) != iProver_top
% 7.67/1.44      | v1_relat_1(k5_relat_1(X1,X0)) = iProver_top ),
% 7.67/1.44      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_1241,plain,
% 7.67/1.44      ( v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = iProver_top
% 7.67/1.44      | v1_relat_1(k6_relat_1(X0)) != iProver_top
% 7.67/1.44      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 7.67/1.44      inference(superposition,[status(thm)],[c_818,c_621]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_21,plain,
% 7.67/1.44      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 7.67/1.44      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_2837,plain,
% 7.67/1.44      ( v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = iProver_top
% 7.67/1.44      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 7.67/1.44      inference(global_propositional_subsumption,[status(thm)],[c_1241,c_21]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_2844,plain,
% 7.67/1.44      ( v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = iProver_top
% 7.67/1.44      | v1_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X1),X0)))) != iProver_top ),
% 7.67/1.44      inference(superposition,[status(thm)],[c_1673,c_2837]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_3141,plain,
% 7.67/1.44      ( v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = iProver_top ),
% 7.67/1.44      inference(superposition,[status(thm)],[c_607,c_2844]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_3158,plain,
% 7.67/1.44      ( v1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)) = iProver_top ),
% 7.67/1.44      inference(superposition,[status(thm)],[c_1505,c_3141]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_3163,plain,
% 7.67/1.44      ( k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X1),X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X0) ),
% 7.67/1.44      inference(superposition,[status(thm)],[c_3141,c_608]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_3166,plain,
% 7.67/1.44      ( k4_relat_1(k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X2))) = k5_relat_1(k6_relat_1(X2),k4_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
% 7.67/1.44      inference(superposition,[status(thm)],[c_3141,c_1202]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_3168,plain,
% 7.67/1.44      ( k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X2)) = k8_relat_1(X2,k7_relat_1(k6_relat_1(X0),X1)) ),
% 7.67/1.44      inference(superposition,[status(thm)],[c_3141,c_617]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_5,plain,
% 7.67/1.44      ( ~ v1_relat_1(X0)
% 7.67/1.44      | k8_relat_1(X1,k7_relat_1(X0,X2)) = k7_relat_1(k8_relat_1(X1,X0),X2) ),
% 7.67/1.44      inference(cnf_transformation,[],[f55]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_616,plain,
% 7.67/1.44      ( k8_relat_1(X0,k7_relat_1(X1,X2)) = k7_relat_1(k8_relat_1(X0,X1),X2)
% 7.67/1.44      | v1_relat_1(X1) != iProver_top ),
% 7.67/1.44      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_985,plain,
% 7.67/1.44      ( k8_relat_1(X0,k7_relat_1(k6_relat_1(X1),X2)) = k7_relat_1(k8_relat_1(X0,k6_relat_1(X1)),X2) ),
% 7.67/1.44      inference(superposition,[status(thm)],[c_607,c_616]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_986,plain,
% 7.67/1.44      ( k8_relat_1(X0,k7_relat_1(k6_relat_1(X1),X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) ),
% 7.67/1.44      inference(light_normalisation,[status(thm)],[c_985,c_931]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_3171,plain,
% 7.67/1.44      ( k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X0),X1) ),
% 7.67/1.44      inference(demodulation,[status(thm)],[c_3168,c_986]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_3173,plain,
% 7.67/1.44      ( k5_relat_1(k6_relat_1(X0),k4_relat_1(k7_relat_1(k6_relat_1(X1),X2))) = k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)) ),
% 7.67/1.44      inference(demodulation,[status(thm)],[c_3166,c_3171]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_3174,plain,
% 7.67/1.44      ( k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)) = k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X2),X1)) ),
% 7.67/1.44      inference(demodulation,[status(thm)],[c_3173,c_1238]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_3175,plain,
% 7.67/1.44      ( k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X1),X0) ),
% 7.67/1.44      inference(demodulation,[status(thm)],[c_3163,c_3174]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_4794,plain,
% 7.67/1.44      ( k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X2) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) ),
% 7.67/1.44      inference(demodulation,[status(thm)],[c_1511,c_3175]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_15,plain,
% 7.67/1.44      ( r1_tarski(k5_relat_1(X0,k6_relat_1(X1)),X0) | ~ v1_relat_1(X0) ),
% 7.67/1.44      inference(cnf_transformation,[],[f64]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_610,plain,
% 7.67/1.44      ( r1_tarski(k5_relat_1(X0,k6_relat_1(X1)),X0) = iProver_top
% 7.67/1.44      | v1_relat_1(X0) != iProver_top ),
% 7.67/1.44      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_1030,plain,
% 7.67/1.44      ( r1_tarski(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X1)) = iProver_top
% 7.67/1.44      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 7.67/1.44      inference(superposition,[status(thm)],[c_818,c_610]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_4843,plain,
% 7.67/1.44      ( r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2),k6_relat_1(X2)) = iProver_top
% 7.67/1.44      | v1_relat_1(k6_relat_1(X2)) != iProver_top ),
% 7.67/1.44      inference(superposition,[status(thm)],[c_4794,c_1030]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_8,plain,
% 7.67/1.44      ( ~ r1_tarski(X0,X1)
% 7.67/1.44      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
% 7.67/1.44      | ~ v1_relat_1(X1)
% 7.67/1.44      | ~ v1_relat_1(X0) ),
% 7.67/1.44      inference(cnf_transformation,[],[f59]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_614,plain,
% 7.67/1.44      ( r1_tarski(X0,X1) != iProver_top
% 7.67/1.44      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) = iProver_top
% 7.67/1.44      | v1_relat_1(X0) != iProver_top
% 7.67/1.44      | v1_relat_1(X1) != iProver_top ),
% 7.67/1.44      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_16,plain,
% 7.67/1.44      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 7.67/1.44      | ~ v1_relat_1(X0)
% 7.67/1.44      | k5_relat_1(X0,k6_relat_1(X1)) = X0 ),
% 7.67/1.44      inference(cnf_transformation,[],[f66]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_609,plain,
% 7.67/1.44      ( k5_relat_1(X0,k6_relat_1(X1)) = X0
% 7.67/1.44      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 7.67/1.44      | v1_relat_1(X0) != iProver_top ),
% 7.67/1.44      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_1795,plain,
% 7.67/1.44      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X1))) = X0
% 7.67/1.44      | r1_tarski(X0,X1) != iProver_top
% 7.67/1.44      | v1_relat_1(X0) != iProver_top
% 7.67/1.44      | v1_relat_1(X1) != iProver_top ),
% 7.67/1.44      inference(superposition,[status(thm)],[c_614,c_609]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_17896,plain,
% 7.67/1.44      ( k5_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2),k6_relat_1(k2_relat_1(k6_relat_1(X2)))) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)
% 7.67/1.44      | v1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)) != iProver_top
% 7.67/1.44      | v1_relat_1(k6_relat_1(X2)) != iProver_top ),
% 7.67/1.44      inference(superposition,[status(thm)],[c_4843,c_1795]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_4821,plain,
% 7.67/1.44      ( k7_relat_1(k7_relat_1(k6_relat_1(X0),k2_relat_1(k7_relat_1(k6_relat_1(X1),X2))),X3) = k5_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X3),k6_relat_1(X0)) ),
% 7.67/1.44      inference(superposition,[status(thm)],[c_4794,c_3171]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_4872,plain,
% 7.67/1.44      ( k5_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2),k6_relat_1(X3)) = k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X3),X1),X0),X2) ),
% 7.67/1.44      inference(light_normalisation,[status(thm)],[c_4821,c_1505]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_1079,plain,
% 7.67/1.44      ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X1) = k8_relat_1(X0,k6_relat_1(X1)) ),
% 7.67/1.44      inference(superposition,[status(thm)],[c_223,c_986]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_1080,plain,
% 7.67/1.44      ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X1) = k7_relat_1(k6_relat_1(X0),X1) ),
% 7.67/1.44      inference(light_normalisation,[status(thm)],[c_1079,c_931]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_4844,plain,
% 7.67/1.44      ( k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2),X2) = k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X2) ),
% 7.67/1.44      inference(superposition,[status(thm)],[c_4794,c_1080]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_4865,plain,
% 7.67/1.44      ( k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2),X2) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) ),
% 7.67/1.44      inference(demodulation,[status(thm)],[c_4844,c_4794]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_5023,plain,
% 7.67/1.44      ( k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X0) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0) ),
% 7.67/1.44      inference(superposition,[status(thm)],[c_1520,c_4865]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_5049,plain,
% 7.67/1.44      ( k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X0) = k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
% 7.67/1.44      inference(light_normalisation,[status(thm)],[c_5023,c_1520]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_5104,plain,
% 7.67/1.44      ( k7_relat_1(k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X2))),X1),X0) = k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X2))) ),
% 7.67/1.44      inference(superposition,[status(thm)],[c_5049,c_1505]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_5112,plain,
% 7.67/1.44      ( k7_relat_1(k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2))),X1),X0) = k6_relat_1(k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2))) ),
% 7.67/1.44      inference(light_normalisation,[status(thm)],[c_5104,c_4794]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_4808,plain,
% 7.67/1.44      ( k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2))),X3) = k7_relat_1(k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X2),X3) ),
% 7.67/1.44      inference(superposition,[status(thm)],[c_4794,c_4794]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_4876,plain,
% 7.67/1.44      ( k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2))),X3) = k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2),X3) ),
% 7.67/1.44      inference(demodulation,[status(thm)],[c_4808,c_4794]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_5113,plain,
% 7.67/1.44      ( k7_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2),X1),X0) = k6_relat_1(k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2))) ),
% 7.67/1.44      inference(demodulation,[status(thm)],[c_5112,c_4876]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_1690,plain,
% 7.67/1.44      ( k7_relat_1(k7_relat_1(k6_relat_1(X0),k2_relat_1(k7_relat_1(k6_relat_1(X1),X2))),X2) = k7_relat_1(k6_relat_1(X0),k2_relat_1(k7_relat_1(k6_relat_1(X2),X1))) ),
% 7.67/1.44      inference(superposition,[status(thm)],[c_1673,c_1505]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_1695,plain,
% 7.67/1.44      ( k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2),X1) = k7_relat_1(k6_relat_1(X0),k2_relat_1(k7_relat_1(k6_relat_1(X1),X2))) ),
% 7.67/1.44      inference(light_normalisation,[status(thm)],[c_1690,c_1505]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_1696,plain,
% 7.67/1.44      ( k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2),X1) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X2),X1) ),
% 7.67/1.44      inference(demodulation,[status(thm)],[c_1695,c_1505]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_5114,plain,
% 7.67/1.44      ( k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2),X0) = k6_relat_1(k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X2),X1))) ),
% 7.67/1.44      inference(light_normalisation,[status(thm)],[c_5113,c_1696]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_17900,plain,
% 7.67/1.44      ( k6_relat_1(k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2))) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X0)
% 7.67/1.44      | v1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X0)) != iProver_top
% 7.67/1.44      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 7.67/1.44      inference(demodulation,[status(thm)],[c_17896,c_11,c_4872,c_5114]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_18382,plain,
% 7.67/1.44      ( v1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X0)) != iProver_top
% 7.67/1.44      | k6_relat_1(k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2))) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X0) ),
% 7.67/1.44      inference(global_propositional_subsumption,[status(thm)],[c_17900,c_21]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_18383,plain,
% 7.67/1.44      ( k6_relat_1(k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2))) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X0)
% 7.67/1.44      | v1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X0)) != iProver_top ),
% 7.67/1.44      inference(renaming,[status(thm)],[c_18382]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_18388,plain,
% 7.67/1.44      ( k6_relat_1(k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2))) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X0) ),
% 7.67/1.44      inference(superposition,[status(thm)],[c_3158,c_18383]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_19063,plain,
% 7.67/1.44      ( k7_relat_1(k7_relat_1(k6_relat_1(X0),k2_relat_1(k7_relat_1(k6_relat_1(X1),X0))),X1) = k6_relat_1(k2_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X1),X0))))) ),
% 7.67/1.44      inference(superposition,[status(thm)],[c_2021,c_18388]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_19440,plain,
% 7.67/1.44      ( k6_relat_1(k2_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))))) = k7_relat_1(k6_relat_1(X1),X0) ),
% 7.67/1.44      inference(light_normalisation,[status(thm)],[c_19063,c_1080,c_1673]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_19441,plain,
% 7.67/1.44      ( k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k7_relat_1(k6_relat_1(X1),X0) ),
% 7.67/1.44      inference(demodulation,[status(thm)],[c_19440,c_11]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_20,negated_conjecture,
% 7.67/1.44      ( k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))) ),
% 7.67/1.44      inference(cnf_transformation,[],[f78]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_1029,plain,
% 7.67/1.44      ( k6_relat_1(k1_setfam_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))) != k7_relat_1(k6_relat_1(sK0),sK1) ),
% 7.67/1.44      inference(demodulation,[status(thm)],[c_818,c_20]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_1401,plain,
% 7.67/1.44      ( k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(sK1),sK0))) != k7_relat_1(k6_relat_1(sK0),sK1) ),
% 7.67/1.44      inference(demodulation,[status(thm)],[c_1313,c_1029]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_19761,plain,
% 7.67/1.44      ( k7_relat_1(k6_relat_1(sK0),sK1) != k7_relat_1(k6_relat_1(sK0),sK1) ),
% 7.67/1.44      inference(demodulation,[status(thm)],[c_19441,c_1401]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_19795,plain,
% 7.67/1.44      ( $false ),
% 7.67/1.44      inference(equality_resolution_simp,[status(thm)],[c_19761]) ).
% 7.67/1.44  
% 7.67/1.44  
% 7.67/1.44  % SZS output end CNFRefutation for theBenchmark.p
% 7.67/1.44  
% 7.67/1.44  ------                               Statistics
% 7.67/1.44  
% 7.67/1.44  ------ General
% 7.67/1.44  
% 7.67/1.44  abstr_ref_over_cycles:                  0
% 7.67/1.44  abstr_ref_under_cycles:                 0
% 7.67/1.44  gc_basic_clause_elim:                   0
% 7.67/1.44  forced_gc_time:                         0
% 7.67/1.44  parsing_time:                           0.01
% 7.67/1.44  unif_index_cands_time:                  0.
% 7.67/1.44  unif_index_add_time:                    0.
% 7.67/1.44  orderings_time:                         0.
% 7.67/1.44  out_proof_time:                         0.012
% 7.67/1.44  total_time:                             0.691
% 7.67/1.44  num_of_symbols:                         45
% 7.67/1.44  num_of_terms:                           31154
% 7.67/1.44  
% 7.67/1.44  ------ Preprocessing
% 7.67/1.44  
% 7.67/1.44  num_of_splits:                          0
% 7.67/1.44  num_of_split_atoms:                     0
% 7.67/1.44  num_of_reused_defs:                     0
% 7.67/1.44  num_eq_ax_congr_red:                    4
% 7.67/1.44  num_of_sem_filtered_clauses:            1
% 7.67/1.44  num_of_subtypes:                        0
% 7.67/1.45  monotx_restored_types:                  0
% 7.67/1.45  sat_num_of_epr_types:                   0
% 7.67/1.45  sat_num_of_non_cyclic_types:            0
% 7.67/1.45  sat_guarded_non_collapsed_types:        0
% 7.67/1.45  num_pure_diseq_elim:                    0
% 7.67/1.45  simp_replaced_by:                       0
% 7.67/1.45  res_preprocessed:                       108
% 7.67/1.45  prep_upred:                             0
% 7.67/1.45  prep_unflattend:                        2
% 7.67/1.45  smt_new_axioms:                         0
% 7.67/1.45  pred_elim_cands:                        2
% 7.67/1.45  pred_elim:                              1
% 7.67/1.45  pred_elim_cl:                           1
% 7.67/1.45  pred_elim_cycles:                       3
% 7.67/1.45  merged_defs:                            0
% 7.67/1.45  merged_defs_ncl:                        0
% 7.67/1.45  bin_hyper_res:                          0
% 7.67/1.45  prep_cycles:                            4
% 7.67/1.45  pred_elim_time:                         0.
% 7.67/1.45  splitting_time:                         0.
% 7.67/1.45  sem_filter_time:                        0.
% 7.67/1.45  monotx_time:                            0.
% 7.67/1.45  subtype_inf_time:                       0.
% 7.67/1.45  
% 7.67/1.45  ------ Problem properties
% 7.67/1.45  
% 7.67/1.45  clauses:                                20
% 7.67/1.45  conjectures:                            1
% 7.67/1.45  epr:                                    0
% 7.67/1.45  horn:                                   20
% 7.67/1.45  ground:                                 1
% 7.67/1.45  unary:                                  6
% 7.67/1.45  binary:                                 9
% 7.67/1.45  lits:                                   41
% 7.67/1.45  lits_eq:                                14
% 7.67/1.45  fd_pure:                                0
% 7.67/1.45  fd_pseudo:                              0
% 7.67/1.45  fd_cond:                                0
% 7.67/1.45  fd_pseudo_cond:                         0
% 7.67/1.45  ac_symbols:                             0
% 7.67/1.45  
% 7.67/1.45  ------ Propositional Solver
% 7.67/1.45  
% 7.67/1.45  prop_solver_calls:                      31
% 7.67/1.45  prop_fast_solver_calls:                 840
% 7.67/1.45  smt_solver_calls:                       0
% 7.67/1.45  smt_fast_solver_calls:                  0
% 7.67/1.45  prop_num_of_clauses:                    7292
% 7.67/1.45  prop_preprocess_simplified:             13081
% 7.67/1.45  prop_fo_subsumed:                       15
% 7.67/1.45  prop_solver_time:                       0.
% 7.67/1.45  smt_solver_time:                        0.
% 7.67/1.45  smt_fast_solver_time:                   0.
% 7.67/1.45  prop_fast_solver_time:                  0.
% 7.67/1.45  prop_unsat_core_time:                   0.
% 7.67/1.45  
% 7.67/1.45  ------ QBF
% 7.67/1.45  
% 7.67/1.45  qbf_q_res:                              0
% 7.67/1.45  qbf_num_tautologies:                    0
% 7.67/1.45  qbf_prep_cycles:                        0
% 7.67/1.45  
% 7.67/1.45  ------ BMC1
% 7.67/1.45  
% 7.67/1.45  bmc1_current_bound:                     -1
% 7.67/1.45  bmc1_last_solved_bound:                 -1
% 7.67/1.45  bmc1_unsat_core_size:                   -1
% 7.67/1.45  bmc1_unsat_core_parents_size:           -1
% 7.67/1.45  bmc1_merge_next_fun:                    0
% 7.67/1.45  bmc1_unsat_core_clauses_time:           0.
% 7.67/1.45  
% 7.67/1.45  ------ Instantiation
% 7.67/1.45  
% 7.67/1.45  inst_num_of_clauses:                    2733
% 7.67/1.45  inst_num_in_passive:                    1608
% 7.67/1.45  inst_num_in_active:                     1002
% 7.67/1.45  inst_num_in_unprocessed:                123
% 7.67/1.45  inst_num_of_loops:                      1080
% 7.67/1.45  inst_num_of_learning_restarts:          0
% 7.67/1.45  inst_num_moves_active_passive:          76
% 7.67/1.45  inst_lit_activity:                      0
% 7.67/1.45  inst_lit_activity_moves:                0
% 7.67/1.45  inst_num_tautologies:                   0
% 7.67/1.45  inst_num_prop_implied:                  0
% 7.67/1.45  inst_num_existing_simplified:           0
% 7.67/1.45  inst_num_eq_res_simplified:             0
% 7.67/1.45  inst_num_child_elim:                    0
% 7.67/1.45  inst_num_of_dismatching_blockings:      584
% 7.67/1.45  inst_num_of_non_proper_insts:           2602
% 7.67/1.45  inst_num_of_duplicates:                 0
% 7.67/1.45  inst_inst_num_from_inst_to_res:         0
% 7.67/1.45  inst_dismatching_checking_time:         0.
% 7.67/1.45  
% 7.67/1.45  ------ Resolution
% 7.67/1.45  
% 7.67/1.45  res_num_of_clauses:                     0
% 7.67/1.45  res_num_in_passive:                     0
% 7.67/1.45  res_num_in_active:                      0
% 7.67/1.45  res_num_of_loops:                       112
% 7.67/1.45  res_forward_subset_subsumed:            524
% 7.67/1.45  res_backward_subset_subsumed:           0
% 7.67/1.45  res_forward_subsumed:                   0
% 7.67/1.45  res_backward_subsumed:                  0
% 7.67/1.45  res_forward_subsumption_resolution:     0
% 7.67/1.45  res_backward_subsumption_resolution:    0
% 7.67/1.45  res_clause_to_clause_subsumption:       6371
% 7.67/1.45  res_orphan_elimination:                 0
% 7.67/1.45  res_tautology_del:                      309
% 7.67/1.45  res_num_eq_res_simplified:              0
% 7.67/1.45  res_num_sel_changes:                    0
% 7.67/1.45  res_moves_from_active_to_pass:          0
% 7.67/1.45  
% 7.67/1.45  ------ Superposition
% 7.67/1.45  
% 7.67/1.45  sup_time_total:                         0.
% 7.67/1.45  sup_time_generating:                    0.
% 7.67/1.45  sup_time_sim_full:                      0.
% 7.67/1.45  sup_time_sim_immed:                     0.
% 7.67/1.45  
% 7.67/1.45  sup_num_of_clauses:                     1220
% 7.67/1.45  sup_num_in_active:                      145
% 7.67/1.45  sup_num_in_passive:                     1075
% 7.67/1.45  sup_num_of_loops:                       214
% 7.67/1.45  sup_fw_superposition:                   3606
% 7.67/1.45  sup_bw_superposition:                   2122
% 7.67/1.45  sup_immediate_simplified:               3135
% 7.67/1.45  sup_given_eliminated:                   3
% 7.67/1.45  comparisons_done:                       0
% 7.67/1.45  comparisons_avoided:                    0
% 7.67/1.45  
% 7.67/1.45  ------ Simplifications
% 7.67/1.45  
% 7.67/1.45  
% 7.67/1.45  sim_fw_subset_subsumed:                 43
% 7.67/1.45  sim_bw_subset_subsumed:                 64
% 7.67/1.45  sim_fw_subsumed:                        212
% 7.67/1.45  sim_bw_subsumed:                        7
% 7.67/1.45  sim_fw_subsumption_res:                 0
% 7.67/1.45  sim_bw_subsumption_res:                 0
% 7.67/1.45  sim_tautology_del:                      7
% 7.67/1.45  sim_eq_tautology_del:                   468
% 7.67/1.45  sim_eq_res_simp:                        0
% 7.67/1.45  sim_fw_demodulated:                     1896
% 7.67/1.45  sim_bw_demodulated:                     94
% 7.67/1.45  sim_light_normalised:                   1957
% 7.67/1.45  sim_joinable_taut:                      0
% 7.67/1.45  sim_joinable_simp:                      0
% 7.67/1.45  sim_ac_normalised:                      0
% 7.67/1.45  sim_smt_subsumption:                    0
% 7.67/1.45  
%------------------------------------------------------------------------------
