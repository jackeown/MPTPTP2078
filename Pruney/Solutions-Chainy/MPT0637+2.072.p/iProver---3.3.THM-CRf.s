%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:50:08 EST 2020

% Result     : Theorem 14.48s
% Output     : CNFRefutation 14.48s
% Verified   : 
% Statistics : Number of formulae       :  162 (1611 expanded)
%              Number of clauses        :   91 ( 762 expanded)
%              Number of leaves         :   22 ( 286 expanded)
%              Depth                    :   22
%              Number of atoms          :  294 (2874 expanded)
%              Number of equality atoms :  175 (1248 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    5 (   2 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f21,axiom,(
    ! [X0] :
      ( v5_relat_1(k6_relat_1(X0),X0)
      & v4_relat_1(k6_relat_1(X0),X0)
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( v4_relat_1(k6_relat_1(X0),X0)
      & v1_relat_1(k6_relat_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f21])).

fof(f69,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f15,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f15])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f36])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f6,axiom,(
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
    inference(ennf_transformation,[],[f6])).

fof(f26,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f62,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f15])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k8_relat_1(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k5_relat_1(X1,k6_relat_1(X0)) = k8_relat_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = k8_relat_1(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = k8_relat_1(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f70,plain,(
    ! [X0] : v4_relat_1(k6_relat_1(X0),X0) ),
    inference(cnf_transformation,[],[f24])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f16,axiom,(
    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f20,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f68,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f5,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f1,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f4])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f48,f49])).

fof(f73,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f47,f72])).

fof(f74,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f46,f73])).

fof(f75,plain,(
    ! [X0,X1] : k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f50,f74])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f52,f75])).

fof(f22,conjecture,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f22])).

fof(f43,plain,(
    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f23])).

fof(f44,plain,
    ( ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))
   => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f43,f44])).

fof(f71,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f45])).

fof(f77,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))) ),
    inference(definition_unfolding,[],[f71,f75])).

cnf(c_19,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_620,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_16,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_622,plain,
    ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_896,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(superposition,[status(thm)],[c_620,c_622])).

cnf(c_13,plain,
    ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_625,plain,
    ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1456,plain,
    ( r1_tarski(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X0)) = iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_896,c_625])).

cnf(c_21,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1893,plain,
    ( r1_tarski(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1456,c_21])).

cnf(c_11,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_627,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_4694,plain,
    ( r1_tarski(X0,k6_relat_1(X1)) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11,c_627])).

cnf(c_5032,plain,
    ( r1_tarski(X0,k6_relat_1(X1)) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4694,c_620])).

cnf(c_5042,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X0) = iProver_top
    | v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1893,c_5032])).

cnf(c_0,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | v1_relat_1(k5_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_634,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k5_relat_1(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2437,plain,
    ( v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_896,c_634])).

cnf(c_4357,plain,
    ( v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2437,c_21])).

cnf(c_4363,plain,
    ( v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4357,c_620])).

cnf(c_52187,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5042,c_4363])).

cnf(c_10,plain,
    ( k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_4,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k8_relat_1(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_630,plain,
    ( k8_relat_1(X0,X1) = X1
    | r1_tarski(k2_relat_1(X1),X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2590,plain,
    ( k8_relat_1(X0,k6_relat_1(X1)) = k6_relat_1(X1)
    | r1_tarski(X1,X0) != iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_10,c_630])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X1,X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_631,plain,
    ( k5_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X1,X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1451,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k8_relat_1(X1,k6_relat_1(X0)) ),
    inference(superposition,[status(thm)],[c_620,c_631])).

cnf(c_1696,plain,
    ( k8_relat_1(X0,k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(light_normalisation,[status(thm)],[c_1451,c_896])).

cnf(c_2594,plain,
    ( k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X1)
    | r1_tarski(X1,X0) != iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2590,c_1696])).

cnf(c_5778,plain,
    ( k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X1)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2594,c_620])).

cnf(c_52215,plain,
    ( k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
    inference(superposition,[status(thm)],[c_52187,c_5778])).

cnf(c_6,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_18,plain,
    ( v4_relat_1(k6_relat_1(X0),X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_217,plain,
    ( ~ v1_relat_1(X0)
    | X1 != X2
    | k7_relat_1(X0,X2) = X0
    | k6_relat_1(X1) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_18])).

cnf(c_218,plain,
    ( ~ v1_relat_1(k6_relat_1(X0))
    | k7_relat_1(k6_relat_1(X0),X0) = k6_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_217])).

cnf(c_222,plain,
    ( k7_relat_1(k6_relat_1(X0),X0) = k6_relat_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_218,c_19])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | k8_relat_1(X1,k7_relat_1(X0,X2)) = k7_relat_1(k8_relat_1(X1,X0),X2) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_629,plain,
    ( k8_relat_1(X0,k7_relat_1(X1,X2)) = k7_relat_1(k8_relat_1(X0,X1),X2)
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1991,plain,
    ( k8_relat_1(X0,k7_relat_1(k6_relat_1(X1),X2)) = k7_relat_1(k8_relat_1(X0,k6_relat_1(X1)),X2) ),
    inference(superposition,[status(thm)],[c_620,c_629])).

cnf(c_1992,plain,
    ( k8_relat_1(X0,k7_relat_1(k6_relat_1(X1),X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) ),
    inference(light_normalisation,[status(thm)],[c_1991,c_1696])).

cnf(c_1995,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X1) = k8_relat_1(X0,k6_relat_1(X1)) ),
    inference(superposition,[status(thm)],[c_222,c_1992])).

cnf(c_1996,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X1) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(light_normalisation,[status(thm)],[c_1995,c_1696])).

cnf(c_15,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_623,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2352,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X1) = iProver_top
    | v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1996,c_623])).

cnf(c_811,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X1)
    | ~ v1_relat_1(k6_relat_1(X0)) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_812,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X1) = iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_811])).

cnf(c_4338,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2352,c_21,c_812])).

cnf(c_5785,plain,
    ( k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(k6_relat_1(X1),X0))) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X1),X0))) ),
    inference(superposition,[status(thm)],[c_4338,c_5778])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k5_relat_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k5_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_626,plain,
    ( k5_relat_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k5_relat_1(X1,X0))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2360,plain,
    ( k5_relat_1(k4_relat_1(k6_relat_1(X0)),k4_relat_1(X1)) = k4_relat_1(k5_relat_1(X1,k6_relat_1(X0)))
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_620,c_626])).

cnf(c_12,plain,
    ( k4_relat_1(k6_relat_1(X0)) = k6_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_2361,plain,
    ( k4_relat_1(k5_relat_1(X0,k6_relat_1(X1))) = k5_relat_1(k6_relat_1(X1),k4_relat_1(X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2360,c_12])).

cnf(c_2429,plain,
    ( k4_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k5_relat_1(k6_relat_1(X1),k4_relat_1(k6_relat_1(X0))) ),
    inference(superposition,[status(thm)],[c_620,c_2361])).

cnf(c_2430,plain,
    ( k4_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) ),
    inference(light_normalisation,[status(thm)],[c_2429,c_12,c_896])).

cnf(c_2431,plain,
    ( k4_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(demodulation,[status(thm)],[c_2430,c_896])).

cnf(c_9107,plain,
    ( k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X1) = k4_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)))) ),
    inference(superposition,[status(thm)],[c_5785,c_2431])).

cnf(c_9150,plain,
    ( k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X1) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
    inference(demodulation,[status(thm)],[c_9107,c_12])).

cnf(c_17,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(X0,k1_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_621,plain,
    ( k7_relat_1(X0,k1_relat_1(X0)) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_4375,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(superposition,[status(thm)],[c_4363,c_621])).

cnf(c_4369,plain,
    ( k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X1),X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X0) ),
    inference(superposition,[status(thm)],[c_4363,c_622])).

cnf(c_4372,plain,
    ( k4_relat_1(k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X2))) = k5_relat_1(k6_relat_1(X2),k4_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
    inference(superposition,[status(thm)],[c_4363,c_2361])).

cnf(c_4374,plain,
    ( k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X2)) = k8_relat_1(X2,k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(superposition,[status(thm)],[c_4363,c_631])).

cnf(c_4379,plain,
    ( k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X0),X1) ),
    inference(demodulation,[status(thm)],[c_4374,c_1992])).

cnf(c_4386,plain,
    ( k5_relat_1(k6_relat_1(X0),k4_relat_1(k7_relat_1(k6_relat_1(X1),X2))) = k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)) ),
    inference(light_normalisation,[status(thm)],[c_4372,c_4379])).

cnf(c_4388,plain,
    ( k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)) = k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X2),X1)) ),
    inference(demodulation,[status(thm)],[c_4386,c_2431])).

cnf(c_4395,plain,
    ( k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X1),X0) ),
    inference(demodulation,[status(thm)],[c_4369,c_4388])).

cnf(c_5278,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X1),X0) = k4_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(superposition,[status(thm)],[c_4375,c_4395])).

cnf(c_5280,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X1),X0) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(light_normalisation,[status(thm)],[c_5278,c_2431])).

cnf(c_10461,plain,
    ( k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X0) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(demodulation,[status(thm)],[c_9150,c_5280])).

cnf(c_11470,plain,
    ( k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k4_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
    inference(superposition,[status(thm)],[c_10461,c_2431])).

cnf(c_11513,plain,
    ( k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(demodulation,[status(thm)],[c_11470,c_2431])).

cnf(c_52217,plain,
    ( k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(light_normalisation,[status(thm)],[c_52215,c_11513])).

cnf(c_53621,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(demodulation,[status(thm)],[c_52217,c_10461])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(X0,k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X2))) = k7_relat_1(k7_relat_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_633,plain,
    ( k7_relat_1(X0,k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X2))) = k7_relat_1(k7_relat_1(X0,X1),X2)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_4671,plain,
    ( k7_relat_1(k6_relat_1(X0),k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X2))) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) ),
    inference(superposition,[status(thm)],[c_620,c_633])).

cnf(c_5661,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))),X0),X1) = k6_relat_1(k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))) ),
    inference(superposition,[status(thm)],[c_4671,c_222])).

cnf(c_5674,plain,
    ( k7_relat_1(k6_relat_1(k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))),X2) = k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X2),X0),X1)) ),
    inference(superposition,[status(thm)],[c_4671,c_2431])).

cnf(c_5706,plain,
    ( k7_relat_1(k6_relat_1(k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))),X2) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X0),X2) ),
    inference(demodulation,[status(thm)],[c_5674,c_4395])).

cnf(c_5744,plain,
    ( k6_relat_1(k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))) = k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X1),X0),X0),X1) ),
    inference(demodulation,[status(thm)],[c_5661,c_5706])).

cnf(c_5746,plain,
    ( k6_relat_1(k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X0),X1) ),
    inference(demodulation,[status(thm)],[c_5744,c_1996])).

cnf(c_20,negated_conjecture,
    ( k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1454,plain,
    ( k6_relat_1(k1_setfam_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))) != k7_relat_1(k6_relat_1(sK0),sK1) ),
    inference(demodulation,[status(thm)],[c_896,c_20])).

cnf(c_19618,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(sK1),sK0),sK1) != k7_relat_1(k6_relat_1(sK0),sK1) ),
    inference(demodulation,[status(thm)],[c_5746,c_1454])).

cnf(c_54803,plain,
    ( k7_relat_1(k6_relat_1(sK0),sK1) != k7_relat_1(k6_relat_1(sK0),sK1) ),
    inference(demodulation,[status(thm)],[c_53621,c_19618])).

cnf(c_54810,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_54803])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:13:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 14.48/2.50  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.48/2.50  
% 14.48/2.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 14.48/2.50  
% 14.48/2.50  ------  iProver source info
% 14.48/2.50  
% 14.48/2.50  git: date: 2020-06-30 10:37:57 +0100
% 14.48/2.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 14.48/2.50  git: non_committed_changes: false
% 14.48/2.50  git: last_make_outside_of_git: false
% 14.48/2.50  
% 14.48/2.50  ------ 
% 14.48/2.50  
% 14.48/2.50  ------ Input Options
% 14.48/2.50  
% 14.48/2.50  --out_options                           all
% 14.48/2.50  --tptp_safe_out                         true
% 14.48/2.50  --problem_path                          ""
% 14.48/2.50  --include_path                          ""
% 14.48/2.50  --clausifier                            res/vclausify_rel
% 14.48/2.50  --clausifier_options                    --mode clausify
% 14.48/2.50  --stdin                                 false
% 14.48/2.50  --stats_out                             all
% 14.48/2.50  
% 14.48/2.50  ------ General Options
% 14.48/2.50  
% 14.48/2.50  --fof                                   false
% 14.48/2.50  --time_out_real                         305.
% 14.48/2.50  --time_out_virtual                      -1.
% 14.48/2.50  --symbol_type_check                     false
% 14.48/2.50  --clausify_out                          false
% 14.48/2.50  --sig_cnt_out                           false
% 14.48/2.50  --trig_cnt_out                          false
% 14.48/2.50  --trig_cnt_out_tolerance                1.
% 14.48/2.50  --trig_cnt_out_sk_spl                   false
% 14.48/2.50  --abstr_cl_out                          false
% 14.48/2.50  
% 14.48/2.50  ------ Global Options
% 14.48/2.50  
% 14.48/2.50  --schedule                              default
% 14.48/2.50  --add_important_lit                     false
% 14.48/2.50  --prop_solver_per_cl                    1000
% 14.48/2.50  --min_unsat_core                        false
% 14.48/2.50  --soft_assumptions                      false
% 14.48/2.50  --soft_lemma_size                       3
% 14.48/2.50  --prop_impl_unit_size                   0
% 14.48/2.50  --prop_impl_unit                        []
% 14.48/2.50  --share_sel_clauses                     true
% 14.48/2.50  --reset_solvers                         false
% 14.48/2.50  --bc_imp_inh                            [conj_cone]
% 14.48/2.50  --conj_cone_tolerance                   3.
% 14.48/2.50  --extra_neg_conj                        none
% 14.48/2.50  --large_theory_mode                     true
% 14.48/2.50  --prolific_symb_bound                   200
% 14.48/2.50  --lt_threshold                          2000
% 14.48/2.50  --clause_weak_htbl                      true
% 14.48/2.50  --gc_record_bc_elim                     false
% 14.48/2.50  
% 14.48/2.50  ------ Preprocessing Options
% 14.48/2.50  
% 14.48/2.50  --preprocessing_flag                    true
% 14.48/2.50  --time_out_prep_mult                    0.1
% 14.48/2.50  --splitting_mode                        input
% 14.48/2.50  --splitting_grd                         true
% 14.48/2.50  --splitting_cvd                         false
% 14.48/2.50  --splitting_cvd_svl                     false
% 14.48/2.50  --splitting_nvd                         32
% 14.48/2.50  --sub_typing                            true
% 14.48/2.50  --prep_gs_sim                           true
% 14.48/2.50  --prep_unflatten                        true
% 14.48/2.50  --prep_res_sim                          true
% 14.48/2.50  --prep_upred                            true
% 14.48/2.50  --prep_sem_filter                       exhaustive
% 14.48/2.50  --prep_sem_filter_out                   false
% 14.48/2.50  --pred_elim                             true
% 14.48/2.50  --res_sim_input                         true
% 14.48/2.50  --eq_ax_congr_red                       true
% 14.48/2.50  --pure_diseq_elim                       true
% 14.48/2.50  --brand_transform                       false
% 14.48/2.50  --non_eq_to_eq                          false
% 14.48/2.50  --prep_def_merge                        true
% 14.48/2.50  --prep_def_merge_prop_impl              false
% 14.48/2.50  --prep_def_merge_mbd                    true
% 14.48/2.50  --prep_def_merge_tr_red                 false
% 14.48/2.50  --prep_def_merge_tr_cl                  false
% 14.48/2.50  --smt_preprocessing                     true
% 14.48/2.50  --smt_ac_axioms                         fast
% 14.48/2.50  --preprocessed_out                      false
% 14.48/2.50  --preprocessed_stats                    false
% 14.48/2.50  
% 14.48/2.50  ------ Abstraction refinement Options
% 14.48/2.50  
% 14.48/2.50  --abstr_ref                             []
% 14.48/2.50  --abstr_ref_prep                        false
% 14.48/2.50  --abstr_ref_until_sat                   false
% 14.48/2.50  --abstr_ref_sig_restrict                funpre
% 14.48/2.50  --abstr_ref_af_restrict_to_split_sk     false
% 14.48/2.50  --abstr_ref_under                       []
% 14.48/2.50  
% 14.48/2.50  ------ SAT Options
% 14.48/2.50  
% 14.48/2.50  --sat_mode                              false
% 14.48/2.50  --sat_fm_restart_options                ""
% 14.48/2.50  --sat_gr_def                            false
% 14.48/2.50  --sat_epr_types                         true
% 14.48/2.50  --sat_non_cyclic_types                  false
% 14.48/2.50  --sat_finite_models                     false
% 14.48/2.50  --sat_fm_lemmas                         false
% 14.48/2.50  --sat_fm_prep                           false
% 14.48/2.50  --sat_fm_uc_incr                        true
% 14.48/2.50  --sat_out_model                         small
% 14.48/2.50  --sat_out_clauses                       false
% 14.48/2.50  
% 14.48/2.50  ------ QBF Options
% 14.48/2.50  
% 14.48/2.50  --qbf_mode                              false
% 14.48/2.50  --qbf_elim_univ                         false
% 14.48/2.50  --qbf_dom_inst                          none
% 14.48/2.50  --qbf_dom_pre_inst                      false
% 14.48/2.50  --qbf_sk_in                             false
% 14.48/2.50  --qbf_pred_elim                         true
% 14.48/2.50  --qbf_split                             512
% 14.48/2.50  
% 14.48/2.50  ------ BMC1 Options
% 14.48/2.50  
% 14.48/2.50  --bmc1_incremental                      false
% 14.48/2.50  --bmc1_axioms                           reachable_all
% 14.48/2.50  --bmc1_min_bound                        0
% 14.48/2.50  --bmc1_max_bound                        -1
% 14.48/2.50  --bmc1_max_bound_default                -1
% 14.48/2.50  --bmc1_symbol_reachability              true
% 14.48/2.50  --bmc1_property_lemmas                  false
% 14.48/2.50  --bmc1_k_induction                      false
% 14.48/2.50  --bmc1_non_equiv_states                 false
% 14.48/2.50  --bmc1_deadlock                         false
% 14.48/2.50  --bmc1_ucm                              false
% 14.48/2.50  --bmc1_add_unsat_core                   none
% 14.48/2.50  --bmc1_unsat_core_children              false
% 14.48/2.50  --bmc1_unsat_core_extrapolate_axioms    false
% 14.48/2.50  --bmc1_out_stat                         full
% 14.48/2.50  --bmc1_ground_init                      false
% 14.48/2.50  --bmc1_pre_inst_next_state              false
% 14.48/2.50  --bmc1_pre_inst_state                   false
% 14.48/2.50  --bmc1_pre_inst_reach_state             false
% 14.48/2.50  --bmc1_out_unsat_core                   false
% 14.48/2.50  --bmc1_aig_witness_out                  false
% 14.48/2.50  --bmc1_verbose                          false
% 14.48/2.50  --bmc1_dump_clauses_tptp                false
% 14.48/2.50  --bmc1_dump_unsat_core_tptp             false
% 14.48/2.50  --bmc1_dump_file                        -
% 14.48/2.50  --bmc1_ucm_expand_uc_limit              128
% 14.48/2.50  --bmc1_ucm_n_expand_iterations          6
% 14.48/2.50  --bmc1_ucm_extend_mode                  1
% 14.48/2.50  --bmc1_ucm_init_mode                    2
% 14.48/2.50  --bmc1_ucm_cone_mode                    none
% 14.48/2.50  --bmc1_ucm_reduced_relation_type        0
% 14.48/2.50  --bmc1_ucm_relax_model                  4
% 14.48/2.50  --bmc1_ucm_full_tr_after_sat            true
% 14.48/2.50  --bmc1_ucm_expand_neg_assumptions       false
% 14.48/2.50  --bmc1_ucm_layered_model                none
% 14.48/2.50  --bmc1_ucm_max_lemma_size               10
% 14.48/2.50  
% 14.48/2.50  ------ AIG Options
% 14.48/2.50  
% 14.48/2.50  --aig_mode                              false
% 14.48/2.50  
% 14.48/2.50  ------ Instantiation Options
% 14.48/2.50  
% 14.48/2.50  --instantiation_flag                    true
% 14.48/2.50  --inst_sos_flag                         false
% 14.48/2.50  --inst_sos_phase                        true
% 14.48/2.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 14.48/2.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 14.48/2.50  --inst_lit_sel_side                     num_symb
% 14.48/2.50  --inst_solver_per_active                1400
% 14.48/2.50  --inst_solver_calls_frac                1.
% 14.48/2.50  --inst_passive_queue_type               priority_queues
% 14.48/2.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 14.48/2.50  --inst_passive_queues_freq              [25;2]
% 14.48/2.50  --inst_dismatching                      true
% 14.48/2.50  --inst_eager_unprocessed_to_passive     true
% 14.48/2.50  --inst_prop_sim_given                   true
% 14.48/2.50  --inst_prop_sim_new                     false
% 14.48/2.50  --inst_subs_new                         false
% 14.48/2.50  --inst_eq_res_simp                      false
% 14.48/2.50  --inst_subs_given                       false
% 14.48/2.50  --inst_orphan_elimination               true
% 14.48/2.50  --inst_learning_loop_flag               true
% 14.48/2.50  --inst_learning_start                   3000
% 14.48/2.50  --inst_learning_factor                  2
% 14.48/2.50  --inst_start_prop_sim_after_learn       3
% 14.48/2.50  --inst_sel_renew                        solver
% 14.48/2.50  --inst_lit_activity_flag                true
% 14.48/2.50  --inst_restr_to_given                   false
% 14.48/2.50  --inst_activity_threshold               500
% 14.48/2.50  --inst_out_proof                        true
% 14.48/2.50  
% 14.48/2.50  ------ Resolution Options
% 14.48/2.50  
% 14.48/2.50  --resolution_flag                       true
% 14.48/2.50  --res_lit_sel                           adaptive
% 14.48/2.50  --res_lit_sel_side                      none
% 14.48/2.50  --res_ordering                          kbo
% 14.48/2.50  --res_to_prop_solver                    active
% 14.48/2.50  --res_prop_simpl_new                    false
% 14.48/2.50  --res_prop_simpl_given                  true
% 14.48/2.50  --res_passive_queue_type                priority_queues
% 14.48/2.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 14.48/2.50  --res_passive_queues_freq               [15;5]
% 14.48/2.50  --res_forward_subs                      full
% 14.48/2.50  --res_backward_subs                     full
% 14.48/2.50  --res_forward_subs_resolution           true
% 14.48/2.50  --res_backward_subs_resolution          true
% 14.48/2.50  --res_orphan_elimination                true
% 14.48/2.50  --res_time_limit                        2.
% 14.48/2.50  --res_out_proof                         true
% 14.48/2.50  
% 14.48/2.50  ------ Superposition Options
% 14.48/2.50  
% 14.48/2.50  --superposition_flag                    true
% 14.48/2.50  --sup_passive_queue_type                priority_queues
% 14.48/2.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 14.48/2.50  --sup_passive_queues_freq               [8;1;4]
% 14.48/2.50  --demod_completeness_check              fast
% 14.48/2.50  --demod_use_ground                      true
% 14.48/2.50  --sup_to_prop_solver                    passive
% 14.48/2.50  --sup_prop_simpl_new                    true
% 14.48/2.50  --sup_prop_simpl_given                  true
% 14.48/2.50  --sup_fun_splitting                     false
% 14.48/2.50  --sup_smt_interval                      50000
% 14.48/2.50  
% 14.48/2.50  ------ Superposition Simplification Setup
% 14.48/2.50  
% 14.48/2.50  --sup_indices_passive                   []
% 14.48/2.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 14.48/2.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 14.48/2.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 14.48/2.50  --sup_full_triv                         [TrivRules;PropSubs]
% 14.48/2.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 14.48/2.50  --sup_full_bw                           [BwDemod]
% 14.48/2.50  --sup_immed_triv                        [TrivRules]
% 14.48/2.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 14.48/2.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 14.48/2.50  --sup_immed_bw_main                     []
% 14.48/2.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 14.48/2.50  --sup_input_triv                        [Unflattening;TrivRules]
% 14.48/2.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 14.48/2.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 14.48/2.50  
% 14.48/2.50  ------ Combination Options
% 14.48/2.50  
% 14.48/2.50  --comb_res_mult                         3
% 14.48/2.50  --comb_sup_mult                         2
% 14.48/2.50  --comb_inst_mult                        10
% 14.48/2.50  
% 14.48/2.50  ------ Debug Options
% 14.48/2.50  
% 14.48/2.50  --dbg_backtrace                         false
% 14.48/2.50  --dbg_dump_prop_clauses                 false
% 14.48/2.50  --dbg_dump_prop_clauses_file            -
% 14.48/2.50  --dbg_out_stat                          false
% 14.48/2.50  ------ Parsing...
% 14.48/2.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 14.48/2.50  
% 14.48/2.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 14.48/2.50  
% 14.48/2.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 14.48/2.50  
% 14.48/2.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 14.48/2.50  ------ Proving...
% 14.48/2.50  ------ Problem Properties 
% 14.48/2.50  
% 14.48/2.50  
% 14.48/2.50  clauses                                 20
% 14.48/2.50  conjectures                             1
% 14.48/2.50  EPR                                     0
% 14.48/2.50  Horn                                    20
% 14.48/2.50  unary                                   6
% 14.48/2.50  binary                                  8
% 14.48/2.50  lits                                    42
% 14.48/2.50  lits eq                                 13
% 14.48/2.50  fd_pure                                 0
% 14.48/2.50  fd_pseudo                               0
% 14.48/2.50  fd_cond                                 0
% 14.48/2.50  fd_pseudo_cond                          0
% 14.48/2.50  AC symbols                              0
% 14.48/2.50  
% 14.48/2.50  ------ Schedule dynamic 5 is on 
% 14.48/2.50  
% 14.48/2.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 14.48/2.50  
% 14.48/2.50  
% 14.48/2.50  ------ 
% 14.48/2.50  Current options:
% 14.48/2.50  ------ 
% 14.48/2.50  
% 14.48/2.50  ------ Input Options
% 14.48/2.50  
% 14.48/2.50  --out_options                           all
% 14.48/2.50  --tptp_safe_out                         true
% 14.48/2.50  --problem_path                          ""
% 14.48/2.50  --include_path                          ""
% 14.48/2.50  --clausifier                            res/vclausify_rel
% 14.48/2.50  --clausifier_options                    --mode clausify
% 14.48/2.50  --stdin                                 false
% 14.48/2.50  --stats_out                             all
% 14.48/2.50  
% 14.48/2.50  ------ General Options
% 14.48/2.50  
% 14.48/2.50  --fof                                   false
% 14.48/2.50  --time_out_real                         305.
% 14.48/2.50  --time_out_virtual                      -1.
% 14.48/2.50  --symbol_type_check                     false
% 14.48/2.50  --clausify_out                          false
% 14.48/2.50  --sig_cnt_out                           false
% 14.48/2.50  --trig_cnt_out                          false
% 14.48/2.50  --trig_cnt_out_tolerance                1.
% 14.48/2.50  --trig_cnt_out_sk_spl                   false
% 14.48/2.50  --abstr_cl_out                          false
% 14.48/2.50  
% 14.48/2.50  ------ Global Options
% 14.48/2.50  
% 14.48/2.50  --schedule                              default
% 14.48/2.50  --add_important_lit                     false
% 14.48/2.50  --prop_solver_per_cl                    1000
% 14.48/2.50  --min_unsat_core                        false
% 14.48/2.50  --soft_assumptions                      false
% 14.48/2.50  --soft_lemma_size                       3
% 14.48/2.50  --prop_impl_unit_size                   0
% 14.48/2.50  --prop_impl_unit                        []
% 14.48/2.50  --share_sel_clauses                     true
% 14.48/2.50  --reset_solvers                         false
% 14.48/2.50  --bc_imp_inh                            [conj_cone]
% 14.48/2.50  --conj_cone_tolerance                   3.
% 14.48/2.50  --extra_neg_conj                        none
% 14.48/2.50  --large_theory_mode                     true
% 14.48/2.50  --prolific_symb_bound                   200
% 14.48/2.50  --lt_threshold                          2000
% 14.48/2.50  --clause_weak_htbl                      true
% 14.48/2.50  --gc_record_bc_elim                     false
% 14.48/2.50  
% 14.48/2.50  ------ Preprocessing Options
% 14.48/2.50  
% 14.48/2.50  --preprocessing_flag                    true
% 14.48/2.50  --time_out_prep_mult                    0.1
% 14.48/2.50  --splitting_mode                        input
% 14.48/2.50  --splitting_grd                         true
% 14.48/2.50  --splitting_cvd                         false
% 14.48/2.50  --splitting_cvd_svl                     false
% 14.48/2.50  --splitting_nvd                         32
% 14.48/2.50  --sub_typing                            true
% 14.48/2.50  --prep_gs_sim                           true
% 14.48/2.50  --prep_unflatten                        true
% 14.48/2.50  --prep_res_sim                          true
% 14.48/2.50  --prep_upred                            true
% 14.48/2.50  --prep_sem_filter                       exhaustive
% 14.48/2.50  --prep_sem_filter_out                   false
% 14.48/2.50  --pred_elim                             true
% 14.48/2.50  --res_sim_input                         true
% 14.48/2.50  --eq_ax_congr_red                       true
% 14.48/2.50  --pure_diseq_elim                       true
% 14.48/2.50  --brand_transform                       false
% 14.48/2.50  --non_eq_to_eq                          false
% 14.48/2.50  --prep_def_merge                        true
% 14.48/2.50  --prep_def_merge_prop_impl              false
% 14.48/2.50  --prep_def_merge_mbd                    true
% 14.48/2.50  --prep_def_merge_tr_red                 false
% 14.48/2.50  --prep_def_merge_tr_cl                  false
% 14.48/2.50  --smt_preprocessing                     true
% 14.48/2.50  --smt_ac_axioms                         fast
% 14.48/2.50  --preprocessed_out                      false
% 14.48/2.50  --preprocessed_stats                    false
% 14.48/2.50  
% 14.48/2.50  ------ Abstraction refinement Options
% 14.48/2.50  
% 14.48/2.50  --abstr_ref                             []
% 14.48/2.50  --abstr_ref_prep                        false
% 14.48/2.50  --abstr_ref_until_sat                   false
% 14.48/2.50  --abstr_ref_sig_restrict                funpre
% 14.48/2.50  --abstr_ref_af_restrict_to_split_sk     false
% 14.48/2.50  --abstr_ref_under                       []
% 14.48/2.50  
% 14.48/2.50  ------ SAT Options
% 14.48/2.50  
% 14.48/2.50  --sat_mode                              false
% 14.48/2.50  --sat_fm_restart_options                ""
% 14.48/2.50  --sat_gr_def                            false
% 14.48/2.50  --sat_epr_types                         true
% 14.48/2.50  --sat_non_cyclic_types                  false
% 14.48/2.50  --sat_finite_models                     false
% 14.48/2.50  --sat_fm_lemmas                         false
% 14.48/2.50  --sat_fm_prep                           false
% 14.48/2.50  --sat_fm_uc_incr                        true
% 14.48/2.50  --sat_out_model                         small
% 14.48/2.50  --sat_out_clauses                       false
% 14.48/2.50  
% 14.48/2.50  ------ QBF Options
% 14.48/2.50  
% 14.48/2.50  --qbf_mode                              false
% 14.48/2.50  --qbf_elim_univ                         false
% 14.48/2.50  --qbf_dom_inst                          none
% 14.48/2.50  --qbf_dom_pre_inst                      false
% 14.48/2.50  --qbf_sk_in                             false
% 14.48/2.50  --qbf_pred_elim                         true
% 14.48/2.50  --qbf_split                             512
% 14.48/2.50  
% 14.48/2.50  ------ BMC1 Options
% 14.48/2.50  
% 14.48/2.50  --bmc1_incremental                      false
% 14.48/2.50  --bmc1_axioms                           reachable_all
% 14.48/2.50  --bmc1_min_bound                        0
% 14.48/2.50  --bmc1_max_bound                        -1
% 14.48/2.50  --bmc1_max_bound_default                -1
% 14.48/2.50  --bmc1_symbol_reachability              true
% 14.48/2.50  --bmc1_property_lemmas                  false
% 14.48/2.50  --bmc1_k_induction                      false
% 14.48/2.50  --bmc1_non_equiv_states                 false
% 14.48/2.50  --bmc1_deadlock                         false
% 14.48/2.50  --bmc1_ucm                              false
% 14.48/2.50  --bmc1_add_unsat_core                   none
% 14.48/2.50  --bmc1_unsat_core_children              false
% 14.48/2.50  --bmc1_unsat_core_extrapolate_axioms    false
% 14.48/2.50  --bmc1_out_stat                         full
% 14.48/2.50  --bmc1_ground_init                      false
% 14.48/2.50  --bmc1_pre_inst_next_state              false
% 14.48/2.50  --bmc1_pre_inst_state                   false
% 14.48/2.50  --bmc1_pre_inst_reach_state             false
% 14.48/2.50  --bmc1_out_unsat_core                   false
% 14.48/2.50  --bmc1_aig_witness_out                  false
% 14.48/2.50  --bmc1_verbose                          false
% 14.48/2.50  --bmc1_dump_clauses_tptp                false
% 14.48/2.50  --bmc1_dump_unsat_core_tptp             false
% 14.48/2.50  --bmc1_dump_file                        -
% 14.48/2.50  --bmc1_ucm_expand_uc_limit              128
% 14.48/2.50  --bmc1_ucm_n_expand_iterations          6
% 14.48/2.50  --bmc1_ucm_extend_mode                  1
% 14.48/2.50  --bmc1_ucm_init_mode                    2
% 14.48/2.50  --bmc1_ucm_cone_mode                    none
% 14.48/2.50  --bmc1_ucm_reduced_relation_type        0
% 14.48/2.50  --bmc1_ucm_relax_model                  4
% 14.48/2.50  --bmc1_ucm_full_tr_after_sat            true
% 14.48/2.50  --bmc1_ucm_expand_neg_assumptions       false
% 14.48/2.50  --bmc1_ucm_layered_model                none
% 14.48/2.50  --bmc1_ucm_max_lemma_size               10
% 14.48/2.50  
% 14.48/2.50  ------ AIG Options
% 14.48/2.50  
% 14.48/2.50  --aig_mode                              false
% 14.48/2.50  
% 14.48/2.50  ------ Instantiation Options
% 14.48/2.50  
% 14.48/2.50  --instantiation_flag                    true
% 14.48/2.50  --inst_sos_flag                         false
% 14.48/2.50  --inst_sos_phase                        true
% 14.48/2.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 14.48/2.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 14.48/2.50  --inst_lit_sel_side                     none
% 14.48/2.50  --inst_solver_per_active                1400
% 14.48/2.50  --inst_solver_calls_frac                1.
% 14.48/2.50  --inst_passive_queue_type               priority_queues
% 14.48/2.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 14.48/2.50  --inst_passive_queues_freq              [25;2]
% 14.48/2.50  --inst_dismatching                      true
% 14.48/2.50  --inst_eager_unprocessed_to_passive     true
% 14.48/2.50  --inst_prop_sim_given                   true
% 14.48/2.50  --inst_prop_sim_new                     false
% 14.48/2.50  --inst_subs_new                         false
% 14.48/2.50  --inst_eq_res_simp                      false
% 14.48/2.50  --inst_subs_given                       false
% 14.48/2.50  --inst_orphan_elimination               true
% 14.48/2.50  --inst_learning_loop_flag               true
% 14.48/2.50  --inst_learning_start                   3000
% 14.48/2.50  --inst_learning_factor                  2
% 14.48/2.50  --inst_start_prop_sim_after_learn       3
% 14.48/2.50  --inst_sel_renew                        solver
% 14.48/2.50  --inst_lit_activity_flag                true
% 14.48/2.50  --inst_restr_to_given                   false
% 14.48/2.50  --inst_activity_threshold               500
% 14.48/2.50  --inst_out_proof                        true
% 14.48/2.50  
% 14.48/2.50  ------ Resolution Options
% 14.48/2.50  
% 14.48/2.50  --resolution_flag                       false
% 14.48/2.50  --res_lit_sel                           adaptive
% 14.48/2.50  --res_lit_sel_side                      none
% 14.48/2.50  --res_ordering                          kbo
% 14.48/2.50  --res_to_prop_solver                    active
% 14.48/2.50  --res_prop_simpl_new                    false
% 14.48/2.50  --res_prop_simpl_given                  true
% 14.48/2.50  --res_passive_queue_type                priority_queues
% 14.48/2.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 14.48/2.50  --res_passive_queues_freq               [15;5]
% 14.48/2.50  --res_forward_subs                      full
% 14.48/2.50  --res_backward_subs                     full
% 14.48/2.50  --res_forward_subs_resolution           true
% 14.48/2.50  --res_backward_subs_resolution          true
% 14.48/2.50  --res_orphan_elimination                true
% 14.48/2.50  --res_time_limit                        2.
% 14.48/2.50  --res_out_proof                         true
% 14.48/2.50  
% 14.48/2.50  ------ Superposition Options
% 14.48/2.50  
% 14.48/2.50  --superposition_flag                    true
% 14.48/2.50  --sup_passive_queue_type                priority_queues
% 14.48/2.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 14.48/2.50  --sup_passive_queues_freq               [8;1;4]
% 14.48/2.50  --demod_completeness_check              fast
% 14.48/2.50  --demod_use_ground                      true
% 14.48/2.50  --sup_to_prop_solver                    passive
% 14.48/2.50  --sup_prop_simpl_new                    true
% 14.48/2.50  --sup_prop_simpl_given                  true
% 14.48/2.50  --sup_fun_splitting                     false
% 14.48/2.50  --sup_smt_interval                      50000
% 14.48/2.50  
% 14.48/2.50  ------ Superposition Simplification Setup
% 14.48/2.50  
% 14.48/2.50  --sup_indices_passive                   []
% 14.48/2.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 14.48/2.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 14.48/2.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 14.48/2.50  --sup_full_triv                         [TrivRules;PropSubs]
% 14.48/2.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 14.48/2.50  --sup_full_bw                           [BwDemod]
% 14.48/2.50  --sup_immed_triv                        [TrivRules]
% 14.48/2.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 14.48/2.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 14.48/2.50  --sup_immed_bw_main                     []
% 14.48/2.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 14.48/2.50  --sup_input_triv                        [Unflattening;TrivRules]
% 14.48/2.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 14.48/2.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 14.48/2.50  
% 14.48/2.50  ------ Combination Options
% 14.48/2.50  
% 14.48/2.50  --comb_res_mult                         3
% 14.48/2.50  --comb_sup_mult                         2
% 14.48/2.50  --comb_inst_mult                        10
% 14.48/2.50  
% 14.48/2.50  ------ Debug Options
% 14.48/2.50  
% 14.48/2.50  --dbg_backtrace                         false
% 14.48/2.50  --dbg_dump_prop_clauses                 false
% 14.48/2.50  --dbg_dump_prop_clauses_file            -
% 14.48/2.50  --dbg_out_stat                          false
% 14.48/2.50  
% 14.48/2.50  
% 14.48/2.50  
% 14.48/2.50  
% 14.48/2.50  ------ Proving...
% 14.48/2.50  
% 14.48/2.50  
% 14.48/2.50  % SZS status Theorem for theBenchmark.p
% 14.48/2.50  
% 14.48/2.50   Resolution empty clause
% 14.48/2.50  
% 14.48/2.50  % SZS output start CNFRefutation for theBenchmark.p
% 14.48/2.50  
% 14.48/2.50  fof(f21,axiom,(
% 14.48/2.50    ! [X0] : (v5_relat_1(k6_relat_1(X0),X0) & v4_relat_1(k6_relat_1(X0),X0) & v1_relat_1(k6_relat_1(X0)))),
% 14.48/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 14.48/2.50  
% 14.48/2.50  fof(f24,plain,(
% 14.48/2.50    ! [X0] : (v4_relat_1(k6_relat_1(X0),X0) & v1_relat_1(k6_relat_1(X0)))),
% 14.48/2.50    inference(pure_predicate_removal,[],[f21])).
% 14.48/2.50  
% 14.48/2.50  fof(f69,plain,(
% 14.48/2.50    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 14.48/2.50    inference(cnf_transformation,[],[f24])).
% 14.48/2.50  
% 14.48/2.50  fof(f19,axiom,(
% 14.48/2.50    ! [X0,X1] : (v1_relat_1(X1) => k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0))),
% 14.48/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 14.48/2.50  
% 14.48/2.50  fof(f41,plain,(
% 14.48/2.50    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 14.48/2.50    inference(ennf_transformation,[],[f19])).
% 14.48/2.50  
% 14.48/2.50  fof(f67,plain,(
% 14.48/2.50    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 14.48/2.50    inference(cnf_transformation,[],[f41])).
% 14.48/2.50  
% 14.48/2.50  fof(f17,axiom,(
% 14.48/2.50    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)))),
% 14.48/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 14.48/2.50  
% 14.48/2.50  fof(f39,plain,(
% 14.48/2.50    ! [X0,X1] : ((r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)) | ~v1_relat_1(X1))),
% 14.48/2.50    inference(ennf_transformation,[],[f17])).
% 14.48/2.50  
% 14.48/2.50  fof(f65,plain,(
% 14.48/2.50    ( ! [X0,X1] : (r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) | ~v1_relat_1(X1)) )),
% 14.48/2.50    inference(cnf_transformation,[],[f39])).
% 14.48/2.50  
% 14.48/2.50  fof(f15,axiom,(
% 14.48/2.50    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 14.48/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 14.48/2.50  
% 14.48/2.50  fof(f61,plain,(
% 14.48/2.50    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 14.48/2.50    inference(cnf_transformation,[],[f15])).
% 14.48/2.50  
% 14.48/2.50  fof(f13,axiom,(
% 14.48/2.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 14.48/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 14.48/2.50  
% 14.48/2.50  fof(f36,plain,(
% 14.48/2.50    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 14.48/2.50    inference(ennf_transformation,[],[f13])).
% 14.48/2.50  
% 14.48/2.50  fof(f37,plain,(
% 14.48/2.50    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 14.48/2.50    inference(flattening,[],[f36])).
% 14.48/2.50  
% 14.48/2.50  fof(f58,plain,(
% 14.48/2.50    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 14.48/2.50    inference(cnf_transformation,[],[f37])).
% 14.48/2.50  
% 14.48/2.50  fof(f6,axiom,(
% 14.48/2.50    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 14.48/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 14.48/2.50  
% 14.48/2.50  fof(f25,plain,(
% 14.48/2.50    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 14.48/2.50    inference(ennf_transformation,[],[f6])).
% 14.48/2.50  
% 14.48/2.50  fof(f26,plain,(
% 14.48/2.50    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 14.48/2.50    inference(flattening,[],[f25])).
% 14.48/2.50  
% 14.48/2.50  fof(f51,plain,(
% 14.48/2.50    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 14.48/2.50    inference(cnf_transformation,[],[f26])).
% 14.48/2.50  
% 14.48/2.50  fof(f62,plain,(
% 14.48/2.50    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 14.48/2.50    inference(cnf_transformation,[],[f15])).
% 14.48/2.50  
% 14.48/2.50  fof(f10,axiom,(
% 14.48/2.50    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k8_relat_1(X0,X1) = X1))),
% 14.48/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 14.48/2.50  
% 14.48/2.50  fof(f31,plain,(
% 14.48/2.50    ! [X0,X1] : ((k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 14.48/2.50    inference(ennf_transformation,[],[f10])).
% 14.48/2.50  
% 14.48/2.50  fof(f32,plain,(
% 14.48/2.50    ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 14.48/2.50    inference(flattening,[],[f31])).
% 14.48/2.50  
% 14.48/2.50  fof(f55,plain,(
% 14.48/2.50    ( ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 14.48/2.50    inference(cnf_transformation,[],[f32])).
% 14.48/2.50  
% 14.48/2.50  fof(f9,axiom,(
% 14.48/2.50    ! [X0,X1] : (v1_relat_1(X1) => k5_relat_1(X1,k6_relat_1(X0)) = k8_relat_1(X0,X1))),
% 14.48/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 14.48/2.50  
% 14.48/2.50  fof(f30,plain,(
% 14.48/2.50    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = k8_relat_1(X0,X1) | ~v1_relat_1(X1))),
% 14.48/2.50    inference(ennf_transformation,[],[f9])).
% 14.48/2.50  
% 14.48/2.50  fof(f54,plain,(
% 14.48/2.50    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = k8_relat_1(X0,X1) | ~v1_relat_1(X1)) )),
% 14.48/2.50    inference(cnf_transformation,[],[f30])).
% 14.48/2.50  
% 14.48/2.50  fof(f12,axiom,(
% 14.48/2.50    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 14.48/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 14.48/2.50  
% 14.48/2.50  fof(f34,plain,(
% 14.48/2.50    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 14.48/2.50    inference(ennf_transformation,[],[f12])).
% 14.48/2.50  
% 14.48/2.50  fof(f35,plain,(
% 14.48/2.50    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 14.48/2.50    inference(flattening,[],[f34])).
% 14.48/2.50  
% 14.48/2.50  fof(f57,plain,(
% 14.48/2.50    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 14.48/2.50    inference(cnf_transformation,[],[f35])).
% 14.48/2.50  
% 14.48/2.50  fof(f70,plain,(
% 14.48/2.50    ( ! [X0] : (v4_relat_1(k6_relat_1(X0),X0)) )),
% 14.48/2.50    inference(cnf_transformation,[],[f24])).
% 14.48/2.50  
% 14.48/2.50  fof(f11,axiom,(
% 14.48/2.50    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)))),
% 14.48/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 14.48/2.50  
% 14.48/2.50  fof(f33,plain,(
% 14.48/2.50    ! [X0,X1,X2] : (k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 14.48/2.50    inference(ennf_transformation,[],[f11])).
% 14.48/2.50  
% 14.48/2.50  fof(f56,plain,(
% 14.48/2.50    ( ! [X2,X0,X1] : (k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 14.48/2.50    inference(cnf_transformation,[],[f33])).
% 14.48/2.50  
% 14.48/2.50  fof(f18,axiom,(
% 14.48/2.50    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 14.48/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 14.48/2.50  
% 14.48/2.50  fof(f40,plain,(
% 14.48/2.50    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 14.48/2.50    inference(ennf_transformation,[],[f18])).
% 14.48/2.50  
% 14.48/2.50  fof(f66,plain,(
% 14.48/2.50    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 14.48/2.50    inference(cnf_transformation,[],[f40])).
% 14.48/2.50  
% 14.48/2.50  fof(f14,axiom,(
% 14.48/2.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,X1))))),
% 14.48/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 14.48/2.50  
% 14.48/2.50  fof(f38,plain,(
% 14.48/2.50    ! [X0] : (! [X1] : (k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 14.48/2.50    inference(ennf_transformation,[],[f14])).
% 14.48/2.50  
% 14.48/2.50  fof(f60,plain,(
% 14.48/2.50    ( ! [X0,X1] : (k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 14.48/2.50    inference(cnf_transformation,[],[f38])).
% 14.48/2.50  
% 14.48/2.50  fof(f16,axiom,(
% 14.48/2.50    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))),
% 14.48/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 14.48/2.50  
% 14.48/2.50  fof(f63,plain,(
% 14.48/2.50    ( ! [X0] : (k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))) )),
% 14.48/2.50    inference(cnf_transformation,[],[f16])).
% 14.48/2.50  
% 14.48/2.50  fof(f20,axiom,(
% 14.48/2.50    ! [X0] : (v1_relat_1(X0) => k7_relat_1(X0,k1_relat_1(X0)) = X0)),
% 14.48/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 14.48/2.50  
% 14.48/2.50  fof(f42,plain,(
% 14.48/2.50    ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 14.48/2.50    inference(ennf_transformation,[],[f20])).
% 14.48/2.50  
% 14.48/2.50  fof(f68,plain,(
% 14.48/2.50    ( ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0)) )),
% 14.48/2.50    inference(cnf_transformation,[],[f42])).
% 14.48/2.50  
% 14.48/2.50  fof(f7,axiom,(
% 14.48/2.50    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1))),
% 14.48/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 14.48/2.50  
% 14.48/2.50  fof(f27,plain,(
% 14.48/2.50    ! [X0,X1,X2] : (k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2))),
% 14.48/2.50    inference(ennf_transformation,[],[f7])).
% 14.48/2.50  
% 14.48/2.50  fof(f52,plain,(
% 14.48/2.50    ( ! [X2,X0,X1] : (k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 14.48/2.50    inference(cnf_transformation,[],[f27])).
% 14.48/2.50  
% 14.48/2.50  fof(f5,axiom,(
% 14.48/2.50    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 14.48/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 14.48/2.50  
% 14.48/2.50  fof(f50,plain,(
% 14.48/2.50    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 14.48/2.50    inference(cnf_transformation,[],[f5])).
% 14.48/2.50  
% 14.48/2.50  fof(f1,axiom,(
% 14.48/2.50    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 14.48/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 14.48/2.50  
% 14.48/2.50  fof(f46,plain,(
% 14.48/2.50    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 14.48/2.50    inference(cnf_transformation,[],[f1])).
% 14.48/2.50  
% 14.48/2.50  fof(f2,axiom,(
% 14.48/2.50    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 14.48/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 14.48/2.50  
% 14.48/2.50  fof(f47,plain,(
% 14.48/2.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 14.48/2.50    inference(cnf_transformation,[],[f2])).
% 14.48/2.50  
% 14.48/2.50  fof(f3,axiom,(
% 14.48/2.50    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 14.48/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 14.48/2.50  
% 14.48/2.50  fof(f48,plain,(
% 14.48/2.50    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 14.48/2.50    inference(cnf_transformation,[],[f3])).
% 14.48/2.50  
% 14.48/2.50  fof(f4,axiom,(
% 14.48/2.50    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 14.48/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 14.48/2.50  
% 14.48/2.50  fof(f49,plain,(
% 14.48/2.50    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 14.48/2.50    inference(cnf_transformation,[],[f4])).
% 14.48/2.50  
% 14.48/2.50  fof(f72,plain,(
% 14.48/2.50    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 14.48/2.50    inference(definition_unfolding,[],[f48,f49])).
% 14.48/2.50  
% 14.48/2.50  fof(f73,plain,(
% 14.48/2.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 14.48/2.50    inference(definition_unfolding,[],[f47,f72])).
% 14.48/2.50  
% 14.48/2.50  fof(f74,plain,(
% 14.48/2.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1)) )),
% 14.48/2.50    inference(definition_unfolding,[],[f46,f73])).
% 14.48/2.50  
% 14.48/2.50  fof(f75,plain,(
% 14.48/2.50    ( ! [X0,X1] : (k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)) = k3_xboole_0(X0,X1)) )),
% 14.48/2.50    inference(definition_unfolding,[],[f50,f74])).
% 14.48/2.50  
% 14.48/2.50  fof(f76,plain,(
% 14.48/2.50    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))) | ~v1_relat_1(X2)) )),
% 14.48/2.50    inference(definition_unfolding,[],[f52,f75])).
% 14.48/2.50  
% 14.48/2.50  fof(f22,conjecture,(
% 14.48/2.50    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 14.48/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 14.48/2.50  
% 14.48/2.50  fof(f23,negated_conjecture,(
% 14.48/2.50    ~! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 14.48/2.50    inference(negated_conjecture,[],[f22])).
% 14.48/2.50  
% 14.48/2.50  fof(f43,plain,(
% 14.48/2.50    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))),
% 14.48/2.50    inference(ennf_transformation,[],[f23])).
% 14.48/2.50  
% 14.48/2.50  fof(f44,plain,(
% 14.48/2.50    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 14.48/2.50    introduced(choice_axiom,[])).
% 14.48/2.50  
% 14.48/2.50  fof(f45,plain,(
% 14.48/2.50    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 14.48/2.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f43,f44])).
% 14.48/2.50  
% 14.48/2.50  fof(f71,plain,(
% 14.48/2.50    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 14.48/2.50    inference(cnf_transformation,[],[f45])).
% 14.48/2.50  
% 14.48/2.50  fof(f77,plain,(
% 14.48/2.50    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1)))),
% 14.48/2.50    inference(definition_unfolding,[],[f71,f75])).
% 14.48/2.50  
% 14.48/2.50  cnf(c_19,plain,
% 14.48/2.50      ( v1_relat_1(k6_relat_1(X0)) ),
% 14.48/2.50      inference(cnf_transformation,[],[f69]) ).
% 14.48/2.50  
% 14.48/2.50  cnf(c_620,plain,
% 14.48/2.50      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 14.48/2.50      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 14.48/2.50  
% 14.48/2.50  cnf(c_16,plain,
% 14.48/2.50      ( ~ v1_relat_1(X0) | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
% 14.48/2.50      inference(cnf_transformation,[],[f67]) ).
% 14.48/2.50  
% 14.48/2.50  cnf(c_622,plain,
% 14.48/2.50      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
% 14.48/2.50      | v1_relat_1(X1) != iProver_top ),
% 14.48/2.50      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 14.48/2.50  
% 14.48/2.50  cnf(c_896,plain,
% 14.48/2.50      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
% 14.48/2.50      inference(superposition,[status(thm)],[c_620,c_622]) ).
% 14.48/2.50  
% 14.48/2.50  cnf(c_13,plain,
% 14.48/2.50      ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) | ~ v1_relat_1(X1) ),
% 14.48/2.50      inference(cnf_transformation,[],[f65]) ).
% 14.48/2.50  
% 14.48/2.50  cnf(c_625,plain,
% 14.48/2.50      ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) = iProver_top
% 14.48/2.50      | v1_relat_1(X1) != iProver_top ),
% 14.48/2.50      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 14.48/2.50  
% 14.48/2.50  cnf(c_1456,plain,
% 14.48/2.50      ( r1_tarski(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X0)) = iProver_top
% 14.48/2.50      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 14.48/2.50      inference(superposition,[status(thm)],[c_896,c_625]) ).
% 14.48/2.50  
% 14.48/2.50  cnf(c_21,plain,
% 14.48/2.50      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 14.48/2.50      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 14.48/2.50  
% 14.48/2.50  cnf(c_1893,plain,
% 14.48/2.50      ( r1_tarski(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X0)) = iProver_top ),
% 14.48/2.50      inference(global_propositional_subsumption,[status(thm)],[c_1456,c_21]) ).
% 14.48/2.50  
% 14.48/2.50  cnf(c_11,plain,
% 14.48/2.50      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 14.48/2.50      inference(cnf_transformation,[],[f61]) ).
% 14.48/2.50  
% 14.48/2.50  cnf(c_8,plain,
% 14.48/2.50      ( ~ r1_tarski(X0,X1)
% 14.48/2.50      | r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
% 14.48/2.50      | ~ v1_relat_1(X1)
% 14.48/2.50      | ~ v1_relat_1(X0) ),
% 14.48/2.50      inference(cnf_transformation,[],[f58]) ).
% 14.48/2.50  
% 14.48/2.50  cnf(c_627,plain,
% 14.48/2.50      ( r1_tarski(X0,X1) != iProver_top
% 14.48/2.50      | r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) = iProver_top
% 14.48/2.50      | v1_relat_1(X0) != iProver_top
% 14.48/2.50      | v1_relat_1(X1) != iProver_top ),
% 14.48/2.50      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 14.48/2.50  
% 14.48/2.50  cnf(c_4694,plain,
% 14.48/2.50      ( r1_tarski(X0,k6_relat_1(X1)) != iProver_top
% 14.48/2.50      | r1_tarski(k1_relat_1(X0),X1) = iProver_top
% 14.48/2.50      | v1_relat_1(X0) != iProver_top
% 14.48/2.50      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 14.48/2.50      inference(superposition,[status(thm)],[c_11,c_627]) ).
% 14.48/2.50  
% 14.48/2.50  cnf(c_5032,plain,
% 14.48/2.50      ( r1_tarski(X0,k6_relat_1(X1)) != iProver_top
% 14.48/2.50      | r1_tarski(k1_relat_1(X0),X1) = iProver_top
% 14.48/2.50      | v1_relat_1(X0) != iProver_top ),
% 14.48/2.50      inference(forward_subsumption_resolution,[status(thm)],[c_4694,c_620]) ).
% 14.48/2.50  
% 14.48/2.50  cnf(c_5042,plain,
% 14.48/2.50      ( r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X0) = iProver_top
% 14.48/2.50      | v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) != iProver_top ),
% 14.48/2.50      inference(superposition,[status(thm)],[c_1893,c_5032]) ).
% 14.48/2.50  
% 14.48/2.50  cnf(c_0,plain,
% 14.48/2.50      ( ~ v1_relat_1(X0) | ~ v1_relat_1(X1) | v1_relat_1(k5_relat_1(X1,X0)) ),
% 14.48/2.50      inference(cnf_transformation,[],[f51]) ).
% 14.48/2.50  
% 14.48/2.50  cnf(c_634,plain,
% 14.48/2.50      ( v1_relat_1(X0) != iProver_top
% 14.48/2.50      | v1_relat_1(X1) != iProver_top
% 14.48/2.50      | v1_relat_1(k5_relat_1(X1,X0)) = iProver_top ),
% 14.48/2.50      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 14.48/2.50  
% 14.48/2.50  cnf(c_2437,plain,
% 14.48/2.50      ( v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = iProver_top
% 14.48/2.50      | v1_relat_1(k6_relat_1(X0)) != iProver_top
% 14.48/2.50      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 14.48/2.50      inference(superposition,[status(thm)],[c_896,c_634]) ).
% 14.48/2.50  
% 14.48/2.50  cnf(c_4357,plain,
% 14.48/2.50      ( v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = iProver_top
% 14.48/2.50      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 14.48/2.50      inference(global_propositional_subsumption,[status(thm)],[c_2437,c_21]) ).
% 14.48/2.50  
% 14.48/2.50  cnf(c_4363,plain,
% 14.48/2.50      ( v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = iProver_top ),
% 14.48/2.50      inference(forward_subsumption_resolution,[status(thm)],[c_4357,c_620]) ).
% 14.48/2.50  
% 14.48/2.50  cnf(c_52187,plain,
% 14.48/2.50      ( r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X0) = iProver_top ),
% 14.48/2.50      inference(global_propositional_subsumption,[status(thm)],[c_5042,c_4363]) ).
% 14.48/2.50  
% 14.48/2.50  cnf(c_10,plain,
% 14.48/2.50      ( k2_relat_1(k6_relat_1(X0)) = X0 ),
% 14.48/2.50      inference(cnf_transformation,[],[f62]) ).
% 14.48/2.50  
% 14.48/2.50  cnf(c_4,plain,
% 14.48/2.50      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 14.48/2.50      | ~ v1_relat_1(X0)
% 14.48/2.50      | k8_relat_1(X1,X0) = X0 ),
% 14.48/2.50      inference(cnf_transformation,[],[f55]) ).
% 14.48/2.50  
% 14.48/2.50  cnf(c_630,plain,
% 14.48/2.50      ( k8_relat_1(X0,X1) = X1
% 14.48/2.50      | r1_tarski(k2_relat_1(X1),X0) != iProver_top
% 14.48/2.50      | v1_relat_1(X1) != iProver_top ),
% 14.48/2.50      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 14.48/2.50  
% 14.48/2.50  cnf(c_2590,plain,
% 14.48/2.50      ( k8_relat_1(X0,k6_relat_1(X1)) = k6_relat_1(X1)
% 14.48/2.50      | r1_tarski(X1,X0) != iProver_top
% 14.48/2.50      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 14.48/2.50      inference(superposition,[status(thm)],[c_10,c_630]) ).
% 14.48/2.50  
% 14.48/2.50  cnf(c_3,plain,
% 14.48/2.50      ( ~ v1_relat_1(X0) | k5_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X1,X0) ),
% 14.48/2.50      inference(cnf_transformation,[],[f54]) ).
% 14.48/2.50  
% 14.48/2.50  cnf(c_631,plain,
% 14.48/2.50      ( k5_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X1,X0)
% 14.48/2.50      | v1_relat_1(X0) != iProver_top ),
% 14.48/2.50      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 14.48/2.50  
% 14.48/2.50  cnf(c_1451,plain,
% 14.48/2.50      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k8_relat_1(X1,k6_relat_1(X0)) ),
% 14.48/2.50      inference(superposition,[status(thm)],[c_620,c_631]) ).
% 14.48/2.50  
% 14.48/2.50  cnf(c_1696,plain,
% 14.48/2.50      ( k8_relat_1(X0,k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X0),X1) ),
% 14.48/2.50      inference(light_normalisation,[status(thm)],[c_1451,c_896]) ).
% 14.48/2.50  
% 14.48/2.50  cnf(c_2594,plain,
% 14.48/2.50      ( k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X1)
% 14.48/2.50      | r1_tarski(X1,X0) != iProver_top
% 14.48/2.50      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 14.48/2.50      inference(demodulation,[status(thm)],[c_2590,c_1696]) ).
% 14.48/2.50  
% 14.48/2.50  cnf(c_5778,plain,
% 14.48/2.50      ( k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X1)
% 14.48/2.50      | r1_tarski(X1,X0) != iProver_top ),
% 14.48/2.50      inference(forward_subsumption_resolution,[status(thm)],[c_2594,c_620]) ).
% 14.48/2.50  
% 14.48/2.50  cnf(c_52215,plain,
% 14.48/2.50      ( k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
% 14.48/2.50      inference(superposition,[status(thm)],[c_52187,c_5778]) ).
% 14.48/2.50  
% 14.48/2.50  cnf(c_6,plain,
% 14.48/2.50      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 14.48/2.50      inference(cnf_transformation,[],[f57]) ).
% 14.48/2.50  
% 14.48/2.50  cnf(c_18,plain,
% 14.48/2.50      ( v4_relat_1(k6_relat_1(X0),X0) ),
% 14.48/2.50      inference(cnf_transformation,[],[f70]) ).
% 14.48/2.50  
% 14.48/2.50  cnf(c_217,plain,
% 14.48/2.50      ( ~ v1_relat_1(X0)
% 14.48/2.50      | X1 != X2
% 14.48/2.50      | k7_relat_1(X0,X2) = X0
% 14.48/2.50      | k6_relat_1(X1) != X0 ),
% 14.48/2.50      inference(resolution_lifted,[status(thm)],[c_6,c_18]) ).
% 14.48/2.50  
% 14.48/2.50  cnf(c_218,plain,
% 14.48/2.50      ( ~ v1_relat_1(k6_relat_1(X0))
% 14.48/2.50      | k7_relat_1(k6_relat_1(X0),X0) = k6_relat_1(X0) ),
% 14.48/2.50      inference(unflattening,[status(thm)],[c_217]) ).
% 14.48/2.50  
% 14.48/2.50  cnf(c_222,plain,
% 14.48/2.50      ( k7_relat_1(k6_relat_1(X0),X0) = k6_relat_1(X0) ),
% 14.48/2.50      inference(global_propositional_subsumption,[status(thm)],[c_218,c_19]) ).
% 14.48/2.50  
% 14.48/2.50  cnf(c_5,plain,
% 14.48/2.50      ( ~ v1_relat_1(X0)
% 14.48/2.50      | k8_relat_1(X1,k7_relat_1(X0,X2)) = k7_relat_1(k8_relat_1(X1,X0),X2) ),
% 14.48/2.50      inference(cnf_transformation,[],[f56]) ).
% 14.48/2.50  
% 14.48/2.50  cnf(c_629,plain,
% 14.48/2.50      ( k8_relat_1(X0,k7_relat_1(X1,X2)) = k7_relat_1(k8_relat_1(X0,X1),X2)
% 14.48/2.50      | v1_relat_1(X1) != iProver_top ),
% 14.48/2.50      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 14.48/2.50  
% 14.48/2.50  cnf(c_1991,plain,
% 14.48/2.50      ( k8_relat_1(X0,k7_relat_1(k6_relat_1(X1),X2)) = k7_relat_1(k8_relat_1(X0,k6_relat_1(X1)),X2) ),
% 14.48/2.50      inference(superposition,[status(thm)],[c_620,c_629]) ).
% 14.48/2.50  
% 14.48/2.50  cnf(c_1992,plain,
% 14.48/2.50      ( k8_relat_1(X0,k7_relat_1(k6_relat_1(X1),X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) ),
% 14.48/2.50      inference(light_normalisation,[status(thm)],[c_1991,c_1696]) ).
% 14.48/2.50  
% 14.48/2.50  cnf(c_1995,plain,
% 14.48/2.50      ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X1) = k8_relat_1(X0,k6_relat_1(X1)) ),
% 14.48/2.50      inference(superposition,[status(thm)],[c_222,c_1992]) ).
% 14.48/2.50  
% 14.48/2.50  cnf(c_1996,plain,
% 14.48/2.50      ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X1) = k7_relat_1(k6_relat_1(X0),X1) ),
% 14.48/2.50      inference(light_normalisation,[status(thm)],[c_1995,c_1696]) ).
% 14.48/2.50  
% 14.48/2.50  cnf(c_15,plain,
% 14.48/2.50      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) | ~ v1_relat_1(X0) ),
% 14.48/2.50      inference(cnf_transformation,[],[f66]) ).
% 14.48/2.50  
% 14.48/2.50  cnf(c_623,plain,
% 14.48/2.50      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) = iProver_top
% 14.48/2.50      | v1_relat_1(X0) != iProver_top ),
% 14.48/2.50      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 14.48/2.50  
% 14.48/2.50  cnf(c_2352,plain,
% 14.48/2.50      ( r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X1) = iProver_top
% 14.48/2.50      | v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) != iProver_top ),
% 14.48/2.50      inference(superposition,[status(thm)],[c_1996,c_623]) ).
% 14.48/2.50  
% 14.48/2.50  cnf(c_811,plain,
% 14.48/2.50      ( r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X1)
% 14.48/2.50      | ~ v1_relat_1(k6_relat_1(X0)) ),
% 14.48/2.50      inference(instantiation,[status(thm)],[c_15]) ).
% 14.48/2.50  
% 14.48/2.50  cnf(c_812,plain,
% 14.48/2.50      ( r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X1) = iProver_top
% 14.48/2.50      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 14.48/2.50      inference(predicate_to_equality,[status(thm)],[c_811]) ).
% 14.48/2.50  
% 14.48/2.50  cnf(c_4338,plain,
% 14.48/2.50      ( r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X1) = iProver_top ),
% 14.48/2.50      inference(global_propositional_subsumption,
% 14.48/2.50                [status(thm)],
% 14.48/2.50                [c_2352,c_21,c_812]) ).
% 14.48/2.50  
% 14.48/2.50  cnf(c_5785,plain,
% 14.48/2.50      ( k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(k6_relat_1(X1),X0))) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X1),X0))) ),
% 14.48/2.50      inference(superposition,[status(thm)],[c_4338,c_5778]) ).
% 14.48/2.50  
% 14.48/2.50  cnf(c_9,plain,
% 14.48/2.50      ( ~ v1_relat_1(X0)
% 14.48/2.50      | ~ v1_relat_1(X1)
% 14.48/2.50      | k5_relat_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k5_relat_1(X1,X0)) ),
% 14.48/2.50      inference(cnf_transformation,[],[f60]) ).
% 14.48/2.50  
% 14.48/2.50  cnf(c_626,plain,
% 14.48/2.50      ( k5_relat_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k5_relat_1(X1,X0))
% 14.48/2.50      | v1_relat_1(X0) != iProver_top
% 14.48/2.50      | v1_relat_1(X1) != iProver_top ),
% 14.48/2.50      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 14.48/2.50  
% 14.48/2.50  cnf(c_2360,plain,
% 14.48/2.50      ( k5_relat_1(k4_relat_1(k6_relat_1(X0)),k4_relat_1(X1)) = k4_relat_1(k5_relat_1(X1,k6_relat_1(X0)))
% 14.48/2.50      | v1_relat_1(X1) != iProver_top ),
% 14.48/2.50      inference(superposition,[status(thm)],[c_620,c_626]) ).
% 14.48/2.50  
% 14.48/2.50  cnf(c_12,plain,
% 14.48/2.50      ( k4_relat_1(k6_relat_1(X0)) = k6_relat_1(X0) ),
% 14.48/2.50      inference(cnf_transformation,[],[f63]) ).
% 14.48/2.50  
% 14.48/2.50  cnf(c_2361,plain,
% 14.48/2.50      ( k4_relat_1(k5_relat_1(X0,k6_relat_1(X1))) = k5_relat_1(k6_relat_1(X1),k4_relat_1(X0))
% 14.48/2.50      | v1_relat_1(X0) != iProver_top ),
% 14.48/2.50      inference(light_normalisation,[status(thm)],[c_2360,c_12]) ).
% 14.48/2.50  
% 14.48/2.50  cnf(c_2429,plain,
% 14.48/2.50      ( k4_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k5_relat_1(k6_relat_1(X1),k4_relat_1(k6_relat_1(X0))) ),
% 14.48/2.50      inference(superposition,[status(thm)],[c_620,c_2361]) ).
% 14.48/2.50  
% 14.48/2.50  cnf(c_2430,plain,
% 14.48/2.50      ( k4_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) ),
% 14.48/2.50      inference(light_normalisation,[status(thm)],[c_2429,c_12,c_896]) ).
% 14.48/2.50  
% 14.48/2.50  cnf(c_2431,plain,
% 14.48/2.50      ( k4_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
% 14.48/2.50      inference(demodulation,[status(thm)],[c_2430,c_896]) ).
% 14.48/2.50  
% 14.48/2.50  cnf(c_9107,plain,
% 14.48/2.50      ( k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X1) = k4_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)))) ),
% 14.48/2.50      inference(superposition,[status(thm)],[c_5785,c_2431]) ).
% 14.48/2.50  
% 14.48/2.50  cnf(c_9150,plain,
% 14.48/2.50      ( k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X1) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
% 14.48/2.50      inference(demodulation,[status(thm)],[c_9107,c_12]) ).
% 14.48/2.50  
% 14.48/2.50  cnf(c_17,plain,
% 14.48/2.50      ( ~ v1_relat_1(X0) | k7_relat_1(X0,k1_relat_1(X0)) = X0 ),
% 14.48/2.50      inference(cnf_transformation,[],[f68]) ).
% 14.48/2.50  
% 14.48/2.50  cnf(c_621,plain,
% 14.48/2.50      ( k7_relat_1(X0,k1_relat_1(X0)) = X0 | v1_relat_1(X0) != iProver_top ),
% 14.48/2.50      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 14.48/2.50  
% 14.48/2.50  cnf(c_4375,plain,
% 14.48/2.50      ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k7_relat_1(k6_relat_1(X0),X1) ),
% 14.48/2.50      inference(superposition,[status(thm)],[c_4363,c_621]) ).
% 14.48/2.50  
% 14.48/2.50  cnf(c_4369,plain,
% 14.48/2.50      ( k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X1),X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X0) ),
% 14.48/2.50      inference(superposition,[status(thm)],[c_4363,c_622]) ).
% 14.48/2.50  
% 14.48/2.50  cnf(c_4372,plain,
% 14.48/2.50      ( k4_relat_1(k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X2))) = k5_relat_1(k6_relat_1(X2),k4_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
% 14.48/2.50      inference(superposition,[status(thm)],[c_4363,c_2361]) ).
% 14.48/2.50  
% 14.48/2.50  cnf(c_4374,plain,
% 14.48/2.50      ( k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X2)) = k8_relat_1(X2,k7_relat_1(k6_relat_1(X0),X1)) ),
% 14.48/2.50      inference(superposition,[status(thm)],[c_4363,c_631]) ).
% 14.48/2.50  
% 14.48/2.50  cnf(c_4379,plain,
% 14.48/2.50      ( k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X0),X1) ),
% 14.48/2.50      inference(demodulation,[status(thm)],[c_4374,c_1992]) ).
% 14.48/2.50  
% 14.48/2.50  cnf(c_4386,plain,
% 14.48/2.50      ( k5_relat_1(k6_relat_1(X0),k4_relat_1(k7_relat_1(k6_relat_1(X1),X2))) = k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)) ),
% 14.48/2.50      inference(light_normalisation,[status(thm)],[c_4372,c_4379]) ).
% 14.48/2.50  
% 14.48/2.50  cnf(c_4388,plain,
% 14.48/2.50      ( k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)) = k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X2),X1)) ),
% 14.48/2.50      inference(demodulation,[status(thm)],[c_4386,c_2431]) ).
% 14.48/2.50  
% 14.48/2.50  cnf(c_4395,plain,
% 14.48/2.50      ( k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X1),X0) ),
% 14.48/2.50      inference(demodulation,[status(thm)],[c_4369,c_4388]) ).
% 14.48/2.50  
% 14.48/2.50  cnf(c_5278,plain,
% 14.48/2.50      ( k7_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X1),X0) = k4_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
% 14.48/2.50      inference(superposition,[status(thm)],[c_4375,c_4395]) ).
% 14.48/2.50  
% 14.48/2.50  cnf(c_5280,plain,
% 14.48/2.50      ( k7_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X1),X0) = k7_relat_1(k6_relat_1(X1),X0) ),
% 14.48/2.50      inference(light_normalisation,[status(thm)],[c_5278,c_2431]) ).
% 14.48/2.50  
% 14.48/2.50  cnf(c_10461,plain,
% 14.48/2.50      ( k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X0) = k7_relat_1(k6_relat_1(X1),X0) ),
% 14.48/2.50      inference(demodulation,[status(thm)],[c_9150,c_5280]) ).
% 14.48/2.50  
% 14.48/2.50  cnf(c_11470,plain,
% 14.48/2.50      ( k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k4_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
% 14.48/2.50      inference(superposition,[status(thm)],[c_10461,c_2431]) ).
% 14.48/2.50  
% 14.48/2.50  cnf(c_11513,plain,
% 14.48/2.50      ( k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k7_relat_1(k6_relat_1(X0),X1) ),
% 14.48/2.50      inference(demodulation,[status(thm)],[c_11470,c_2431]) ).
% 14.48/2.50  
% 14.48/2.50  cnf(c_52217,plain,
% 14.48/2.50      ( k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k7_relat_1(k6_relat_1(X0),X1) ),
% 14.48/2.50      inference(light_normalisation,[status(thm)],[c_52215,c_11513]) ).
% 14.48/2.50  
% 14.48/2.50  cnf(c_53621,plain,
% 14.48/2.50      ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0) = k7_relat_1(k6_relat_1(X1),X0) ),
% 14.48/2.50      inference(demodulation,[status(thm)],[c_52217,c_10461]) ).
% 14.48/2.50  
% 14.48/2.50  cnf(c_1,plain,
% 14.48/2.50      ( ~ v1_relat_1(X0)
% 14.48/2.50      | k7_relat_1(X0,k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X2))) = k7_relat_1(k7_relat_1(X0,X1),X2) ),
% 14.48/2.50      inference(cnf_transformation,[],[f76]) ).
% 14.48/2.50  
% 14.48/2.50  cnf(c_633,plain,
% 14.48/2.50      ( k7_relat_1(X0,k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X2))) = k7_relat_1(k7_relat_1(X0,X1),X2)
% 14.48/2.50      | v1_relat_1(X0) != iProver_top ),
% 14.48/2.50      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 14.48/2.50  
% 14.48/2.50  cnf(c_4671,plain,
% 14.48/2.50      ( k7_relat_1(k6_relat_1(X0),k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X2))) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) ),
% 14.48/2.50      inference(superposition,[status(thm)],[c_620,c_633]) ).
% 14.48/2.50  
% 14.48/2.50  cnf(c_5661,plain,
% 14.48/2.50      ( k7_relat_1(k7_relat_1(k6_relat_1(k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))),X0),X1) = k6_relat_1(k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))) ),
% 14.48/2.50      inference(superposition,[status(thm)],[c_4671,c_222]) ).
% 14.48/2.50  
% 14.48/2.50  cnf(c_5674,plain,
% 14.48/2.50      ( k7_relat_1(k6_relat_1(k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))),X2) = k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X2),X0),X1)) ),
% 14.48/2.50      inference(superposition,[status(thm)],[c_4671,c_2431]) ).
% 14.48/2.50  
% 14.48/2.50  cnf(c_5706,plain,
% 14.48/2.50      ( k7_relat_1(k6_relat_1(k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))),X2) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X0),X2) ),
% 14.48/2.50      inference(demodulation,[status(thm)],[c_5674,c_4395]) ).
% 14.48/2.50  
% 14.48/2.50  cnf(c_5744,plain,
% 14.48/2.50      ( k6_relat_1(k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))) = k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X1),X0),X0),X1) ),
% 14.48/2.50      inference(demodulation,[status(thm)],[c_5661,c_5706]) ).
% 14.48/2.50  
% 14.48/2.50  cnf(c_5746,plain,
% 14.48/2.50      ( k6_relat_1(k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X0),X1) ),
% 14.48/2.50      inference(demodulation,[status(thm)],[c_5744,c_1996]) ).
% 14.48/2.50  
% 14.48/2.50  cnf(c_20,negated_conjecture,
% 14.48/2.50      ( k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))) ),
% 14.48/2.50      inference(cnf_transformation,[],[f77]) ).
% 14.48/2.50  
% 14.48/2.50  cnf(c_1454,plain,
% 14.48/2.50      ( k6_relat_1(k1_setfam_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))) != k7_relat_1(k6_relat_1(sK0),sK1) ),
% 14.48/2.50      inference(demodulation,[status(thm)],[c_896,c_20]) ).
% 14.48/2.50  
% 14.48/2.50  cnf(c_19618,plain,
% 14.48/2.50      ( k7_relat_1(k7_relat_1(k6_relat_1(sK1),sK0),sK1) != k7_relat_1(k6_relat_1(sK0),sK1) ),
% 14.48/2.50      inference(demodulation,[status(thm)],[c_5746,c_1454]) ).
% 14.48/2.50  
% 14.48/2.50  cnf(c_54803,plain,
% 14.48/2.50      ( k7_relat_1(k6_relat_1(sK0),sK1) != k7_relat_1(k6_relat_1(sK0),sK1) ),
% 14.48/2.50      inference(demodulation,[status(thm)],[c_53621,c_19618]) ).
% 14.48/2.50  
% 14.48/2.50  cnf(c_54810,plain,
% 14.48/2.50      ( $false ),
% 14.48/2.50      inference(equality_resolution_simp,[status(thm)],[c_54803]) ).
% 14.48/2.50  
% 14.48/2.50  
% 14.48/2.50  % SZS output end CNFRefutation for theBenchmark.p
% 14.48/2.50  
% 14.48/2.50  ------                               Statistics
% 14.48/2.50  
% 14.48/2.50  ------ General
% 14.48/2.50  
% 14.48/2.50  abstr_ref_over_cycles:                  0
% 14.48/2.50  abstr_ref_under_cycles:                 0
% 14.48/2.50  gc_basic_clause_elim:                   0
% 14.48/2.50  forced_gc_time:                         0
% 14.48/2.50  parsing_time:                           0.011
% 14.48/2.50  unif_index_cands_time:                  0.
% 14.48/2.50  unif_index_add_time:                    0.
% 14.48/2.50  orderings_time:                         0.
% 14.48/2.50  out_proof_time:                         0.015
% 14.48/2.50  total_time:                             1.608
% 14.48/2.50  num_of_symbols:                         45
% 14.48/2.50  num_of_terms:                           75480
% 14.48/2.50  
% 14.48/2.50  ------ Preprocessing
% 14.48/2.50  
% 14.48/2.50  num_of_splits:                          0
% 14.48/2.50  num_of_split_atoms:                     0
% 14.48/2.50  num_of_reused_defs:                     0
% 14.48/2.50  num_eq_ax_congr_red:                    4
% 14.48/2.50  num_of_sem_filtered_clauses:            1
% 14.48/2.50  num_of_subtypes:                        0
% 14.48/2.50  monotx_restored_types:                  0
% 14.48/2.50  sat_num_of_epr_types:                   0
% 14.48/2.50  sat_num_of_non_cyclic_types:            0
% 14.48/2.50  sat_guarded_non_collapsed_types:        0
% 14.48/2.50  num_pure_diseq_elim:                    0
% 14.48/2.50  simp_replaced_by:                       0
% 14.48/2.50  res_preprocessed:                       108
% 14.48/2.50  prep_upred:                             0
% 14.48/2.50  prep_unflattend:                        2
% 14.48/2.50  smt_new_axioms:                         0
% 14.48/2.50  pred_elim_cands:                        2
% 14.48/2.50  pred_elim:                              1
% 14.48/2.50  pred_elim_cl:                           1
% 14.48/2.50  pred_elim_cycles:                       3
% 14.48/2.50  merged_defs:                            0
% 14.48/2.50  merged_defs_ncl:                        0
% 14.48/2.50  bin_hyper_res:                          0
% 14.48/2.50  prep_cycles:                            4
% 14.48/2.50  pred_elim_time:                         0.
% 14.48/2.50  splitting_time:                         0.
% 14.48/2.50  sem_filter_time:                        0.
% 14.48/2.50  monotx_time:                            0.
% 14.48/2.50  subtype_inf_time:                       0.
% 14.48/2.50  
% 14.48/2.50  ------ Problem properties
% 14.48/2.50  
% 14.48/2.50  clauses:                                20
% 14.48/2.50  conjectures:                            1
% 14.48/2.50  epr:                                    0
% 14.48/2.50  horn:                                   20
% 14.48/2.50  ground:                                 1
% 14.48/2.50  unary:                                  6
% 14.48/2.50  binary:                                 8
% 14.48/2.50  lits:                                   42
% 14.48/2.50  lits_eq:                                13
% 14.48/2.50  fd_pure:                                0
% 14.48/2.50  fd_pseudo:                              0
% 14.48/2.50  fd_cond:                                0
% 14.48/2.50  fd_pseudo_cond:                         0
% 14.48/2.50  ac_symbols:                             0
% 14.48/2.50  
% 14.48/2.50  ------ Propositional Solver
% 14.48/2.50  
% 14.48/2.50  prop_solver_calls:                      31
% 14.48/2.50  prop_fast_solver_calls:                 877
% 14.48/2.50  smt_solver_calls:                       0
% 14.48/2.50  smt_fast_solver_calls:                  0
% 14.48/2.50  prop_num_of_clauses:                    19271
% 14.48/2.50  prop_preprocess_simplified:             25814
% 14.48/2.50  prop_fo_subsumed:                       10
% 14.48/2.50  prop_solver_time:                       0.
% 14.48/2.50  smt_solver_time:                        0.
% 14.48/2.50  smt_fast_solver_time:                   0.
% 14.48/2.50  prop_fast_solver_time:                  0.
% 14.48/2.50  prop_unsat_core_time:                   0.
% 14.48/2.50  
% 14.48/2.50  ------ QBF
% 14.48/2.50  
% 14.48/2.50  qbf_q_res:                              0
% 14.48/2.50  qbf_num_tautologies:                    0
% 14.48/2.50  qbf_prep_cycles:                        0
% 14.48/2.50  
% 14.48/2.50  ------ BMC1
% 14.48/2.50  
% 14.48/2.50  bmc1_current_bound:                     -1
% 14.48/2.50  bmc1_last_solved_bound:                 -1
% 14.48/2.50  bmc1_unsat_core_size:                   -1
% 14.48/2.50  bmc1_unsat_core_parents_size:           -1
% 14.48/2.50  bmc1_merge_next_fun:                    0
% 14.48/2.50  bmc1_unsat_core_clauses_time:           0.
% 14.48/2.50  
% 14.48/2.50  ------ Instantiation
% 14.48/2.50  
% 14.48/2.50  inst_num_of_clauses:                    4553
% 14.48/2.50  inst_num_in_passive:                    1391
% 14.48/2.50  inst_num_in_active:                     1182
% 14.48/2.50  inst_num_in_unprocessed:                1980
% 14.48/2.50  inst_num_of_loops:                      1380
% 14.48/2.50  inst_num_of_learning_restarts:          0
% 14.48/2.50  inst_num_moves_active_passive:          197
% 14.48/2.50  inst_lit_activity:                      0
% 14.48/2.50  inst_lit_activity_moves:                2
% 14.48/2.50  inst_num_tautologies:                   0
% 14.48/2.50  inst_num_prop_implied:                  0
% 14.48/2.50  inst_num_existing_simplified:           0
% 14.48/2.50  inst_num_eq_res_simplified:             0
% 14.48/2.50  inst_num_child_elim:                    0
% 14.48/2.50  inst_num_of_dismatching_blockings:      4638
% 14.48/2.50  inst_num_of_non_proper_insts:           3603
% 14.48/2.50  inst_num_of_duplicates:                 0
% 14.48/2.50  inst_inst_num_from_inst_to_res:         0
% 14.48/2.50  inst_dismatching_checking_time:         0.
% 14.48/2.50  
% 14.48/2.50  ------ Resolution
% 14.48/2.50  
% 14.48/2.50  res_num_of_clauses:                     0
% 14.48/2.50  res_num_in_passive:                     0
% 14.48/2.50  res_num_in_active:                      0
% 14.48/2.50  res_num_of_loops:                       112
% 14.48/2.50  res_forward_subset_subsumed:            317
% 14.48/2.50  res_backward_subset_subsumed:           4
% 14.48/2.50  res_forward_subsumed:                   0
% 14.48/2.50  res_backward_subsumed:                  0
% 14.48/2.50  res_forward_subsumption_resolution:     0
% 14.48/2.50  res_backward_subsumption_resolution:    0
% 14.48/2.50  res_clause_to_clause_subsumption:       14814
% 14.48/2.50  res_orphan_elimination:                 0
% 14.48/2.50  res_tautology_del:                      215
% 14.48/2.50  res_num_eq_res_simplified:              0
% 14.48/2.50  res_num_sel_changes:                    0
% 14.48/2.50  res_moves_from_active_to_pass:          0
% 14.48/2.50  
% 14.48/2.50  ------ Superposition
% 14.48/2.50  
% 14.48/2.50  sup_time_total:                         0.
% 14.48/2.50  sup_time_generating:                    0.
% 14.48/2.50  sup_time_sim_full:                      0.
% 14.48/2.50  sup_time_sim_immed:                     0.
% 14.48/2.50  
% 14.48/2.50  sup_num_of_clauses:                     2464
% 14.48/2.50  sup_num_in_active:                      198
% 14.48/2.50  sup_num_in_passive:                     2266
% 14.48/2.50  sup_num_of_loops:                       274
% 14.48/2.50  sup_fw_superposition:                   5581
% 14.48/2.50  sup_bw_superposition:                   3809
% 14.48/2.50  sup_immediate_simplified:               3509
% 14.48/2.50  sup_given_eliminated:                   1
% 14.48/2.50  comparisons_done:                       0
% 14.48/2.50  comparisons_avoided:                    0
% 14.48/2.50  
% 14.48/2.50  ------ Simplifications
% 14.48/2.50  
% 14.48/2.50  
% 14.48/2.50  sim_fw_subset_subsumed:                 45
% 14.48/2.50  sim_bw_subset_subsumed:                 38
% 14.48/2.50  sim_fw_subsumed:                        681
% 14.48/2.50  sim_bw_subsumed:                        10
% 14.48/2.50  sim_fw_subsumption_res:                 8
% 14.48/2.50  sim_bw_subsumption_res:                 0
% 14.48/2.50  sim_tautology_del:                      0
% 14.48/2.50  sim_eq_tautology_del:                   229
% 14.48/2.50  sim_eq_res_simp:                        0
% 14.48/2.50  sim_fw_demodulated:                     1962
% 14.48/2.50  sim_bw_demodulated:                     286
% 14.48/2.50  sim_light_normalised:                   1338
% 14.48/2.50  sim_joinable_taut:                      0
% 14.48/2.50  sim_joinable_simp:                      0
% 14.48/2.50  sim_ac_normalised:                      0
% 14.48/2.50  sim_smt_subsumption:                    0
% 14.48/2.50  
%------------------------------------------------------------------------------
