%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:50:07 EST 2020

% Result     : Theorem 7.88s
% Output     : CNFRefutation 7.88s
% Verified   : 
% Statistics : Number of formulae       :  226 (19225 expanded)
%              Number of clauses        :  155 (7515 expanded)
%              Number of leaves         :   21 (3990 expanded)
%              Depth                    :   49
%              Number of atoms          :  414 (30984 expanded)
%              Number of equality atoms :  292 (15888 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    5 (   2 average)
%              Maximal term depth       :    9 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f55,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f20,axiom,(
    ! [X0] :
      ( v5_relat_1(k6_relat_1(X0),X0)
      & v4_relat_1(k6_relat_1(X0),X0)
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( v4_relat_1(k6_relat_1(X0),X0)
      & v1_relat_1(k6_relat_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f20])).

fof(f66,plain,(
    ! [X0] : v4_relat_1(k6_relat_1(X0),X0) ),
    inference(cnf_transformation,[],[f23])).

fof(f65,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f5,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f1,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f4])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f45,f46])).

fof(f69,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f44,f68])).

fof(f70,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f43,f69])).

fof(f71,plain,(
    ! [X0,X1] : k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f47,f70])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f50,f71])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k3_xboole_0(k2_relat_1(X1),X0) = k2_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k2_relat_1(X1),X0) = k2_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k2_relat_1(X1),X0) = k2_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k4_enumset1(k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),X0)) = k2_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f51,f71])).

fof(f16,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k5_relat_1(X1,k6_relat_1(X0)) = k8_relat_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = k8_relat_1(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = k8_relat_1(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f17,axiom,(
    ! [X0] : k4_relat_1(k6_relat_1(X0)) = k6_relat_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0] : k4_relat_1(k6_relat_1(X0)) = k6_relat_1(X0) ),
    inference(cnf_transformation,[],[f17])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f25,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f59,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k8_relat_1(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f21,conjecture,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f21])).

fof(f40,plain,(
    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f22])).

fof(f41,plain,
    ( ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))
   => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f40,f41])).

fof(f67,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f42])).

fof(f74,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))) ),
    inference(definition_unfolding,[],[f67,f71])).

cnf(c_7,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_17,plain,
    ( v4_relat_1(k6_relat_1(X0),X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_206,plain,
    ( ~ v1_relat_1(X0)
    | X1 != X2
    | k7_relat_1(X0,X2) = X0
    | k6_relat_1(X1) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_17])).

cnf(c_207,plain,
    ( ~ v1_relat_1(k6_relat_1(X0))
    | k7_relat_1(k6_relat_1(X0),X0) = k6_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_206])).

cnf(c_18,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_211,plain,
    ( k7_relat_1(k6_relat_1(X0),X0) = k6_relat_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_207,c_18])).

cnf(c_573,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(X0,k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X2))) = k7_relat_1(k7_relat_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_584,plain,
    ( k7_relat_1(X0,k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X2))) = k7_relat_1(k7_relat_1(X0,X1),X2)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1313,plain,
    ( k7_relat_1(k6_relat_1(X0),k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X2))) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) ),
    inference(superposition,[status(thm)],[c_573,c_584])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | k1_setfam_1(k4_enumset1(k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X0),X1)) = k2_relat_1(k8_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_583,plain,
    ( k1_setfam_1(k4_enumset1(k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X0),X1)) = k2_relat_1(k8_relat_1(X1,X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1320,plain,
    ( k1_setfam_1(k4_enumset1(k2_relat_1(k6_relat_1(X0)),k2_relat_1(k6_relat_1(X0)),k2_relat_1(k6_relat_1(X0)),k2_relat_1(k6_relat_1(X0)),k2_relat_1(k6_relat_1(X0)),X1)) = k2_relat_1(k8_relat_1(X1,k6_relat_1(X0))) ),
    inference(superposition,[status(thm)],[c_573,c_583])).

cnf(c_11,plain,
    ( k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1321,plain,
    ( k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)) = k2_relat_1(k8_relat_1(X1,k6_relat_1(X0))) ),
    inference(light_normalisation,[status(thm)],[c_1320,c_11])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X1,X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_582,plain,
    ( k5_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X1,X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_876,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k8_relat_1(X1,k6_relat_1(X0)) ),
    inference(superposition,[status(thm)],[c_573,c_582])).

cnf(c_16,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_574,plain,
    ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_774,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(superposition,[status(thm)],[c_573,c_574])).

cnf(c_877,plain,
    ( k8_relat_1(X0,k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(light_normalisation,[status(thm)],[c_876,c_774])).

cnf(c_1322,plain,
    ( k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)) = k2_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
    inference(demodulation,[status(thm)],[c_1321,c_877])).

cnf(c_1492,plain,
    ( k7_relat_1(k6_relat_1(X0),k2_relat_1(k7_relat_1(k6_relat_1(X1),X2))) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X2),X1) ),
    inference(demodulation,[status(thm)],[c_1313,c_1322])).

cnf(c_10,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k5_relat_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k5_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_577,plain,
    ( k5_relat_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k5_relat_1(X1,X0))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1175,plain,
    ( k5_relat_1(k4_relat_1(k6_relat_1(X0)),k4_relat_1(X1)) = k4_relat_1(k5_relat_1(X1,k6_relat_1(X0)))
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_573,c_577])).

cnf(c_13,plain,
    ( k4_relat_1(k6_relat_1(X0)) = k6_relat_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1176,plain,
    ( k4_relat_1(k5_relat_1(X0,k6_relat_1(X1))) = k5_relat_1(k6_relat_1(X1),k4_relat_1(X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1175,c_13])).

cnf(c_1219,plain,
    ( k4_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k5_relat_1(k6_relat_1(X1),k4_relat_1(k6_relat_1(X0))) ),
    inference(superposition,[status(thm)],[c_573,c_1176])).

cnf(c_1220,plain,
    ( k4_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) ),
    inference(light_normalisation,[status(thm)],[c_1219,c_13,c_774])).

cnf(c_1221,plain,
    ( k4_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(demodulation,[status(thm)],[c_1220,c_774])).

cnf(c_1498,plain,
    ( k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X2) = k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X2),X1),X0)) ),
    inference(superposition,[status(thm)],[c_1492,c_1221])).

cnf(c_0,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | v1_relat_1(k5_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_586,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k5_relat_1(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_981,plain,
    ( v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_774,c_586])).

cnf(c_20,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3396,plain,
    ( v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_981,c_20])).

cnf(c_3720,plain,
    ( v1_relat_1(k6_relat_1(X0)) != iProver_top
    | v1_relat_1(k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1498,c_3396])).

cnf(c_7409,plain,
    ( v1_relat_1(k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3720,c_20])).

cnf(c_7418,plain,
    ( v1_relat_1(k4_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_211,c_7409])).

cnf(c_7465,plain,
    ( v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7418,c_1221])).

cnf(c_1497,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X1),X0) = k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
    inference(superposition,[status(thm)],[c_1492,c_211])).

cnf(c_1506,plain,
    ( k7_relat_1(k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X0),X1)),X1) = k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X1),X0))) ),
    inference(demodulation,[status(thm)],[c_1497,c_1498])).

cnf(c_1507,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0) = k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
    inference(light_normalisation,[status(thm)],[c_1506,c_211,c_1221])).

cnf(c_7536,plain,
    ( k4_relat_1(k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X2))) = k5_relat_1(k6_relat_1(X2),k4_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
    inference(superposition,[status(thm)],[c_7465,c_1176])).

cnf(c_932,plain,
    ( k5_relat_1(k5_relat_1(X0,X1),k6_relat_1(X2)) = k8_relat_1(X2,k5_relat_1(X0,X1))
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_586,c_582])).

cnf(c_2648,plain,
    ( k5_relat_1(k5_relat_1(k6_relat_1(X0),X1),k6_relat_1(X2)) = k8_relat_1(X2,k5_relat_1(k6_relat_1(X0),X1))
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_573,c_932])).

cnf(c_2883,plain,
    ( k5_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),k6_relat_1(X2)) = k8_relat_1(X2,k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) ),
    inference(superposition,[status(thm)],[c_573,c_2648])).

cnf(c_2884,plain,
    ( k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X2)) = k8_relat_1(X2,k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(light_normalisation,[status(thm)],[c_2883,c_774])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | k8_relat_1(X1,k7_relat_1(X0,X2)) = k7_relat_1(k8_relat_1(X1,X0),X2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_580,plain,
    ( k8_relat_1(X0,k7_relat_1(X1,X2)) = k7_relat_1(k8_relat_1(X0,X1),X2)
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_880,plain,
    ( k8_relat_1(X0,k7_relat_1(k6_relat_1(X1),X2)) = k7_relat_1(k8_relat_1(X0,k6_relat_1(X1)),X2) ),
    inference(superposition,[status(thm)],[c_573,c_580])).

cnf(c_881,plain,
    ( k8_relat_1(X0,k7_relat_1(k6_relat_1(X1),X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) ),
    inference(light_normalisation,[status(thm)],[c_880,c_877])).

cnf(c_2885,plain,
    ( k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X0),X1) ),
    inference(demodulation,[status(thm)],[c_2884,c_881])).

cnf(c_7547,plain,
    ( k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)) = k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X2),X1)) ),
    inference(light_normalisation,[status(thm)],[c_7536,c_1221,c_2885])).

cnf(c_931,plain,
    ( k5_relat_1(k6_relat_1(X0),k5_relat_1(X1,X2)) = k7_relat_1(k5_relat_1(X1,X2),X0)
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_586,c_574])).

cnf(c_2106,plain,
    ( k5_relat_1(k6_relat_1(X0),k5_relat_1(k6_relat_1(X1),X2)) = k7_relat_1(k5_relat_1(k6_relat_1(X1),X2),X0)
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_573,c_931])).

cnf(c_2875,plain,
    ( k5_relat_1(k6_relat_1(X0),k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) = k7_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)),X0) ),
    inference(superposition,[status(thm)],[c_573,c_2106])).

cnf(c_2876,plain,
    ( k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X1),X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X0) ),
    inference(demodulation,[status(thm)],[c_2875,c_774])).

cnf(c_7548,plain,
    ( k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X1),X0) ),
    inference(demodulation,[status(thm)],[c_7547,c_2876])).

cnf(c_14,plain,
    ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_576,plain,
    ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_983,plain,
    ( r1_tarski(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X0)) = iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_774,c_576])).

cnf(c_1166,plain,
    ( r1_tarski(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_983,c_20])).

cnf(c_1499,plain,
    ( r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2),k6_relat_1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1492,c_1166])).

cnf(c_1610,plain,
    ( r1_tarski(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))),k6_relat_1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1507,c_1499])).

cnf(c_12,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_578,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1672,plain,
    ( r1_tarski(X0,k1_relat_1(X1)) = iProver_top
    | r1_tarski(k6_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_12,c_578])).

cnf(c_1723,plain,
    ( v1_relat_1(X1) != iProver_top
    | r1_tarski(k6_relat_1(X0),X1) != iProver_top
    | r1_tarski(X0,k1_relat_1(X1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1672,c_20])).

cnf(c_1724,plain,
    ( r1_tarski(X0,k1_relat_1(X1)) = iProver_top
    | r1_tarski(k6_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_1723])).

cnf(c_1730,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)),k1_relat_1(k6_relat_1(X0))) = iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1610,c_1724])).

cnf(c_1731,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X0) = iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1730,c_12])).

cnf(c_2193,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1731,c_20])).

cnf(c_3736,plain,
    ( r1_tarski(k2_relat_1(k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2))),k2_relat_1(k7_relat_1(k6_relat_1(X2),X1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1498,c_2193])).

cnf(c_5,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k8_relat_1(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_581,plain,
    ( k8_relat_1(X0,X1) = X1
    | r1_tarski(k2_relat_1(X1),X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1227,plain,
    ( k8_relat_1(X0,k6_relat_1(X1)) = k6_relat_1(X1)
    | r1_tarski(X1,X0) != iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11,c_581])).

cnf(c_1228,plain,
    ( k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X1)
    | r1_tarski(X1,X0) != iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1227,c_877])).

cnf(c_4726,plain,
    ( k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))),k2_relat_1(k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X2),X1),X0)))) = k6_relat_1(k2_relat_1(k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X2),X1),X0))))
    | v1_relat_1(k6_relat_1(k2_relat_1(k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X2),X1),X0))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3736,c_1228])).

cnf(c_3717,plain,
    ( k7_relat_1(k6_relat_1(k2_relat_1(k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)))),X3) = k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X3),X0),k2_relat_1(k7_relat_1(k6_relat_1(X2),X1)))) ),
    inference(superposition,[status(thm)],[c_1498,c_1498])).

cnf(c_1503,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),k2_relat_1(k7_relat_1(k6_relat_1(X2),X3))) = k8_relat_1(X0,k7_relat_1(k7_relat_1(k6_relat_1(X1),X3),X2)) ),
    inference(superposition,[status(thm)],[c_1492,c_881])).

cnf(c_3772,plain,
    ( k7_relat_1(k6_relat_1(k2_relat_1(k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)))),X3) = k4_relat_1(k8_relat_1(X3,k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2))) ),
    inference(demodulation,[status(thm)],[c_3717,c_1503])).

cnf(c_4727,plain,
    ( k4_relat_1(k7_relat_1(k4_relat_1(k8_relat_1(X0,k7_relat_1(k7_relat_1(k6_relat_1(X1),X0),X2))),X2)) = k6_relat_1(k2_relat_1(k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X1),X0),X2))))
    | v1_relat_1(k6_relat_1(k2_relat_1(k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X1),X0),X2))))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4726,c_1498,c_3772])).

cnf(c_930,plain,
    ( k8_relat_1(X0,k7_relat_1(k5_relat_1(X1,X2),X3)) = k7_relat_1(k8_relat_1(X0,k5_relat_1(X1,X2)),X3)
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_586,c_580])).

cnf(c_1664,plain,
    ( k8_relat_1(X0,k7_relat_1(k5_relat_1(k6_relat_1(X1),X2),X3)) = k7_relat_1(k8_relat_1(X0,k5_relat_1(k6_relat_1(X1),X2)),X3)
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_573,c_930])).

cnf(c_4322,plain,
    ( k8_relat_1(X0,k7_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)),X3)) = k7_relat_1(k8_relat_1(X0,k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))),X3) ),
    inference(superposition,[status(thm)],[c_573,c_1664])).

cnf(c_4325,plain,
    ( k8_relat_1(X0,k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X3)) = k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2),X3) ),
    inference(demodulation,[status(thm)],[c_4322,c_774,c_881])).

cnf(c_4728,plain,
    ( k4_relat_1(k7_relat_1(k4_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0),X2)),X2)) = k6_relat_1(k2_relat_1(k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X1),X0),X2))))
    | v1_relat_1(k6_relat_1(k2_relat_1(k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X1),X0),X2))))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4727,c_4325])).

cnf(c_4729,plain,
    ( k4_relat_1(k7_relat_1(k4_relat_1(k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2))),X0)) = k6_relat_1(k2_relat_1(k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X0))))
    | v1_relat_1(k6_relat_1(k2_relat_1(k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X0))))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4728,c_1498,c_1507])).

cnf(c_1609,plain,
    ( k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),k2_relat_1(k7_relat_1(k6_relat_1(X1),X2))))) = k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X2),X1),X0) ),
    inference(superposition,[status(thm)],[c_1492,c_1507])).

cnf(c_1613,plain,
    ( k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2),X0) = k6_relat_1(k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2))) ),
    inference(light_normalisation,[status(thm)],[c_1609,c_1492])).

cnf(c_3746,plain,
    ( k7_relat_1(k6_relat_1(X0),k2_relat_1(k7_relat_1(k6_relat_1(X1),X2))) = k4_relat_1(k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X2),X1))) ),
    inference(superposition,[status(thm)],[c_1498,c_1221])).

cnf(c_3759,plain,
    ( k4_relat_1(k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2))) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) ),
    inference(light_normalisation,[status(thm)],[c_3746,c_1492])).

cnf(c_4730,plain,
    ( k6_relat_1(k2_relat_1(k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)))) = k6_relat_1(k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X2),X0),X1)))
    | v1_relat_1(k6_relat_1(k2_relat_1(k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2))))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4729,c_13,c_1613,c_3759])).

cnf(c_5178,plain,
    ( k6_relat_1(k2_relat_1(k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)))) = k6_relat_1(k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X2),X0),X1))) ),
    inference(superposition,[status(thm)],[c_573,c_4730])).

cnf(c_5421,plain,
    ( k2_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)))) = k2_relat_1(k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X0))) ),
    inference(superposition,[status(thm)],[c_5178,c_11])).

cnf(c_5469,plain,
    ( k2_relat_1(k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2))) = k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X2),X0),X1)) ),
    inference(demodulation,[status(thm)],[c_5421,c_11])).

cnf(c_5481,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)),k2_relat_1(k7_relat_1(k6_relat_1(X0),X2))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5469,c_3736])).

cnf(c_5854,plain,
    ( k8_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)),k7_relat_1(k7_relat_1(k6_relat_1(X0),X2),X1)) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X2),X1)
    | v1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X2),X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5481,c_581])).

cnf(c_5859,plain,
    ( k7_relat_1(k7_relat_1(k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0)),X2),X1) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X2),X1)
    | v1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X2),X1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5854,c_1498,c_4325])).

cnf(c_5860,plain,
    ( k7_relat_1(k7_relat_1(k4_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)))),X2),X1) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X2),X1)
    | v1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X2),X1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5859,c_1507])).

cnf(c_5861,plain,
    ( k7_relat_1(k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)),X1) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X0),X1)
    | v1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X2),X0),X1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5860,c_13,c_1498])).

cnf(c_15,plain,
    ( r1_tarski(k5_relat_1(X0,k6_relat_1(X1)),X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_575,plain,
    ( r1_tarski(k5_relat_1(X0,k6_relat_1(X1)),X0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_982,plain,
    ( r1_tarski(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X1)) = iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_774,c_575])).

cnf(c_1097,plain,
    ( r1_tarski(k6_relat_1(X0),k6_relat_1(X0)) = iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_211,c_982])).

cnf(c_1102,plain,
    ( r1_tarski(k6_relat_1(X0),k6_relat_1(X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1097,c_20])).

cnf(c_1729,plain,
    ( r1_tarski(X0,k1_relat_1(k6_relat_1(X0))) = iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1102,c_1724])).

cnf(c_1732,plain,
    ( r1_tarski(X0,X0) = iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1729,c_12])).

cnf(c_1764,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1732,c_20])).

cnf(c_1770,plain,
    ( k8_relat_1(k2_relat_1(X0),X0) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1764,c_581])).

cnf(c_1776,plain,
    ( k8_relat_1(k2_relat_1(k5_relat_1(X0,X1)),k5_relat_1(X0,X1)) = k5_relat_1(X0,X1)
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_586,c_1770])).

cnf(c_4336,plain,
    ( k8_relat_1(k2_relat_1(k5_relat_1(k6_relat_1(X0),X1)),k5_relat_1(k6_relat_1(X0),X1)) = k5_relat_1(k6_relat_1(X0),X1)
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_573,c_1776])).

cnf(c_4505,plain,
    ( k8_relat_1(k2_relat_1(k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X1),X2))),k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X1),X2))) = k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X1),X2))
    | v1_relat_1(k6_relat_1(X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3396,c_4336])).

cnf(c_4506,plain,
    ( k8_relat_1(k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)),k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4505,c_2876])).

cnf(c_3714,plain,
    ( k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),k2_relat_1(k7_relat_1(k6_relat_1(X1),X2))),X3)) = k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X3),X2),X1))),X0) ),
    inference(superposition,[status(thm)],[c_1492,c_1498])).

cnf(c_3775,plain,
    ( k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2))),X3) = k4_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X3),X1),X2),X0)) ),
    inference(light_normalisation,[status(thm)],[c_3714,c_1492])).

cnf(c_4507,plain,
    ( k7_relat_1(k7_relat_1(k4_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2),X0)),X1),X2) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4506,c_3775,c_4325])).

cnf(c_4508,plain,
    ( k7_relat_1(k7_relat_1(k4_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)))),X1),X2) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4507,c_1613])).

cnf(c_4509,plain,
    ( k7_relat_1(k4_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X0),X1),X2)),X1) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X0),X1)
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4508,c_13,c_3775])).

cnf(c_4510,plain,
    ( k7_relat_1(k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)),X1) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X0),X1)
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4509,c_211])).

cnf(c_6773,plain,
    ( k7_relat_1(k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)),X1) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X0),X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5861,c_20,c_4510])).

cnf(c_8597,plain,
    ( k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2),X1) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X2),X1) ),
    inference(demodulation,[status(thm)],[c_7548,c_6773])).

cnf(c_8834,plain,
    ( k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X1) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X0),X1) ),
    inference(superposition,[status(thm)],[c_1507,c_8597])).

cnf(c_8867,plain,
    ( k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X1) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(light_normalisation,[status(thm)],[c_8834,c_211])).

cnf(c_9416,plain,
    ( k7_relat_1(k6_relat_1(X0),k2_relat_1(k7_relat_1(k6_relat_1(X1),X0))) = k4_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
    inference(superposition,[status(thm)],[c_8867,c_1221])).

cnf(c_9457,plain,
    ( k7_relat_1(k6_relat_1(X0),k2_relat_1(k7_relat_1(k6_relat_1(X1),X0))) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(demodulation,[status(thm)],[c_9416,c_1221,c_1492])).

cnf(c_1048,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X1) = k8_relat_1(X0,k6_relat_1(X1)) ),
    inference(superposition,[status(thm)],[c_211,c_881])).

cnf(c_1049,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X1) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(light_normalisation,[status(thm)],[c_1048,c_877])).

cnf(c_9684,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),k2_relat_1(k7_relat_1(k6_relat_1(X1),X0))) = k7_relat_1(k6_relat_1(X0),k2_relat_1(k7_relat_1(k6_relat_1(X1),X0))) ),
    inference(superposition,[status(thm)],[c_9457,c_1049])).

cnf(c_9730,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),k2_relat_1(k7_relat_1(k6_relat_1(X1),X0))) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(demodulation,[status(thm)],[c_9684,c_9457])).

cnf(c_3748,plain,
    ( r1_tarski(k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)),k6_relat_1(X0)) = iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1498,c_982])).

cnf(c_21218,plain,
    ( r1_tarski(k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)),k6_relat_1(X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3748,c_20])).

cnf(c_21222,plain,
    ( r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2),k6_relat_1(X2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_21218,c_7548])).

cnf(c_21230,plain,
    ( r1_tarski(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X1),X0)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_9730,c_21222])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_579,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1712,plain,
    ( k8_relat_1(k2_relat_1(X0),X1) = X1
    | r1_tarski(X1,X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_579,c_581])).

cnf(c_22224,plain,
    ( k8_relat_1(k2_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)))),k7_relat_1(k6_relat_1(X1),X0)) = k7_relat_1(k6_relat_1(X1),X0)
    | v1_relat_1(k7_relat_1(k6_relat_1(X1),X0)) != iProver_top
    | v1_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_21230,c_1712])).

cnf(c_22257,plain,
    ( k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k7_relat_1(k6_relat_1(X1),X0)
    | v1_relat_1(k7_relat_1(k6_relat_1(X1),X0)) != iProver_top
    | v1_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_22224,c_11,c_881,c_1507,c_8867])).

cnf(c_21232,plain,
    ( r1_tarski(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_211,c_21222])).

cnf(c_22180,plain,
    ( k8_relat_1(k2_relat_1(k6_relat_1(X0)),k7_relat_1(k6_relat_1(X1),X0)) = k7_relat_1(k6_relat_1(X1),X0)
    | v1_relat_1(k7_relat_1(k6_relat_1(X1),X0)) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_21232,c_1712])).

cnf(c_22305,plain,
    ( k8_relat_1(X0,k7_relat_1(k6_relat_1(X1),X0)) = k7_relat_1(k6_relat_1(X1),X0)
    | v1_relat_1(k7_relat_1(k6_relat_1(X1),X0)) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_22180,c_11])).

cnf(c_22306,plain,
    ( k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k7_relat_1(k6_relat_1(X1),X0)
    | v1_relat_1(k7_relat_1(k6_relat_1(X1),X0)) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_22305,c_881,c_1507])).

cnf(c_23272,plain,
    ( v1_relat_1(k7_relat_1(k6_relat_1(X1),X0)) != iProver_top
    | k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_22257,c_20,c_22306])).

cnf(c_23273,plain,
    ( k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k7_relat_1(k6_relat_1(X1),X0)
    | v1_relat_1(k7_relat_1(k6_relat_1(X1),X0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_23272])).

cnf(c_23278,plain,
    ( k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(superposition,[status(thm)],[c_7465,c_23273])).

cnf(c_19,negated_conjecture,
    ( k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_980,plain,
    ( k6_relat_1(k1_setfam_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))) != k7_relat_1(k6_relat_1(sK0),sK1) ),
    inference(demodulation,[status(thm)],[c_774,c_19])).

cnf(c_1372,plain,
    ( k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(sK1),sK0))) != k7_relat_1(k6_relat_1(sK0),sK1) ),
    inference(demodulation,[status(thm)],[c_1322,c_980])).

cnf(c_23547,plain,
    ( k7_relat_1(k6_relat_1(sK0),sK1) != k7_relat_1(k6_relat_1(sK0),sK1) ),
    inference(demodulation,[status(thm)],[c_23278,c_1372])).

cnf(c_23579,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_23547])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 09:33:37 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running in FOF mode
% 7.88/1.47  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.88/1.47  
% 7.88/1.47  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.88/1.47  
% 7.88/1.47  ------  iProver source info
% 7.88/1.47  
% 7.88/1.47  git: date: 2020-06-30 10:37:57 +0100
% 7.88/1.47  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.88/1.47  git: non_committed_changes: false
% 7.88/1.47  git: last_make_outside_of_git: false
% 7.88/1.47  
% 7.88/1.47  ------ 
% 7.88/1.47  
% 7.88/1.47  ------ Input Options
% 7.88/1.47  
% 7.88/1.47  --out_options                           all
% 7.88/1.47  --tptp_safe_out                         true
% 7.88/1.47  --problem_path                          ""
% 7.88/1.47  --include_path                          ""
% 7.88/1.47  --clausifier                            res/vclausify_rel
% 7.88/1.47  --clausifier_options                    ""
% 7.88/1.47  --stdin                                 false
% 7.88/1.47  --stats_out                             all
% 7.88/1.47  
% 7.88/1.47  ------ General Options
% 7.88/1.47  
% 7.88/1.47  --fof                                   false
% 7.88/1.47  --time_out_real                         305.
% 7.88/1.47  --time_out_virtual                      -1.
% 7.88/1.47  --symbol_type_check                     false
% 7.88/1.47  --clausify_out                          false
% 7.88/1.47  --sig_cnt_out                           false
% 7.88/1.47  --trig_cnt_out                          false
% 7.88/1.47  --trig_cnt_out_tolerance                1.
% 7.88/1.47  --trig_cnt_out_sk_spl                   false
% 7.88/1.47  --abstr_cl_out                          false
% 7.88/1.47  
% 7.88/1.47  ------ Global Options
% 7.88/1.47  
% 7.88/1.47  --schedule                              default
% 7.88/1.47  --add_important_lit                     false
% 7.88/1.47  --prop_solver_per_cl                    1000
% 7.88/1.47  --min_unsat_core                        false
% 7.88/1.47  --soft_assumptions                      false
% 7.88/1.47  --soft_lemma_size                       3
% 7.88/1.47  --prop_impl_unit_size                   0
% 7.88/1.47  --prop_impl_unit                        []
% 7.88/1.47  --share_sel_clauses                     true
% 7.88/1.47  --reset_solvers                         false
% 7.88/1.47  --bc_imp_inh                            [conj_cone]
% 7.88/1.47  --conj_cone_tolerance                   3.
% 7.88/1.47  --extra_neg_conj                        none
% 7.88/1.47  --large_theory_mode                     true
% 7.88/1.47  --prolific_symb_bound                   200
% 7.88/1.47  --lt_threshold                          2000
% 7.88/1.47  --clause_weak_htbl                      true
% 7.88/1.47  --gc_record_bc_elim                     false
% 7.88/1.47  
% 7.88/1.47  ------ Preprocessing Options
% 7.88/1.47  
% 7.88/1.47  --preprocessing_flag                    true
% 7.88/1.47  --time_out_prep_mult                    0.1
% 7.88/1.47  --splitting_mode                        input
% 7.88/1.47  --splitting_grd                         true
% 7.88/1.47  --splitting_cvd                         false
% 7.88/1.47  --splitting_cvd_svl                     false
% 7.88/1.47  --splitting_nvd                         32
% 7.88/1.47  --sub_typing                            true
% 7.88/1.47  --prep_gs_sim                           true
% 7.88/1.47  --prep_unflatten                        true
% 7.88/1.47  --prep_res_sim                          true
% 7.88/1.47  --prep_upred                            true
% 7.88/1.47  --prep_sem_filter                       exhaustive
% 7.88/1.47  --prep_sem_filter_out                   false
% 7.88/1.47  --pred_elim                             true
% 7.88/1.47  --res_sim_input                         true
% 7.88/1.47  --eq_ax_congr_red                       true
% 7.88/1.47  --pure_diseq_elim                       true
% 7.88/1.47  --brand_transform                       false
% 7.88/1.47  --non_eq_to_eq                          false
% 7.88/1.47  --prep_def_merge                        true
% 7.88/1.47  --prep_def_merge_prop_impl              false
% 7.88/1.47  --prep_def_merge_mbd                    true
% 7.88/1.47  --prep_def_merge_tr_red                 false
% 7.88/1.47  --prep_def_merge_tr_cl                  false
% 7.88/1.47  --smt_preprocessing                     true
% 7.88/1.47  --smt_ac_axioms                         fast
% 7.88/1.47  --preprocessed_out                      false
% 7.88/1.47  --preprocessed_stats                    false
% 7.88/1.47  
% 7.88/1.47  ------ Abstraction refinement Options
% 7.88/1.47  
% 7.88/1.47  --abstr_ref                             []
% 7.88/1.47  --abstr_ref_prep                        false
% 7.88/1.47  --abstr_ref_until_sat                   false
% 7.88/1.47  --abstr_ref_sig_restrict                funpre
% 7.88/1.47  --abstr_ref_af_restrict_to_split_sk     false
% 7.88/1.47  --abstr_ref_under                       []
% 7.88/1.47  
% 7.88/1.47  ------ SAT Options
% 7.88/1.47  
% 7.88/1.47  --sat_mode                              false
% 7.88/1.47  --sat_fm_restart_options                ""
% 7.88/1.47  --sat_gr_def                            false
% 7.88/1.47  --sat_epr_types                         true
% 7.88/1.47  --sat_non_cyclic_types                  false
% 7.88/1.47  --sat_finite_models                     false
% 7.88/1.47  --sat_fm_lemmas                         false
% 7.88/1.47  --sat_fm_prep                           false
% 7.88/1.47  --sat_fm_uc_incr                        true
% 7.88/1.47  --sat_out_model                         small
% 7.88/1.47  --sat_out_clauses                       false
% 7.88/1.47  
% 7.88/1.47  ------ QBF Options
% 7.88/1.47  
% 7.88/1.47  --qbf_mode                              false
% 7.88/1.47  --qbf_elim_univ                         false
% 7.88/1.47  --qbf_dom_inst                          none
% 7.88/1.47  --qbf_dom_pre_inst                      false
% 7.88/1.47  --qbf_sk_in                             false
% 7.88/1.47  --qbf_pred_elim                         true
% 7.88/1.47  --qbf_split                             512
% 7.88/1.47  
% 7.88/1.47  ------ BMC1 Options
% 7.88/1.47  
% 7.88/1.47  --bmc1_incremental                      false
% 7.88/1.47  --bmc1_axioms                           reachable_all
% 7.88/1.47  --bmc1_min_bound                        0
% 7.88/1.47  --bmc1_max_bound                        -1
% 7.88/1.47  --bmc1_max_bound_default                -1
% 7.88/1.47  --bmc1_symbol_reachability              true
% 7.88/1.47  --bmc1_property_lemmas                  false
% 7.88/1.47  --bmc1_k_induction                      false
% 7.88/1.47  --bmc1_non_equiv_states                 false
% 7.88/1.47  --bmc1_deadlock                         false
% 7.88/1.47  --bmc1_ucm                              false
% 7.88/1.47  --bmc1_add_unsat_core                   none
% 7.88/1.47  --bmc1_unsat_core_children              false
% 7.88/1.47  --bmc1_unsat_core_extrapolate_axioms    false
% 7.88/1.47  --bmc1_out_stat                         full
% 7.88/1.47  --bmc1_ground_init                      false
% 7.88/1.47  --bmc1_pre_inst_next_state              false
% 7.88/1.47  --bmc1_pre_inst_state                   false
% 7.88/1.47  --bmc1_pre_inst_reach_state             false
% 7.88/1.47  --bmc1_out_unsat_core                   false
% 7.88/1.47  --bmc1_aig_witness_out                  false
% 7.88/1.47  --bmc1_verbose                          false
% 7.88/1.47  --bmc1_dump_clauses_tptp                false
% 7.88/1.47  --bmc1_dump_unsat_core_tptp             false
% 7.88/1.47  --bmc1_dump_file                        -
% 7.88/1.47  --bmc1_ucm_expand_uc_limit              128
% 7.88/1.47  --bmc1_ucm_n_expand_iterations          6
% 7.88/1.47  --bmc1_ucm_extend_mode                  1
% 7.88/1.47  --bmc1_ucm_init_mode                    2
% 7.88/1.47  --bmc1_ucm_cone_mode                    none
% 7.88/1.47  --bmc1_ucm_reduced_relation_type        0
% 7.88/1.47  --bmc1_ucm_relax_model                  4
% 7.88/1.47  --bmc1_ucm_full_tr_after_sat            true
% 7.88/1.47  --bmc1_ucm_expand_neg_assumptions       false
% 7.88/1.47  --bmc1_ucm_layered_model                none
% 7.88/1.47  --bmc1_ucm_max_lemma_size               10
% 7.88/1.47  
% 7.88/1.47  ------ AIG Options
% 7.88/1.47  
% 7.88/1.47  --aig_mode                              false
% 7.88/1.47  
% 7.88/1.47  ------ Instantiation Options
% 7.88/1.47  
% 7.88/1.47  --instantiation_flag                    true
% 7.88/1.47  --inst_sos_flag                         true
% 7.88/1.47  --inst_sos_phase                        true
% 7.88/1.47  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.88/1.47  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.88/1.47  --inst_lit_sel_side                     num_symb
% 7.88/1.47  --inst_solver_per_active                1400
% 7.88/1.47  --inst_solver_calls_frac                1.
% 7.88/1.47  --inst_passive_queue_type               priority_queues
% 7.88/1.47  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.88/1.47  --inst_passive_queues_freq              [25;2]
% 7.88/1.47  --inst_dismatching                      true
% 7.88/1.47  --inst_eager_unprocessed_to_passive     true
% 7.88/1.47  --inst_prop_sim_given                   true
% 7.88/1.47  --inst_prop_sim_new                     false
% 7.88/1.47  --inst_subs_new                         false
% 7.88/1.47  --inst_eq_res_simp                      false
% 7.88/1.47  --inst_subs_given                       false
% 7.88/1.47  --inst_orphan_elimination               true
% 7.88/1.47  --inst_learning_loop_flag               true
% 7.88/1.47  --inst_learning_start                   3000
% 7.88/1.47  --inst_learning_factor                  2
% 7.88/1.47  --inst_start_prop_sim_after_learn       3
% 7.88/1.47  --inst_sel_renew                        solver
% 7.88/1.47  --inst_lit_activity_flag                true
% 7.88/1.47  --inst_restr_to_given                   false
% 7.88/1.47  --inst_activity_threshold               500
% 7.88/1.47  --inst_out_proof                        true
% 7.88/1.47  
% 7.88/1.47  ------ Resolution Options
% 7.88/1.47  
% 7.88/1.47  --resolution_flag                       true
% 7.88/1.47  --res_lit_sel                           adaptive
% 7.88/1.47  --res_lit_sel_side                      none
% 7.88/1.47  --res_ordering                          kbo
% 7.88/1.47  --res_to_prop_solver                    active
% 7.88/1.47  --res_prop_simpl_new                    false
% 7.88/1.47  --res_prop_simpl_given                  true
% 7.88/1.47  --res_passive_queue_type                priority_queues
% 7.88/1.47  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.88/1.47  --res_passive_queues_freq               [15;5]
% 7.88/1.47  --res_forward_subs                      full
% 7.88/1.47  --res_backward_subs                     full
% 7.88/1.47  --res_forward_subs_resolution           true
% 7.88/1.47  --res_backward_subs_resolution          true
% 7.88/1.47  --res_orphan_elimination                true
% 7.88/1.47  --res_time_limit                        2.
% 7.88/1.47  --res_out_proof                         true
% 7.88/1.47  
% 7.88/1.47  ------ Superposition Options
% 7.88/1.47  
% 7.88/1.47  --superposition_flag                    true
% 7.88/1.47  --sup_passive_queue_type                priority_queues
% 7.88/1.47  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.88/1.47  --sup_passive_queues_freq               [8;1;4]
% 7.88/1.47  --demod_completeness_check              fast
% 7.88/1.47  --demod_use_ground                      true
% 7.88/1.47  --sup_to_prop_solver                    passive
% 7.88/1.47  --sup_prop_simpl_new                    true
% 7.88/1.47  --sup_prop_simpl_given                  true
% 7.88/1.47  --sup_fun_splitting                     true
% 7.88/1.47  --sup_smt_interval                      50000
% 7.88/1.47  
% 7.88/1.47  ------ Superposition Simplification Setup
% 7.88/1.47  
% 7.88/1.47  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.88/1.47  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.88/1.47  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.88/1.47  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.88/1.47  --sup_full_triv                         [TrivRules;PropSubs]
% 7.88/1.47  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.88/1.47  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.88/1.47  --sup_immed_triv                        [TrivRules]
% 7.88/1.47  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.88/1.47  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.88/1.47  --sup_immed_bw_main                     []
% 7.88/1.47  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.88/1.47  --sup_input_triv                        [Unflattening;TrivRules]
% 7.88/1.47  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.88/1.47  --sup_input_bw                          []
% 7.88/1.47  
% 7.88/1.47  ------ Combination Options
% 7.88/1.47  
% 7.88/1.47  --comb_res_mult                         3
% 7.88/1.47  --comb_sup_mult                         2
% 7.88/1.47  --comb_inst_mult                        10
% 7.88/1.47  
% 7.88/1.47  ------ Debug Options
% 7.88/1.47  
% 7.88/1.47  --dbg_backtrace                         false
% 7.88/1.47  --dbg_dump_prop_clauses                 false
% 7.88/1.47  --dbg_dump_prop_clauses_file            -
% 7.88/1.47  --dbg_out_stat                          false
% 7.88/1.47  ------ Parsing...
% 7.88/1.47  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.88/1.47  
% 7.88/1.47  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.88/1.47  
% 7.88/1.47  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.88/1.47  
% 7.88/1.47  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.88/1.47  ------ Proving...
% 7.88/1.47  ------ Problem Properties 
% 7.88/1.47  
% 7.88/1.47  
% 7.88/1.47  clauses                                 19
% 7.88/1.47  conjectures                             1
% 7.88/1.47  EPR                                     0
% 7.88/1.47  Horn                                    19
% 7.88/1.47  unary                                   6
% 7.88/1.47  binary                                  8
% 7.88/1.47  lits                                    39
% 7.88/1.47  lits eq                                 13
% 7.88/1.47  fd_pure                                 0
% 7.88/1.47  fd_pseudo                               0
% 7.88/1.47  fd_cond                                 0
% 7.88/1.47  fd_pseudo_cond                          0
% 7.88/1.47  AC symbols                              0
% 7.88/1.47  
% 7.88/1.47  ------ Schedule dynamic 5 is on 
% 7.88/1.47  
% 7.88/1.47  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.88/1.47  
% 7.88/1.47  
% 7.88/1.47  ------ 
% 7.88/1.47  Current options:
% 7.88/1.47  ------ 
% 7.88/1.47  
% 7.88/1.47  ------ Input Options
% 7.88/1.47  
% 7.88/1.47  --out_options                           all
% 7.88/1.47  --tptp_safe_out                         true
% 7.88/1.47  --problem_path                          ""
% 7.88/1.47  --include_path                          ""
% 7.88/1.47  --clausifier                            res/vclausify_rel
% 7.88/1.47  --clausifier_options                    ""
% 7.88/1.47  --stdin                                 false
% 7.88/1.47  --stats_out                             all
% 7.88/1.47  
% 7.88/1.47  ------ General Options
% 7.88/1.47  
% 7.88/1.47  --fof                                   false
% 7.88/1.47  --time_out_real                         305.
% 7.88/1.47  --time_out_virtual                      -1.
% 7.88/1.47  --symbol_type_check                     false
% 7.88/1.47  --clausify_out                          false
% 7.88/1.47  --sig_cnt_out                           false
% 7.88/1.47  --trig_cnt_out                          false
% 7.88/1.47  --trig_cnt_out_tolerance                1.
% 7.88/1.47  --trig_cnt_out_sk_spl                   false
% 7.88/1.47  --abstr_cl_out                          false
% 7.88/1.47  
% 7.88/1.47  ------ Global Options
% 7.88/1.47  
% 7.88/1.47  --schedule                              default
% 7.88/1.47  --add_important_lit                     false
% 7.88/1.47  --prop_solver_per_cl                    1000
% 7.88/1.47  --min_unsat_core                        false
% 7.88/1.47  --soft_assumptions                      false
% 7.88/1.47  --soft_lemma_size                       3
% 7.88/1.47  --prop_impl_unit_size                   0
% 7.88/1.47  --prop_impl_unit                        []
% 7.88/1.47  --share_sel_clauses                     true
% 7.88/1.47  --reset_solvers                         false
% 7.88/1.47  --bc_imp_inh                            [conj_cone]
% 7.88/1.47  --conj_cone_tolerance                   3.
% 7.88/1.47  --extra_neg_conj                        none
% 7.88/1.47  --large_theory_mode                     true
% 7.88/1.47  --prolific_symb_bound                   200
% 7.88/1.47  --lt_threshold                          2000
% 7.88/1.47  --clause_weak_htbl                      true
% 7.88/1.47  --gc_record_bc_elim                     false
% 7.88/1.47  
% 7.88/1.47  ------ Preprocessing Options
% 7.88/1.47  
% 7.88/1.47  --preprocessing_flag                    true
% 7.88/1.47  --time_out_prep_mult                    0.1
% 7.88/1.47  --splitting_mode                        input
% 7.88/1.47  --splitting_grd                         true
% 7.88/1.47  --splitting_cvd                         false
% 7.88/1.47  --splitting_cvd_svl                     false
% 7.88/1.47  --splitting_nvd                         32
% 7.88/1.47  --sub_typing                            true
% 7.88/1.47  --prep_gs_sim                           true
% 7.88/1.47  --prep_unflatten                        true
% 7.88/1.47  --prep_res_sim                          true
% 7.88/1.47  --prep_upred                            true
% 7.88/1.47  --prep_sem_filter                       exhaustive
% 7.88/1.47  --prep_sem_filter_out                   false
% 7.88/1.47  --pred_elim                             true
% 7.88/1.47  --res_sim_input                         true
% 7.88/1.47  --eq_ax_congr_red                       true
% 7.88/1.47  --pure_diseq_elim                       true
% 7.88/1.47  --brand_transform                       false
% 7.88/1.47  --non_eq_to_eq                          false
% 7.88/1.47  --prep_def_merge                        true
% 7.88/1.47  --prep_def_merge_prop_impl              false
% 7.88/1.47  --prep_def_merge_mbd                    true
% 7.88/1.47  --prep_def_merge_tr_red                 false
% 7.88/1.47  --prep_def_merge_tr_cl                  false
% 7.88/1.47  --smt_preprocessing                     true
% 7.88/1.47  --smt_ac_axioms                         fast
% 7.88/1.47  --preprocessed_out                      false
% 7.88/1.47  --preprocessed_stats                    false
% 7.88/1.47  
% 7.88/1.47  ------ Abstraction refinement Options
% 7.88/1.47  
% 7.88/1.47  --abstr_ref                             []
% 7.88/1.47  --abstr_ref_prep                        false
% 7.88/1.47  --abstr_ref_until_sat                   false
% 7.88/1.47  --abstr_ref_sig_restrict                funpre
% 7.88/1.47  --abstr_ref_af_restrict_to_split_sk     false
% 7.88/1.47  --abstr_ref_under                       []
% 7.88/1.47  
% 7.88/1.47  ------ SAT Options
% 7.88/1.47  
% 7.88/1.47  --sat_mode                              false
% 7.88/1.47  --sat_fm_restart_options                ""
% 7.88/1.47  --sat_gr_def                            false
% 7.88/1.47  --sat_epr_types                         true
% 7.88/1.47  --sat_non_cyclic_types                  false
% 7.88/1.47  --sat_finite_models                     false
% 7.88/1.47  --sat_fm_lemmas                         false
% 7.88/1.47  --sat_fm_prep                           false
% 7.88/1.47  --sat_fm_uc_incr                        true
% 7.88/1.47  --sat_out_model                         small
% 7.88/1.47  --sat_out_clauses                       false
% 7.88/1.47  
% 7.88/1.47  ------ QBF Options
% 7.88/1.47  
% 7.88/1.47  --qbf_mode                              false
% 7.88/1.47  --qbf_elim_univ                         false
% 7.88/1.47  --qbf_dom_inst                          none
% 7.88/1.47  --qbf_dom_pre_inst                      false
% 7.88/1.47  --qbf_sk_in                             false
% 7.88/1.47  --qbf_pred_elim                         true
% 7.88/1.47  --qbf_split                             512
% 7.88/1.47  
% 7.88/1.47  ------ BMC1 Options
% 7.88/1.47  
% 7.88/1.47  --bmc1_incremental                      false
% 7.88/1.47  --bmc1_axioms                           reachable_all
% 7.88/1.47  --bmc1_min_bound                        0
% 7.88/1.47  --bmc1_max_bound                        -1
% 7.88/1.47  --bmc1_max_bound_default                -1
% 7.88/1.47  --bmc1_symbol_reachability              true
% 7.88/1.47  --bmc1_property_lemmas                  false
% 7.88/1.47  --bmc1_k_induction                      false
% 7.88/1.47  --bmc1_non_equiv_states                 false
% 7.88/1.47  --bmc1_deadlock                         false
% 7.88/1.47  --bmc1_ucm                              false
% 7.88/1.47  --bmc1_add_unsat_core                   none
% 7.88/1.47  --bmc1_unsat_core_children              false
% 7.88/1.47  --bmc1_unsat_core_extrapolate_axioms    false
% 7.88/1.47  --bmc1_out_stat                         full
% 7.88/1.47  --bmc1_ground_init                      false
% 7.88/1.47  --bmc1_pre_inst_next_state              false
% 7.88/1.47  --bmc1_pre_inst_state                   false
% 7.88/1.47  --bmc1_pre_inst_reach_state             false
% 7.88/1.47  --bmc1_out_unsat_core                   false
% 7.88/1.47  --bmc1_aig_witness_out                  false
% 7.88/1.47  --bmc1_verbose                          false
% 7.88/1.47  --bmc1_dump_clauses_tptp                false
% 7.88/1.47  --bmc1_dump_unsat_core_tptp             false
% 7.88/1.47  --bmc1_dump_file                        -
% 7.88/1.47  --bmc1_ucm_expand_uc_limit              128
% 7.88/1.47  --bmc1_ucm_n_expand_iterations          6
% 7.88/1.47  --bmc1_ucm_extend_mode                  1
% 7.88/1.47  --bmc1_ucm_init_mode                    2
% 7.88/1.47  --bmc1_ucm_cone_mode                    none
% 7.88/1.47  --bmc1_ucm_reduced_relation_type        0
% 7.88/1.47  --bmc1_ucm_relax_model                  4
% 7.88/1.47  --bmc1_ucm_full_tr_after_sat            true
% 7.88/1.47  --bmc1_ucm_expand_neg_assumptions       false
% 7.88/1.47  --bmc1_ucm_layered_model                none
% 7.88/1.47  --bmc1_ucm_max_lemma_size               10
% 7.88/1.47  
% 7.88/1.47  ------ AIG Options
% 7.88/1.47  
% 7.88/1.47  --aig_mode                              false
% 7.88/1.47  
% 7.88/1.47  ------ Instantiation Options
% 7.88/1.47  
% 7.88/1.47  --instantiation_flag                    true
% 7.88/1.47  --inst_sos_flag                         true
% 7.88/1.47  --inst_sos_phase                        true
% 7.88/1.47  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.88/1.47  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.88/1.47  --inst_lit_sel_side                     none
% 7.88/1.47  --inst_solver_per_active                1400
% 7.88/1.47  --inst_solver_calls_frac                1.
% 7.88/1.47  --inst_passive_queue_type               priority_queues
% 7.88/1.47  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.88/1.47  --inst_passive_queues_freq              [25;2]
% 7.88/1.47  --inst_dismatching                      true
% 7.88/1.47  --inst_eager_unprocessed_to_passive     true
% 7.88/1.47  --inst_prop_sim_given                   true
% 7.88/1.47  --inst_prop_sim_new                     false
% 7.88/1.47  --inst_subs_new                         false
% 7.88/1.47  --inst_eq_res_simp                      false
% 7.88/1.47  --inst_subs_given                       false
% 7.88/1.47  --inst_orphan_elimination               true
% 7.88/1.47  --inst_learning_loop_flag               true
% 7.88/1.47  --inst_learning_start                   3000
% 7.88/1.47  --inst_learning_factor                  2
% 7.88/1.47  --inst_start_prop_sim_after_learn       3
% 7.88/1.47  --inst_sel_renew                        solver
% 7.88/1.47  --inst_lit_activity_flag                true
% 7.88/1.47  --inst_restr_to_given                   false
% 7.88/1.47  --inst_activity_threshold               500
% 7.88/1.47  --inst_out_proof                        true
% 7.88/1.47  
% 7.88/1.47  ------ Resolution Options
% 7.88/1.47  
% 7.88/1.47  --resolution_flag                       false
% 7.88/1.47  --res_lit_sel                           adaptive
% 7.88/1.47  --res_lit_sel_side                      none
% 7.88/1.47  --res_ordering                          kbo
% 7.88/1.47  --res_to_prop_solver                    active
% 7.88/1.47  --res_prop_simpl_new                    false
% 7.88/1.47  --res_prop_simpl_given                  true
% 7.88/1.47  --res_passive_queue_type                priority_queues
% 7.88/1.47  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.88/1.47  --res_passive_queues_freq               [15;5]
% 7.88/1.47  --res_forward_subs                      full
% 7.88/1.47  --res_backward_subs                     full
% 7.88/1.47  --res_forward_subs_resolution           true
% 7.88/1.47  --res_backward_subs_resolution          true
% 7.88/1.47  --res_orphan_elimination                true
% 7.88/1.47  --res_time_limit                        2.
% 7.88/1.47  --res_out_proof                         true
% 7.88/1.47  
% 7.88/1.47  ------ Superposition Options
% 7.88/1.47  
% 7.88/1.47  --superposition_flag                    true
% 7.88/1.47  --sup_passive_queue_type                priority_queues
% 7.88/1.47  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.88/1.47  --sup_passive_queues_freq               [8;1;4]
% 7.88/1.47  --demod_completeness_check              fast
% 7.88/1.47  --demod_use_ground                      true
% 7.88/1.47  --sup_to_prop_solver                    passive
% 7.88/1.47  --sup_prop_simpl_new                    true
% 7.88/1.47  --sup_prop_simpl_given                  true
% 7.88/1.47  --sup_fun_splitting                     true
% 7.88/1.47  --sup_smt_interval                      50000
% 7.88/1.47  
% 7.88/1.47  ------ Superposition Simplification Setup
% 7.88/1.47  
% 7.88/1.47  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.88/1.47  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.88/1.47  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.88/1.47  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.88/1.47  --sup_full_triv                         [TrivRules;PropSubs]
% 7.88/1.47  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.88/1.47  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.88/1.47  --sup_immed_triv                        [TrivRules]
% 7.88/1.47  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.88/1.47  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.88/1.47  --sup_immed_bw_main                     []
% 7.88/1.47  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.88/1.47  --sup_input_triv                        [Unflattening;TrivRules]
% 7.88/1.47  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.88/1.47  --sup_input_bw                          []
% 7.88/1.47  
% 7.88/1.47  ------ Combination Options
% 7.88/1.47  
% 7.88/1.47  --comb_res_mult                         3
% 7.88/1.47  --comb_sup_mult                         2
% 7.88/1.47  --comb_inst_mult                        10
% 7.88/1.47  
% 7.88/1.47  ------ Debug Options
% 7.88/1.47  
% 7.88/1.47  --dbg_backtrace                         false
% 7.88/1.47  --dbg_dump_prop_clauses                 false
% 7.88/1.47  --dbg_dump_prop_clauses_file            -
% 7.88/1.47  --dbg_out_stat                          false
% 7.88/1.47  
% 7.88/1.47  
% 7.88/1.47  
% 7.88/1.47  
% 7.88/1.47  ------ Proving...
% 7.88/1.47  
% 7.88/1.47  
% 7.88/1.47  % SZS status Theorem for theBenchmark.p
% 7.88/1.47  
% 7.88/1.47   Resolution empty clause
% 7.88/1.47  
% 7.88/1.47  % SZS output start CNFRefutation for theBenchmark.p
% 7.88/1.47  
% 7.88/1.47  fof(f13,axiom,(
% 7.88/1.47    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 7.88/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.88/1.47  
% 7.88/1.47  fof(f33,plain,(
% 7.88/1.47    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 7.88/1.47    inference(ennf_transformation,[],[f13])).
% 7.88/1.47  
% 7.88/1.47  fof(f34,plain,(
% 7.88/1.47    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.88/1.47    inference(flattening,[],[f33])).
% 7.88/1.47  
% 7.88/1.47  fof(f55,plain,(
% 7.88/1.47    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.88/1.47    inference(cnf_transformation,[],[f34])).
% 7.88/1.47  
% 7.88/1.47  fof(f20,axiom,(
% 7.88/1.47    ! [X0] : (v5_relat_1(k6_relat_1(X0),X0) & v4_relat_1(k6_relat_1(X0),X0) & v1_relat_1(k6_relat_1(X0)))),
% 7.88/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.88/1.47  
% 7.88/1.47  fof(f23,plain,(
% 7.88/1.47    ! [X0] : (v4_relat_1(k6_relat_1(X0),X0) & v1_relat_1(k6_relat_1(X0)))),
% 7.88/1.47    inference(pure_predicate_removal,[],[f20])).
% 7.88/1.47  
% 7.88/1.47  fof(f66,plain,(
% 7.88/1.47    ( ! [X0] : (v4_relat_1(k6_relat_1(X0),X0)) )),
% 7.88/1.47    inference(cnf_transformation,[],[f23])).
% 7.88/1.47  
% 7.88/1.47  fof(f65,plain,(
% 7.88/1.47    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 7.88/1.47    inference(cnf_transformation,[],[f23])).
% 7.88/1.47  
% 7.88/1.47  fof(f8,axiom,(
% 7.88/1.47    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1))),
% 7.88/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.88/1.47  
% 7.88/1.47  fof(f27,plain,(
% 7.88/1.47    ! [X0,X1,X2] : (k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2))),
% 7.88/1.47    inference(ennf_transformation,[],[f8])).
% 7.88/1.47  
% 7.88/1.47  fof(f50,plain,(
% 7.88/1.47    ( ! [X2,X0,X1] : (k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 7.88/1.47    inference(cnf_transformation,[],[f27])).
% 7.88/1.47  
% 7.88/1.47  fof(f5,axiom,(
% 7.88/1.47    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 7.88/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.88/1.47  
% 7.88/1.47  fof(f47,plain,(
% 7.88/1.47    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 7.88/1.47    inference(cnf_transformation,[],[f5])).
% 7.88/1.47  
% 7.88/1.47  fof(f1,axiom,(
% 7.88/1.47    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 7.88/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.88/1.47  
% 7.88/1.47  fof(f43,plain,(
% 7.88/1.47    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 7.88/1.47    inference(cnf_transformation,[],[f1])).
% 7.88/1.47  
% 7.88/1.47  fof(f2,axiom,(
% 7.88/1.47    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 7.88/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.88/1.47  
% 7.88/1.47  fof(f44,plain,(
% 7.88/1.47    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 7.88/1.47    inference(cnf_transformation,[],[f2])).
% 7.88/1.47  
% 7.88/1.47  fof(f3,axiom,(
% 7.88/1.47    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 7.88/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.88/1.47  
% 7.88/1.47  fof(f45,plain,(
% 7.88/1.47    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 7.88/1.47    inference(cnf_transformation,[],[f3])).
% 7.88/1.47  
% 7.88/1.47  fof(f4,axiom,(
% 7.88/1.47    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 7.88/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.88/1.47  
% 7.88/1.47  fof(f46,plain,(
% 7.88/1.47    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 7.88/1.47    inference(cnf_transformation,[],[f4])).
% 7.88/1.47  
% 7.88/1.47  fof(f68,plain,(
% 7.88/1.47    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 7.88/1.47    inference(definition_unfolding,[],[f45,f46])).
% 7.88/1.47  
% 7.88/1.47  fof(f69,plain,(
% 7.88/1.47    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 7.88/1.47    inference(definition_unfolding,[],[f44,f68])).
% 7.88/1.47  
% 7.88/1.47  fof(f70,plain,(
% 7.88/1.47    ( ! [X0,X1] : (k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1)) )),
% 7.88/1.47    inference(definition_unfolding,[],[f43,f69])).
% 7.88/1.47  
% 7.88/1.47  fof(f71,plain,(
% 7.88/1.47    ( ! [X0,X1] : (k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)) = k3_xboole_0(X0,X1)) )),
% 7.88/1.47    inference(definition_unfolding,[],[f47,f70])).
% 7.88/1.47  
% 7.88/1.47  fof(f72,plain,(
% 7.88/1.47    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))) | ~v1_relat_1(X2)) )),
% 7.88/1.47    inference(definition_unfolding,[],[f50,f71])).
% 7.88/1.47  
% 7.88/1.47  fof(f9,axiom,(
% 7.88/1.47    ! [X0,X1] : (v1_relat_1(X1) => k3_xboole_0(k2_relat_1(X1),X0) = k2_relat_1(k8_relat_1(X0,X1)))),
% 7.88/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.88/1.47  
% 7.88/1.47  fof(f28,plain,(
% 7.88/1.47    ! [X0,X1] : (k3_xboole_0(k2_relat_1(X1),X0) = k2_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1))),
% 7.88/1.47    inference(ennf_transformation,[],[f9])).
% 7.88/1.47  
% 7.88/1.47  fof(f51,plain,(
% 7.88/1.47    ( ! [X0,X1] : (k3_xboole_0(k2_relat_1(X1),X0) = k2_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1)) )),
% 7.88/1.47    inference(cnf_transformation,[],[f28])).
% 7.88/1.47  
% 7.88/1.47  fof(f73,plain,(
% 7.88/1.47    ( ! [X0,X1] : (k1_setfam_1(k4_enumset1(k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),X0)) = k2_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1)) )),
% 7.88/1.47    inference(definition_unfolding,[],[f51,f71])).
% 7.88/1.47  
% 7.88/1.47  fof(f16,axiom,(
% 7.88/1.47    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 7.88/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.88/1.47  
% 7.88/1.47  fof(f60,plain,(
% 7.88/1.47    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 7.88/1.47    inference(cnf_transformation,[],[f16])).
% 7.88/1.47  
% 7.88/1.47  fof(f10,axiom,(
% 7.88/1.47    ! [X0,X1] : (v1_relat_1(X1) => k5_relat_1(X1,k6_relat_1(X0)) = k8_relat_1(X0,X1))),
% 7.88/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.88/1.47  
% 7.88/1.47  fof(f29,plain,(
% 7.88/1.47    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = k8_relat_1(X0,X1) | ~v1_relat_1(X1))),
% 7.88/1.47    inference(ennf_transformation,[],[f10])).
% 7.88/1.47  
% 7.88/1.47  fof(f52,plain,(
% 7.88/1.47    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = k8_relat_1(X0,X1) | ~v1_relat_1(X1)) )),
% 7.88/1.47    inference(cnf_transformation,[],[f29])).
% 7.88/1.47  
% 7.88/1.47  fof(f19,axiom,(
% 7.88/1.47    ! [X0,X1] : (v1_relat_1(X1) => k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0))),
% 7.88/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.88/1.47  
% 7.88/1.47  fof(f39,plain,(
% 7.88/1.47    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.88/1.47    inference(ennf_transformation,[],[f19])).
% 7.88/1.47  
% 7.88/1.47  fof(f64,plain,(
% 7.88/1.47    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.88/1.47    inference(cnf_transformation,[],[f39])).
% 7.88/1.47  
% 7.88/1.47  fof(f15,axiom,(
% 7.88/1.47    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,X1))))),
% 7.88/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.88/1.47  
% 7.88/1.47  fof(f37,plain,(
% 7.88/1.47    ! [X0] : (! [X1] : (k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 7.88/1.47    inference(ennf_transformation,[],[f15])).
% 7.88/1.47  
% 7.88/1.47  fof(f58,plain,(
% 7.88/1.47    ( ! [X0,X1] : (k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 7.88/1.47    inference(cnf_transformation,[],[f37])).
% 7.88/1.47  
% 7.88/1.47  fof(f17,axiom,(
% 7.88/1.47    ! [X0] : k4_relat_1(k6_relat_1(X0)) = k6_relat_1(X0)),
% 7.88/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.88/1.47  
% 7.88/1.47  fof(f61,plain,(
% 7.88/1.47    ( ! [X0] : (k4_relat_1(k6_relat_1(X0)) = k6_relat_1(X0)) )),
% 7.88/1.47    inference(cnf_transformation,[],[f17])).
% 7.88/1.47  
% 7.88/1.47  fof(f6,axiom,(
% 7.88/1.47    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 7.88/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.88/1.47  
% 7.88/1.47  fof(f24,plain,(
% 7.88/1.47    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 7.88/1.47    inference(ennf_transformation,[],[f6])).
% 7.88/1.47  
% 7.88/1.47  fof(f25,plain,(
% 7.88/1.47    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 7.88/1.47    inference(flattening,[],[f24])).
% 7.88/1.47  
% 7.88/1.47  fof(f48,plain,(
% 7.88/1.47    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 7.88/1.47    inference(cnf_transformation,[],[f25])).
% 7.88/1.47  
% 7.88/1.47  fof(f12,axiom,(
% 7.88/1.47    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)))),
% 7.88/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.88/1.47  
% 7.88/1.47  fof(f32,plain,(
% 7.88/1.47    ! [X0,X1,X2] : (k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 7.88/1.47    inference(ennf_transformation,[],[f12])).
% 7.88/1.47  
% 7.88/1.47  fof(f54,plain,(
% 7.88/1.47    ( ! [X2,X0,X1] : (k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 7.88/1.47    inference(cnf_transformation,[],[f32])).
% 7.88/1.47  
% 7.88/1.47  fof(f18,axiom,(
% 7.88/1.47    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)))),
% 7.88/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.88/1.47  
% 7.88/1.47  fof(f38,plain,(
% 7.88/1.47    ! [X0,X1] : ((r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)) | ~v1_relat_1(X1))),
% 7.88/1.47    inference(ennf_transformation,[],[f18])).
% 7.88/1.47  
% 7.88/1.47  fof(f63,plain,(
% 7.88/1.47    ( ! [X0,X1] : (r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) | ~v1_relat_1(X1)) )),
% 7.88/1.47    inference(cnf_transformation,[],[f38])).
% 7.88/1.47  
% 7.88/1.47  fof(f59,plain,(
% 7.88/1.47    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 7.88/1.47    inference(cnf_transformation,[],[f16])).
% 7.88/1.47  
% 7.88/1.47  fof(f14,axiom,(
% 7.88/1.47    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 7.88/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.88/1.47  
% 7.88/1.47  fof(f35,plain,(
% 7.88/1.47    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 7.88/1.47    inference(ennf_transformation,[],[f14])).
% 7.88/1.47  
% 7.88/1.47  fof(f36,plain,(
% 7.88/1.47    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 7.88/1.47    inference(flattening,[],[f35])).
% 7.88/1.47  
% 7.88/1.47  fof(f56,plain,(
% 7.88/1.47    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 7.88/1.47    inference(cnf_transformation,[],[f36])).
% 7.88/1.47  
% 7.88/1.47  fof(f11,axiom,(
% 7.88/1.47    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k8_relat_1(X0,X1) = X1))),
% 7.88/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.88/1.47  
% 7.88/1.47  fof(f30,plain,(
% 7.88/1.47    ! [X0,X1] : ((k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.88/1.47    inference(ennf_transformation,[],[f11])).
% 7.88/1.47  
% 7.88/1.47  fof(f31,plain,(
% 7.88/1.47    ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 7.88/1.47    inference(flattening,[],[f30])).
% 7.88/1.47  
% 7.88/1.47  fof(f53,plain,(
% 7.88/1.47    ( ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 7.88/1.47    inference(cnf_transformation,[],[f31])).
% 7.88/1.47  
% 7.88/1.47  fof(f62,plain,(
% 7.88/1.47    ( ! [X0,X1] : (r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) | ~v1_relat_1(X1)) )),
% 7.88/1.47    inference(cnf_transformation,[],[f38])).
% 7.88/1.47  
% 7.88/1.47  fof(f57,plain,(
% 7.88/1.47    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 7.88/1.47    inference(cnf_transformation,[],[f36])).
% 7.88/1.47  
% 7.88/1.47  fof(f21,conjecture,(
% 7.88/1.47    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 7.88/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.88/1.47  
% 7.88/1.47  fof(f22,negated_conjecture,(
% 7.88/1.47    ~! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 7.88/1.47    inference(negated_conjecture,[],[f21])).
% 7.88/1.47  
% 7.88/1.47  fof(f40,plain,(
% 7.88/1.47    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))),
% 7.88/1.47    inference(ennf_transformation,[],[f22])).
% 7.88/1.47  
% 7.88/1.47  fof(f41,plain,(
% 7.88/1.47    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 7.88/1.47    introduced(choice_axiom,[])).
% 7.88/1.47  
% 7.88/1.47  fof(f42,plain,(
% 7.88/1.47    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 7.88/1.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f40,f41])).
% 7.88/1.47  
% 7.88/1.47  fof(f67,plain,(
% 7.88/1.47    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 7.88/1.47    inference(cnf_transformation,[],[f42])).
% 7.88/1.47  
% 7.88/1.47  fof(f74,plain,(
% 7.88/1.47    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1)))),
% 7.88/1.47    inference(definition_unfolding,[],[f67,f71])).
% 7.88/1.47  
% 7.88/1.47  cnf(c_7,plain,
% 7.88/1.47      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 7.88/1.47      inference(cnf_transformation,[],[f55]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_17,plain,
% 7.88/1.47      ( v4_relat_1(k6_relat_1(X0),X0) ),
% 7.88/1.47      inference(cnf_transformation,[],[f66]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_206,plain,
% 7.88/1.47      ( ~ v1_relat_1(X0)
% 7.88/1.47      | X1 != X2
% 7.88/1.47      | k7_relat_1(X0,X2) = X0
% 7.88/1.47      | k6_relat_1(X1) != X0 ),
% 7.88/1.47      inference(resolution_lifted,[status(thm)],[c_7,c_17]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_207,plain,
% 7.88/1.47      ( ~ v1_relat_1(k6_relat_1(X0))
% 7.88/1.47      | k7_relat_1(k6_relat_1(X0),X0) = k6_relat_1(X0) ),
% 7.88/1.47      inference(unflattening,[status(thm)],[c_206]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_18,plain,
% 7.88/1.47      ( v1_relat_1(k6_relat_1(X0)) ),
% 7.88/1.47      inference(cnf_transformation,[],[f65]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_211,plain,
% 7.88/1.47      ( k7_relat_1(k6_relat_1(X0),X0) = k6_relat_1(X0) ),
% 7.88/1.47      inference(global_propositional_subsumption,[status(thm)],[c_207,c_18]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_573,plain,
% 7.88/1.47      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 7.88/1.47      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_2,plain,
% 7.88/1.47      ( ~ v1_relat_1(X0)
% 7.88/1.47      | k7_relat_1(X0,k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X2))) = k7_relat_1(k7_relat_1(X0,X1),X2) ),
% 7.88/1.47      inference(cnf_transformation,[],[f72]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_584,plain,
% 7.88/1.47      ( k7_relat_1(X0,k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X2))) = k7_relat_1(k7_relat_1(X0,X1),X2)
% 7.88/1.47      | v1_relat_1(X0) != iProver_top ),
% 7.88/1.47      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_1313,plain,
% 7.88/1.47      ( k7_relat_1(k6_relat_1(X0),k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X2))) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) ),
% 7.88/1.47      inference(superposition,[status(thm)],[c_573,c_584]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_3,plain,
% 7.88/1.47      ( ~ v1_relat_1(X0)
% 7.88/1.47      | k1_setfam_1(k4_enumset1(k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X0),X1)) = k2_relat_1(k8_relat_1(X1,X0)) ),
% 7.88/1.47      inference(cnf_transformation,[],[f73]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_583,plain,
% 7.88/1.47      ( k1_setfam_1(k4_enumset1(k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X0),X1)) = k2_relat_1(k8_relat_1(X1,X0))
% 7.88/1.47      | v1_relat_1(X0) != iProver_top ),
% 7.88/1.47      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_1320,plain,
% 7.88/1.47      ( k1_setfam_1(k4_enumset1(k2_relat_1(k6_relat_1(X0)),k2_relat_1(k6_relat_1(X0)),k2_relat_1(k6_relat_1(X0)),k2_relat_1(k6_relat_1(X0)),k2_relat_1(k6_relat_1(X0)),X1)) = k2_relat_1(k8_relat_1(X1,k6_relat_1(X0))) ),
% 7.88/1.47      inference(superposition,[status(thm)],[c_573,c_583]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_11,plain,
% 7.88/1.47      ( k2_relat_1(k6_relat_1(X0)) = X0 ),
% 7.88/1.47      inference(cnf_transformation,[],[f60]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_1321,plain,
% 7.88/1.47      ( k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)) = k2_relat_1(k8_relat_1(X1,k6_relat_1(X0))) ),
% 7.88/1.47      inference(light_normalisation,[status(thm)],[c_1320,c_11]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_4,plain,
% 7.88/1.47      ( ~ v1_relat_1(X0) | k5_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X1,X0) ),
% 7.88/1.47      inference(cnf_transformation,[],[f52]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_582,plain,
% 7.88/1.47      ( k5_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X1,X0)
% 7.88/1.47      | v1_relat_1(X0) != iProver_top ),
% 7.88/1.47      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_876,plain,
% 7.88/1.47      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k8_relat_1(X1,k6_relat_1(X0)) ),
% 7.88/1.47      inference(superposition,[status(thm)],[c_573,c_582]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_16,plain,
% 7.88/1.47      ( ~ v1_relat_1(X0) | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
% 7.88/1.47      inference(cnf_transformation,[],[f64]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_574,plain,
% 7.88/1.47      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
% 7.88/1.47      | v1_relat_1(X1) != iProver_top ),
% 7.88/1.47      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_774,plain,
% 7.88/1.47      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
% 7.88/1.47      inference(superposition,[status(thm)],[c_573,c_574]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_877,plain,
% 7.88/1.47      ( k8_relat_1(X0,k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X0),X1) ),
% 7.88/1.47      inference(light_normalisation,[status(thm)],[c_876,c_774]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_1322,plain,
% 7.88/1.47      ( k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)) = k2_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
% 7.88/1.47      inference(demodulation,[status(thm)],[c_1321,c_877]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_1492,plain,
% 7.88/1.47      ( k7_relat_1(k6_relat_1(X0),k2_relat_1(k7_relat_1(k6_relat_1(X1),X2))) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X2),X1) ),
% 7.88/1.47      inference(demodulation,[status(thm)],[c_1313,c_1322]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_10,plain,
% 7.88/1.47      ( ~ v1_relat_1(X0)
% 7.88/1.47      | ~ v1_relat_1(X1)
% 7.88/1.47      | k5_relat_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k5_relat_1(X1,X0)) ),
% 7.88/1.47      inference(cnf_transformation,[],[f58]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_577,plain,
% 7.88/1.47      ( k5_relat_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k5_relat_1(X1,X0))
% 7.88/1.47      | v1_relat_1(X0) != iProver_top
% 7.88/1.47      | v1_relat_1(X1) != iProver_top ),
% 7.88/1.47      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_1175,plain,
% 7.88/1.47      ( k5_relat_1(k4_relat_1(k6_relat_1(X0)),k4_relat_1(X1)) = k4_relat_1(k5_relat_1(X1,k6_relat_1(X0)))
% 7.88/1.47      | v1_relat_1(X1) != iProver_top ),
% 7.88/1.47      inference(superposition,[status(thm)],[c_573,c_577]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_13,plain,
% 7.88/1.47      ( k4_relat_1(k6_relat_1(X0)) = k6_relat_1(X0) ),
% 7.88/1.47      inference(cnf_transformation,[],[f61]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_1176,plain,
% 7.88/1.47      ( k4_relat_1(k5_relat_1(X0,k6_relat_1(X1))) = k5_relat_1(k6_relat_1(X1),k4_relat_1(X0))
% 7.88/1.47      | v1_relat_1(X0) != iProver_top ),
% 7.88/1.47      inference(light_normalisation,[status(thm)],[c_1175,c_13]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_1219,plain,
% 7.88/1.47      ( k4_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k5_relat_1(k6_relat_1(X1),k4_relat_1(k6_relat_1(X0))) ),
% 7.88/1.47      inference(superposition,[status(thm)],[c_573,c_1176]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_1220,plain,
% 7.88/1.47      ( k4_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) ),
% 7.88/1.47      inference(light_normalisation,[status(thm)],[c_1219,c_13,c_774]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_1221,plain,
% 7.88/1.47      ( k4_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
% 7.88/1.47      inference(demodulation,[status(thm)],[c_1220,c_774]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_1498,plain,
% 7.88/1.47      ( k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X2) = k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X2),X1),X0)) ),
% 7.88/1.47      inference(superposition,[status(thm)],[c_1492,c_1221]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_0,plain,
% 7.88/1.47      ( ~ v1_relat_1(X0) | ~ v1_relat_1(X1) | v1_relat_1(k5_relat_1(X1,X0)) ),
% 7.88/1.47      inference(cnf_transformation,[],[f48]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_586,plain,
% 7.88/1.47      ( v1_relat_1(X0) != iProver_top
% 7.88/1.47      | v1_relat_1(X1) != iProver_top
% 7.88/1.47      | v1_relat_1(k5_relat_1(X1,X0)) = iProver_top ),
% 7.88/1.47      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_981,plain,
% 7.88/1.47      ( v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = iProver_top
% 7.88/1.47      | v1_relat_1(k6_relat_1(X0)) != iProver_top
% 7.88/1.47      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 7.88/1.47      inference(superposition,[status(thm)],[c_774,c_586]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_20,plain,
% 7.88/1.47      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 7.88/1.47      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_3396,plain,
% 7.88/1.47      ( v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = iProver_top
% 7.88/1.47      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 7.88/1.47      inference(global_propositional_subsumption,[status(thm)],[c_981,c_20]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_3720,plain,
% 7.88/1.47      ( v1_relat_1(k6_relat_1(X0)) != iProver_top
% 7.88/1.47      | v1_relat_1(k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2))) = iProver_top ),
% 7.88/1.47      inference(superposition,[status(thm)],[c_1498,c_3396]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_7409,plain,
% 7.88/1.47      ( v1_relat_1(k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2))) = iProver_top ),
% 7.88/1.47      inference(global_propositional_subsumption,[status(thm)],[c_3720,c_20]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_7418,plain,
% 7.88/1.47      ( v1_relat_1(k4_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = iProver_top ),
% 7.88/1.47      inference(superposition,[status(thm)],[c_211,c_7409]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_7465,plain,
% 7.88/1.47      ( v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = iProver_top ),
% 7.88/1.47      inference(light_normalisation,[status(thm)],[c_7418,c_1221]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_1497,plain,
% 7.88/1.47      ( k7_relat_1(k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X1),X0) = k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
% 7.88/1.47      inference(superposition,[status(thm)],[c_1492,c_211]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_1506,plain,
% 7.88/1.47      ( k7_relat_1(k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X0),X1)),X1) = k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X1),X0))) ),
% 7.88/1.47      inference(demodulation,[status(thm)],[c_1497,c_1498]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_1507,plain,
% 7.88/1.47      ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0) = k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
% 7.88/1.47      inference(light_normalisation,[status(thm)],[c_1506,c_211,c_1221]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_7536,plain,
% 7.88/1.47      ( k4_relat_1(k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X2))) = k5_relat_1(k6_relat_1(X2),k4_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
% 7.88/1.47      inference(superposition,[status(thm)],[c_7465,c_1176]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_932,plain,
% 7.88/1.47      ( k5_relat_1(k5_relat_1(X0,X1),k6_relat_1(X2)) = k8_relat_1(X2,k5_relat_1(X0,X1))
% 7.88/1.47      | v1_relat_1(X1) != iProver_top
% 7.88/1.47      | v1_relat_1(X0) != iProver_top ),
% 7.88/1.47      inference(superposition,[status(thm)],[c_586,c_582]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_2648,plain,
% 7.88/1.47      ( k5_relat_1(k5_relat_1(k6_relat_1(X0),X1),k6_relat_1(X2)) = k8_relat_1(X2,k5_relat_1(k6_relat_1(X0),X1))
% 7.88/1.47      | v1_relat_1(X1) != iProver_top ),
% 7.88/1.47      inference(superposition,[status(thm)],[c_573,c_932]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_2883,plain,
% 7.88/1.47      ( k5_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),k6_relat_1(X2)) = k8_relat_1(X2,k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) ),
% 7.88/1.47      inference(superposition,[status(thm)],[c_573,c_2648]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_2884,plain,
% 7.88/1.47      ( k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X2)) = k8_relat_1(X2,k7_relat_1(k6_relat_1(X0),X1)) ),
% 7.88/1.47      inference(light_normalisation,[status(thm)],[c_2883,c_774]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_6,plain,
% 7.88/1.47      ( ~ v1_relat_1(X0)
% 7.88/1.47      | k8_relat_1(X1,k7_relat_1(X0,X2)) = k7_relat_1(k8_relat_1(X1,X0),X2) ),
% 7.88/1.47      inference(cnf_transformation,[],[f54]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_580,plain,
% 7.88/1.47      ( k8_relat_1(X0,k7_relat_1(X1,X2)) = k7_relat_1(k8_relat_1(X0,X1),X2)
% 7.88/1.47      | v1_relat_1(X1) != iProver_top ),
% 7.88/1.47      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_880,plain,
% 7.88/1.47      ( k8_relat_1(X0,k7_relat_1(k6_relat_1(X1),X2)) = k7_relat_1(k8_relat_1(X0,k6_relat_1(X1)),X2) ),
% 7.88/1.47      inference(superposition,[status(thm)],[c_573,c_580]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_881,plain,
% 7.88/1.47      ( k8_relat_1(X0,k7_relat_1(k6_relat_1(X1),X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) ),
% 7.88/1.47      inference(light_normalisation,[status(thm)],[c_880,c_877]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_2885,plain,
% 7.88/1.47      ( k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X0),X1) ),
% 7.88/1.47      inference(demodulation,[status(thm)],[c_2884,c_881]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_7547,plain,
% 7.88/1.47      ( k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)) = k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X2),X1)) ),
% 7.88/1.47      inference(light_normalisation,[status(thm)],[c_7536,c_1221,c_2885]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_931,plain,
% 7.88/1.47      ( k5_relat_1(k6_relat_1(X0),k5_relat_1(X1,X2)) = k7_relat_1(k5_relat_1(X1,X2),X0)
% 7.88/1.47      | v1_relat_1(X2) != iProver_top
% 7.88/1.47      | v1_relat_1(X1) != iProver_top ),
% 7.88/1.47      inference(superposition,[status(thm)],[c_586,c_574]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_2106,plain,
% 7.88/1.47      ( k5_relat_1(k6_relat_1(X0),k5_relat_1(k6_relat_1(X1),X2)) = k7_relat_1(k5_relat_1(k6_relat_1(X1),X2),X0)
% 7.88/1.47      | v1_relat_1(X2) != iProver_top ),
% 7.88/1.47      inference(superposition,[status(thm)],[c_573,c_931]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_2875,plain,
% 7.88/1.47      ( k5_relat_1(k6_relat_1(X0),k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) = k7_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)),X0) ),
% 7.88/1.47      inference(superposition,[status(thm)],[c_573,c_2106]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_2876,plain,
% 7.88/1.47      ( k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X1),X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X0) ),
% 7.88/1.47      inference(demodulation,[status(thm)],[c_2875,c_774]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_7548,plain,
% 7.88/1.47      ( k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X1),X0) ),
% 7.88/1.47      inference(demodulation,[status(thm)],[c_7547,c_2876]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_14,plain,
% 7.88/1.47      ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) | ~ v1_relat_1(X1) ),
% 7.88/1.47      inference(cnf_transformation,[],[f63]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_576,plain,
% 7.88/1.47      ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) = iProver_top
% 7.88/1.47      | v1_relat_1(X1) != iProver_top ),
% 7.88/1.47      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_983,plain,
% 7.88/1.47      ( r1_tarski(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X0)) = iProver_top
% 7.88/1.47      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 7.88/1.47      inference(superposition,[status(thm)],[c_774,c_576]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_1166,plain,
% 7.88/1.47      ( r1_tarski(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X0)) = iProver_top ),
% 7.88/1.47      inference(global_propositional_subsumption,[status(thm)],[c_983,c_20]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_1499,plain,
% 7.88/1.47      ( r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2),k6_relat_1(X0)) = iProver_top ),
% 7.88/1.47      inference(superposition,[status(thm)],[c_1492,c_1166]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_1610,plain,
% 7.88/1.47      ( r1_tarski(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))),k6_relat_1(X0)) = iProver_top ),
% 7.88/1.47      inference(superposition,[status(thm)],[c_1507,c_1499]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_12,plain,
% 7.88/1.47      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 7.88/1.47      inference(cnf_transformation,[],[f59]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_9,plain,
% 7.88/1.47      ( ~ r1_tarski(X0,X1)
% 7.88/1.47      | r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
% 7.88/1.47      | ~ v1_relat_1(X1)
% 7.88/1.47      | ~ v1_relat_1(X0) ),
% 7.88/1.47      inference(cnf_transformation,[],[f56]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_578,plain,
% 7.88/1.47      ( r1_tarski(X0,X1) != iProver_top
% 7.88/1.47      | r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) = iProver_top
% 7.88/1.47      | v1_relat_1(X0) != iProver_top
% 7.88/1.47      | v1_relat_1(X1) != iProver_top ),
% 7.88/1.47      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_1672,plain,
% 7.88/1.47      ( r1_tarski(X0,k1_relat_1(X1)) = iProver_top
% 7.88/1.47      | r1_tarski(k6_relat_1(X0),X1) != iProver_top
% 7.88/1.47      | v1_relat_1(X1) != iProver_top
% 7.88/1.47      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 7.88/1.47      inference(superposition,[status(thm)],[c_12,c_578]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_1723,plain,
% 7.88/1.47      ( v1_relat_1(X1) != iProver_top
% 7.88/1.47      | r1_tarski(k6_relat_1(X0),X1) != iProver_top
% 7.88/1.47      | r1_tarski(X0,k1_relat_1(X1)) = iProver_top ),
% 7.88/1.47      inference(global_propositional_subsumption,[status(thm)],[c_1672,c_20]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_1724,plain,
% 7.88/1.47      ( r1_tarski(X0,k1_relat_1(X1)) = iProver_top
% 7.88/1.47      | r1_tarski(k6_relat_1(X0),X1) != iProver_top
% 7.88/1.47      | v1_relat_1(X1) != iProver_top ),
% 7.88/1.47      inference(renaming,[status(thm)],[c_1723]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_1730,plain,
% 7.88/1.47      ( r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)),k1_relat_1(k6_relat_1(X0))) = iProver_top
% 7.88/1.47      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 7.88/1.47      inference(superposition,[status(thm)],[c_1610,c_1724]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_1731,plain,
% 7.88/1.47      ( r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X0) = iProver_top
% 7.88/1.47      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 7.88/1.47      inference(light_normalisation,[status(thm)],[c_1730,c_12]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_2193,plain,
% 7.88/1.47      ( r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X0) = iProver_top ),
% 7.88/1.47      inference(global_propositional_subsumption,[status(thm)],[c_1731,c_20]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_3736,plain,
% 7.88/1.47      ( r1_tarski(k2_relat_1(k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2))),k2_relat_1(k7_relat_1(k6_relat_1(X2),X1))) = iProver_top ),
% 7.88/1.47      inference(superposition,[status(thm)],[c_1498,c_2193]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_5,plain,
% 7.88/1.47      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 7.88/1.47      | ~ v1_relat_1(X0)
% 7.88/1.47      | k8_relat_1(X1,X0) = X0 ),
% 7.88/1.47      inference(cnf_transformation,[],[f53]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_581,plain,
% 7.88/1.47      ( k8_relat_1(X0,X1) = X1
% 7.88/1.47      | r1_tarski(k2_relat_1(X1),X0) != iProver_top
% 7.88/1.47      | v1_relat_1(X1) != iProver_top ),
% 7.88/1.47      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_1227,plain,
% 7.88/1.47      ( k8_relat_1(X0,k6_relat_1(X1)) = k6_relat_1(X1)
% 7.88/1.47      | r1_tarski(X1,X0) != iProver_top
% 7.88/1.47      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 7.88/1.47      inference(superposition,[status(thm)],[c_11,c_581]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_1228,plain,
% 7.88/1.47      ( k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X1)
% 7.88/1.47      | r1_tarski(X1,X0) != iProver_top
% 7.88/1.47      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 7.88/1.47      inference(demodulation,[status(thm)],[c_1227,c_877]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_4726,plain,
% 7.88/1.47      ( k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))),k2_relat_1(k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X2),X1),X0)))) = k6_relat_1(k2_relat_1(k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X2),X1),X0))))
% 7.88/1.47      | v1_relat_1(k6_relat_1(k2_relat_1(k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X2),X1),X0))))) != iProver_top ),
% 7.88/1.47      inference(superposition,[status(thm)],[c_3736,c_1228]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_3717,plain,
% 7.88/1.47      ( k7_relat_1(k6_relat_1(k2_relat_1(k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)))),X3) = k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X3),X0),k2_relat_1(k7_relat_1(k6_relat_1(X2),X1)))) ),
% 7.88/1.47      inference(superposition,[status(thm)],[c_1498,c_1498]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_1503,plain,
% 7.88/1.47      ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),k2_relat_1(k7_relat_1(k6_relat_1(X2),X3))) = k8_relat_1(X0,k7_relat_1(k7_relat_1(k6_relat_1(X1),X3),X2)) ),
% 7.88/1.47      inference(superposition,[status(thm)],[c_1492,c_881]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_3772,plain,
% 7.88/1.47      ( k7_relat_1(k6_relat_1(k2_relat_1(k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)))),X3) = k4_relat_1(k8_relat_1(X3,k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2))) ),
% 7.88/1.47      inference(demodulation,[status(thm)],[c_3717,c_1503]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_4727,plain,
% 7.88/1.47      ( k4_relat_1(k7_relat_1(k4_relat_1(k8_relat_1(X0,k7_relat_1(k7_relat_1(k6_relat_1(X1),X0),X2))),X2)) = k6_relat_1(k2_relat_1(k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X1),X0),X2))))
% 7.88/1.47      | v1_relat_1(k6_relat_1(k2_relat_1(k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X1),X0),X2))))) != iProver_top ),
% 7.88/1.47      inference(demodulation,[status(thm)],[c_4726,c_1498,c_3772]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_930,plain,
% 7.88/1.47      ( k8_relat_1(X0,k7_relat_1(k5_relat_1(X1,X2),X3)) = k7_relat_1(k8_relat_1(X0,k5_relat_1(X1,X2)),X3)
% 7.88/1.47      | v1_relat_1(X2) != iProver_top
% 7.88/1.47      | v1_relat_1(X1) != iProver_top ),
% 7.88/1.47      inference(superposition,[status(thm)],[c_586,c_580]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_1664,plain,
% 7.88/1.47      ( k8_relat_1(X0,k7_relat_1(k5_relat_1(k6_relat_1(X1),X2),X3)) = k7_relat_1(k8_relat_1(X0,k5_relat_1(k6_relat_1(X1),X2)),X3)
% 7.88/1.47      | v1_relat_1(X2) != iProver_top ),
% 7.88/1.47      inference(superposition,[status(thm)],[c_573,c_930]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_4322,plain,
% 7.88/1.47      ( k8_relat_1(X0,k7_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)),X3)) = k7_relat_1(k8_relat_1(X0,k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))),X3) ),
% 7.88/1.47      inference(superposition,[status(thm)],[c_573,c_1664]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_4325,plain,
% 7.88/1.47      ( k8_relat_1(X0,k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X3)) = k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2),X3) ),
% 7.88/1.47      inference(demodulation,[status(thm)],[c_4322,c_774,c_881]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_4728,plain,
% 7.88/1.47      ( k4_relat_1(k7_relat_1(k4_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0),X2)),X2)) = k6_relat_1(k2_relat_1(k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X1),X0),X2))))
% 7.88/1.47      | v1_relat_1(k6_relat_1(k2_relat_1(k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X1),X0),X2))))) != iProver_top ),
% 7.88/1.47      inference(demodulation,[status(thm)],[c_4727,c_4325]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_4729,plain,
% 7.88/1.47      ( k4_relat_1(k7_relat_1(k4_relat_1(k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2))),X0)) = k6_relat_1(k2_relat_1(k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X0))))
% 7.88/1.47      | v1_relat_1(k6_relat_1(k2_relat_1(k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X0))))) != iProver_top ),
% 7.88/1.47      inference(light_normalisation,[status(thm)],[c_4728,c_1498,c_1507]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_1609,plain,
% 7.88/1.47      ( k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),k2_relat_1(k7_relat_1(k6_relat_1(X1),X2))))) = k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X2),X1),X0) ),
% 7.88/1.47      inference(superposition,[status(thm)],[c_1492,c_1507]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_1613,plain,
% 7.88/1.47      ( k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2),X0) = k6_relat_1(k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2))) ),
% 7.88/1.47      inference(light_normalisation,[status(thm)],[c_1609,c_1492]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_3746,plain,
% 7.88/1.47      ( k7_relat_1(k6_relat_1(X0),k2_relat_1(k7_relat_1(k6_relat_1(X1),X2))) = k4_relat_1(k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X2),X1))) ),
% 7.88/1.47      inference(superposition,[status(thm)],[c_1498,c_1221]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_3759,plain,
% 7.88/1.47      ( k4_relat_1(k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2))) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) ),
% 7.88/1.47      inference(light_normalisation,[status(thm)],[c_3746,c_1492]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_4730,plain,
% 7.88/1.47      ( k6_relat_1(k2_relat_1(k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)))) = k6_relat_1(k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X2),X0),X1)))
% 7.88/1.47      | v1_relat_1(k6_relat_1(k2_relat_1(k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2))))) != iProver_top ),
% 7.88/1.47      inference(demodulation,[status(thm)],[c_4729,c_13,c_1613,c_3759]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_5178,plain,
% 7.88/1.47      ( k6_relat_1(k2_relat_1(k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)))) = k6_relat_1(k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X2),X0),X1))) ),
% 7.88/1.47      inference(superposition,[status(thm)],[c_573,c_4730]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_5421,plain,
% 7.88/1.47      ( k2_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)))) = k2_relat_1(k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X0))) ),
% 7.88/1.47      inference(superposition,[status(thm)],[c_5178,c_11]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_5469,plain,
% 7.88/1.47      ( k2_relat_1(k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2))) = k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X2),X0),X1)) ),
% 7.88/1.47      inference(demodulation,[status(thm)],[c_5421,c_11]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_5481,plain,
% 7.88/1.47      ( r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)),k2_relat_1(k7_relat_1(k6_relat_1(X0),X2))) = iProver_top ),
% 7.88/1.47      inference(demodulation,[status(thm)],[c_5469,c_3736]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_5854,plain,
% 7.88/1.47      ( k8_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)),k7_relat_1(k7_relat_1(k6_relat_1(X0),X2),X1)) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X2),X1)
% 7.88/1.47      | v1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X2),X1)) != iProver_top ),
% 7.88/1.47      inference(superposition,[status(thm)],[c_5481,c_581]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_5859,plain,
% 7.88/1.47      ( k7_relat_1(k7_relat_1(k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0)),X2),X1) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X2),X1)
% 7.88/1.47      | v1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X2),X1)) != iProver_top ),
% 7.88/1.47      inference(demodulation,[status(thm)],[c_5854,c_1498,c_4325]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_5860,plain,
% 7.88/1.47      ( k7_relat_1(k7_relat_1(k4_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)))),X2),X1) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X2),X1)
% 7.88/1.47      | v1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X2),X1)) != iProver_top ),
% 7.88/1.47      inference(light_normalisation,[status(thm)],[c_5859,c_1507]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_5861,plain,
% 7.88/1.47      ( k7_relat_1(k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)),X1) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X0),X1)
% 7.88/1.47      | v1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X2),X0),X1)) != iProver_top ),
% 7.88/1.47      inference(demodulation,[status(thm)],[c_5860,c_13,c_1498]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_15,plain,
% 7.88/1.47      ( r1_tarski(k5_relat_1(X0,k6_relat_1(X1)),X0) | ~ v1_relat_1(X0) ),
% 7.88/1.47      inference(cnf_transformation,[],[f62]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_575,plain,
% 7.88/1.47      ( r1_tarski(k5_relat_1(X0,k6_relat_1(X1)),X0) = iProver_top
% 7.88/1.47      | v1_relat_1(X0) != iProver_top ),
% 7.88/1.47      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_982,plain,
% 7.88/1.47      ( r1_tarski(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X1)) = iProver_top
% 7.88/1.47      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 7.88/1.47      inference(superposition,[status(thm)],[c_774,c_575]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_1097,plain,
% 7.88/1.47      ( r1_tarski(k6_relat_1(X0),k6_relat_1(X0)) = iProver_top
% 7.88/1.47      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 7.88/1.47      inference(superposition,[status(thm)],[c_211,c_982]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_1102,plain,
% 7.88/1.47      ( r1_tarski(k6_relat_1(X0),k6_relat_1(X0)) = iProver_top ),
% 7.88/1.47      inference(global_propositional_subsumption,[status(thm)],[c_1097,c_20]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_1729,plain,
% 7.88/1.47      ( r1_tarski(X0,k1_relat_1(k6_relat_1(X0))) = iProver_top
% 7.88/1.47      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 7.88/1.47      inference(superposition,[status(thm)],[c_1102,c_1724]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_1732,plain,
% 7.88/1.47      ( r1_tarski(X0,X0) = iProver_top
% 7.88/1.47      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 7.88/1.47      inference(light_normalisation,[status(thm)],[c_1729,c_12]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_1764,plain,
% 7.88/1.47      ( r1_tarski(X0,X0) = iProver_top ),
% 7.88/1.47      inference(global_propositional_subsumption,[status(thm)],[c_1732,c_20]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_1770,plain,
% 7.88/1.47      ( k8_relat_1(k2_relat_1(X0),X0) = X0 | v1_relat_1(X0) != iProver_top ),
% 7.88/1.47      inference(superposition,[status(thm)],[c_1764,c_581]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_1776,plain,
% 7.88/1.47      ( k8_relat_1(k2_relat_1(k5_relat_1(X0,X1)),k5_relat_1(X0,X1)) = k5_relat_1(X0,X1)
% 7.88/1.47      | v1_relat_1(X1) != iProver_top
% 7.88/1.47      | v1_relat_1(X0) != iProver_top ),
% 7.88/1.47      inference(superposition,[status(thm)],[c_586,c_1770]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_4336,plain,
% 7.88/1.47      ( k8_relat_1(k2_relat_1(k5_relat_1(k6_relat_1(X0),X1)),k5_relat_1(k6_relat_1(X0),X1)) = k5_relat_1(k6_relat_1(X0),X1)
% 7.88/1.47      | v1_relat_1(X1) != iProver_top ),
% 7.88/1.47      inference(superposition,[status(thm)],[c_573,c_1776]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_4505,plain,
% 7.88/1.47      ( k8_relat_1(k2_relat_1(k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X1),X2))),k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X1),X2))) = k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X1),X2))
% 7.88/1.47      | v1_relat_1(k6_relat_1(X2)) != iProver_top ),
% 7.88/1.47      inference(superposition,[status(thm)],[c_3396,c_4336]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_4506,plain,
% 7.88/1.47      ( k8_relat_1(k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)),k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)
% 7.88/1.47      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 7.88/1.47      inference(light_normalisation,[status(thm)],[c_4505,c_2876]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_3714,plain,
% 7.88/1.47      ( k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),k2_relat_1(k7_relat_1(k6_relat_1(X1),X2))),X3)) = k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X3),X2),X1))),X0) ),
% 7.88/1.47      inference(superposition,[status(thm)],[c_1492,c_1498]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_3775,plain,
% 7.88/1.47      ( k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2))),X3) = k4_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X3),X1),X2),X0)) ),
% 7.88/1.47      inference(light_normalisation,[status(thm)],[c_3714,c_1492]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_4507,plain,
% 7.88/1.47      ( k7_relat_1(k7_relat_1(k4_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2),X0)),X1),X2) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)
% 7.88/1.47      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 7.88/1.47      inference(demodulation,[status(thm)],[c_4506,c_3775,c_4325]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_4508,plain,
% 7.88/1.47      ( k7_relat_1(k7_relat_1(k4_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)))),X1),X2) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)
% 7.88/1.47      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 7.88/1.47      inference(light_normalisation,[status(thm)],[c_4507,c_1613]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_4509,plain,
% 7.88/1.47      ( k7_relat_1(k4_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X0),X1),X2)),X1) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X0),X1)
% 7.88/1.47      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 7.88/1.47      inference(demodulation,[status(thm)],[c_4508,c_13,c_3775]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_4510,plain,
% 7.88/1.47      ( k7_relat_1(k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)),X1) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X0),X1)
% 7.88/1.47      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 7.88/1.47      inference(light_normalisation,[status(thm)],[c_4509,c_211]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_6773,plain,
% 7.88/1.47      ( k7_relat_1(k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)),X1) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X0),X1) ),
% 7.88/1.47      inference(global_propositional_subsumption,
% 7.88/1.47                [status(thm)],
% 7.88/1.47                [c_5861,c_20,c_4510]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_8597,plain,
% 7.88/1.47      ( k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2),X1) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X2),X1) ),
% 7.88/1.47      inference(demodulation,[status(thm)],[c_7548,c_6773]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_8834,plain,
% 7.88/1.47      ( k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X1) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X0),X1) ),
% 7.88/1.47      inference(superposition,[status(thm)],[c_1507,c_8597]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_8867,plain,
% 7.88/1.47      ( k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X1) = k7_relat_1(k6_relat_1(X0),X1) ),
% 7.88/1.47      inference(light_normalisation,[status(thm)],[c_8834,c_211]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_9416,plain,
% 7.88/1.47      ( k7_relat_1(k6_relat_1(X0),k2_relat_1(k7_relat_1(k6_relat_1(X1),X0))) = k4_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
% 7.88/1.47      inference(superposition,[status(thm)],[c_8867,c_1221]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_9457,plain,
% 7.88/1.47      ( k7_relat_1(k6_relat_1(X0),k2_relat_1(k7_relat_1(k6_relat_1(X1),X0))) = k7_relat_1(k6_relat_1(X0),X1) ),
% 7.88/1.47      inference(demodulation,[status(thm)],[c_9416,c_1221,c_1492]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_1048,plain,
% 7.88/1.47      ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X1) = k8_relat_1(X0,k6_relat_1(X1)) ),
% 7.88/1.47      inference(superposition,[status(thm)],[c_211,c_881]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_1049,plain,
% 7.88/1.47      ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X1) = k7_relat_1(k6_relat_1(X0),X1) ),
% 7.88/1.47      inference(light_normalisation,[status(thm)],[c_1048,c_877]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_9684,plain,
% 7.88/1.47      ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),k2_relat_1(k7_relat_1(k6_relat_1(X1),X0))) = k7_relat_1(k6_relat_1(X0),k2_relat_1(k7_relat_1(k6_relat_1(X1),X0))) ),
% 7.88/1.47      inference(superposition,[status(thm)],[c_9457,c_1049]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_9730,plain,
% 7.88/1.47      ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),k2_relat_1(k7_relat_1(k6_relat_1(X1),X0))) = k7_relat_1(k6_relat_1(X0),X1) ),
% 7.88/1.47      inference(demodulation,[status(thm)],[c_9684,c_9457]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_3748,plain,
% 7.88/1.47      ( r1_tarski(k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)),k6_relat_1(X0)) = iProver_top
% 7.88/1.47      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 7.88/1.47      inference(superposition,[status(thm)],[c_1498,c_982]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_21218,plain,
% 7.88/1.47      ( r1_tarski(k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)),k6_relat_1(X0)) = iProver_top ),
% 7.88/1.47      inference(global_propositional_subsumption,[status(thm)],[c_3748,c_20]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_21222,plain,
% 7.88/1.47      ( r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2),k6_relat_1(X2)) = iProver_top ),
% 7.88/1.47      inference(light_normalisation,[status(thm)],[c_21218,c_7548]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_21230,plain,
% 7.88/1.47      ( r1_tarski(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X1),X0)))) = iProver_top ),
% 7.88/1.47      inference(superposition,[status(thm)],[c_9730,c_21222]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_8,plain,
% 7.88/1.47      ( ~ r1_tarski(X0,X1)
% 7.88/1.47      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
% 7.88/1.47      | ~ v1_relat_1(X1)
% 7.88/1.47      | ~ v1_relat_1(X0) ),
% 7.88/1.47      inference(cnf_transformation,[],[f57]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_579,plain,
% 7.88/1.47      ( r1_tarski(X0,X1) != iProver_top
% 7.88/1.47      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) = iProver_top
% 7.88/1.47      | v1_relat_1(X0) != iProver_top
% 7.88/1.47      | v1_relat_1(X1) != iProver_top ),
% 7.88/1.47      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_1712,plain,
% 7.88/1.47      ( k8_relat_1(k2_relat_1(X0),X1) = X1
% 7.88/1.47      | r1_tarski(X1,X0) != iProver_top
% 7.88/1.47      | v1_relat_1(X1) != iProver_top
% 7.88/1.47      | v1_relat_1(X0) != iProver_top ),
% 7.88/1.47      inference(superposition,[status(thm)],[c_579,c_581]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_22224,plain,
% 7.88/1.47      ( k8_relat_1(k2_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)))),k7_relat_1(k6_relat_1(X1),X0)) = k7_relat_1(k6_relat_1(X1),X0)
% 7.88/1.47      | v1_relat_1(k7_relat_1(k6_relat_1(X1),X0)) != iProver_top
% 7.88/1.47      | v1_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)))) != iProver_top ),
% 7.88/1.47      inference(superposition,[status(thm)],[c_21230,c_1712]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_22257,plain,
% 7.88/1.47      ( k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k7_relat_1(k6_relat_1(X1),X0)
% 7.88/1.47      | v1_relat_1(k7_relat_1(k6_relat_1(X1),X0)) != iProver_top
% 7.88/1.47      | v1_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)))) != iProver_top ),
% 7.88/1.47      inference(demodulation,[status(thm)],[c_22224,c_11,c_881,c_1507,c_8867]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_21232,plain,
% 7.88/1.47      ( r1_tarski(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X1)) = iProver_top ),
% 7.88/1.47      inference(superposition,[status(thm)],[c_211,c_21222]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_22180,plain,
% 7.88/1.47      ( k8_relat_1(k2_relat_1(k6_relat_1(X0)),k7_relat_1(k6_relat_1(X1),X0)) = k7_relat_1(k6_relat_1(X1),X0)
% 7.88/1.47      | v1_relat_1(k7_relat_1(k6_relat_1(X1),X0)) != iProver_top
% 7.88/1.47      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 7.88/1.47      inference(superposition,[status(thm)],[c_21232,c_1712]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_22305,plain,
% 7.88/1.47      ( k8_relat_1(X0,k7_relat_1(k6_relat_1(X1),X0)) = k7_relat_1(k6_relat_1(X1),X0)
% 7.88/1.47      | v1_relat_1(k7_relat_1(k6_relat_1(X1),X0)) != iProver_top
% 7.88/1.47      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 7.88/1.47      inference(light_normalisation,[status(thm)],[c_22180,c_11]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_22306,plain,
% 7.88/1.47      ( k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k7_relat_1(k6_relat_1(X1),X0)
% 7.88/1.47      | v1_relat_1(k7_relat_1(k6_relat_1(X1),X0)) != iProver_top
% 7.88/1.47      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 7.88/1.47      inference(demodulation,[status(thm)],[c_22305,c_881,c_1507]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_23272,plain,
% 7.88/1.47      ( v1_relat_1(k7_relat_1(k6_relat_1(X1),X0)) != iProver_top
% 7.88/1.47      | k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k7_relat_1(k6_relat_1(X1),X0) ),
% 7.88/1.47      inference(global_propositional_subsumption,
% 7.88/1.47                [status(thm)],
% 7.88/1.47                [c_22257,c_20,c_22306]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_23273,plain,
% 7.88/1.47      ( k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k7_relat_1(k6_relat_1(X1),X0)
% 7.88/1.47      | v1_relat_1(k7_relat_1(k6_relat_1(X1),X0)) != iProver_top ),
% 7.88/1.47      inference(renaming,[status(thm)],[c_23272]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_23278,plain,
% 7.88/1.47      ( k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k7_relat_1(k6_relat_1(X1),X0) ),
% 7.88/1.47      inference(superposition,[status(thm)],[c_7465,c_23273]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_19,negated_conjecture,
% 7.88/1.47      ( k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))) ),
% 7.88/1.47      inference(cnf_transformation,[],[f74]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_980,plain,
% 7.88/1.47      ( k6_relat_1(k1_setfam_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))) != k7_relat_1(k6_relat_1(sK0),sK1) ),
% 7.88/1.47      inference(demodulation,[status(thm)],[c_774,c_19]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_1372,plain,
% 7.88/1.47      ( k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(sK1),sK0))) != k7_relat_1(k6_relat_1(sK0),sK1) ),
% 7.88/1.47      inference(demodulation,[status(thm)],[c_1322,c_980]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_23547,plain,
% 7.88/1.47      ( k7_relat_1(k6_relat_1(sK0),sK1) != k7_relat_1(k6_relat_1(sK0),sK1) ),
% 7.88/1.47      inference(demodulation,[status(thm)],[c_23278,c_1372]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_23579,plain,
% 7.88/1.47      ( $false ),
% 7.88/1.47      inference(equality_resolution_simp,[status(thm)],[c_23547]) ).
% 7.88/1.47  
% 7.88/1.47  
% 7.88/1.47  % SZS output end CNFRefutation for theBenchmark.p
% 7.88/1.47  
% 7.88/1.47  ------                               Statistics
% 7.88/1.47  
% 7.88/1.47  ------ General
% 7.88/1.47  
% 7.88/1.47  abstr_ref_over_cycles:                  0
% 7.88/1.47  abstr_ref_under_cycles:                 0
% 7.88/1.47  gc_basic_clause_elim:                   0
% 7.88/1.47  forced_gc_time:                         0
% 7.88/1.47  parsing_time:                           0.009
% 7.88/1.47  unif_index_cands_time:                  0.
% 7.88/1.47  unif_index_add_time:                    0.
% 7.88/1.47  orderings_time:                         0.
% 7.88/1.47  out_proof_time:                         0.014
% 7.88/1.47  total_time:                             0.802
% 7.88/1.47  num_of_symbols:                         45
% 7.88/1.47  num_of_terms:                           36312
% 7.88/1.47  
% 7.88/1.47  ------ Preprocessing
% 7.88/1.47  
% 7.88/1.47  num_of_splits:                          0
% 7.88/1.47  num_of_split_atoms:                     0
% 7.88/1.47  num_of_reused_defs:                     0
% 7.88/1.47  num_eq_ax_congr_red:                    4
% 7.88/1.47  num_of_sem_filtered_clauses:            1
% 7.88/1.47  num_of_subtypes:                        0
% 7.88/1.47  monotx_restored_types:                  0
% 7.88/1.47  sat_num_of_epr_types:                   0
% 7.88/1.47  sat_num_of_non_cyclic_types:            0
% 7.88/1.47  sat_guarded_non_collapsed_types:        0
% 7.88/1.47  num_pure_diseq_elim:                    0
% 7.88/1.47  simp_replaced_by:                       0
% 7.88/1.47  res_preprocessed:                       104
% 7.88/1.47  prep_upred:                             0
% 7.88/1.47  prep_unflattend:                        2
% 7.88/1.47  smt_new_axioms:                         0
% 7.88/1.47  pred_elim_cands:                        2
% 7.88/1.47  pred_elim:                              1
% 7.88/1.47  pred_elim_cl:                           1
% 7.88/1.47  pred_elim_cycles:                       3
% 7.88/1.47  merged_defs:                            0
% 7.88/1.47  merged_defs_ncl:                        0
% 7.88/1.47  bin_hyper_res:                          0
% 7.88/1.47  prep_cycles:                            4
% 7.88/1.47  pred_elim_time:                         0.
% 7.88/1.47  splitting_time:                         0.
% 7.88/1.47  sem_filter_time:                        0.
% 7.88/1.47  monotx_time:                            0.
% 7.88/1.47  subtype_inf_time:                       0.
% 7.88/1.47  
% 7.88/1.47  ------ Problem properties
% 7.88/1.47  
% 7.88/1.47  clauses:                                19
% 7.88/1.47  conjectures:                            1
% 7.88/1.47  epr:                                    0
% 7.88/1.47  horn:                                   19
% 7.88/1.47  ground:                                 1
% 7.88/1.47  unary:                                  6
% 7.88/1.47  binary:                                 8
% 7.88/1.47  lits:                                   39
% 7.88/1.47  lits_eq:                                13
% 7.88/1.47  fd_pure:                                0
% 7.88/1.47  fd_pseudo:                              0
% 7.88/1.47  fd_cond:                                0
% 7.88/1.47  fd_pseudo_cond:                         0
% 7.88/1.48  ac_symbols:                             0
% 7.88/1.48  
% 7.88/1.48  ------ Propositional Solver
% 7.88/1.48  
% 7.88/1.48  prop_solver_calls:                      33
% 7.88/1.48  prop_fast_solver_calls:                 860
% 7.88/1.48  smt_solver_calls:                       0
% 7.88/1.48  smt_fast_solver_calls:                  0
% 7.88/1.48  prop_num_of_clauses:                    7940
% 7.88/1.48  prop_preprocess_simplified:             12499
% 7.88/1.48  prop_fo_subsumed:                       17
% 7.88/1.48  prop_solver_time:                       0.
% 7.88/1.48  smt_solver_time:                        0.
% 7.88/1.48  smt_fast_solver_time:                   0.
% 7.88/1.48  prop_fast_solver_time:                  0.
% 7.88/1.48  prop_unsat_core_time:                   0.
% 7.88/1.48  
% 7.88/1.48  ------ QBF
% 7.88/1.48  
% 7.88/1.48  qbf_q_res:                              0
% 7.88/1.48  qbf_num_tautologies:                    0
% 7.88/1.48  qbf_prep_cycles:                        0
% 7.88/1.48  
% 7.88/1.48  ------ BMC1
% 7.88/1.48  
% 7.88/1.48  bmc1_current_bound:                     -1
% 7.88/1.48  bmc1_last_solved_bound:                 -1
% 7.88/1.48  bmc1_unsat_core_size:                   -1
% 7.88/1.48  bmc1_unsat_core_parents_size:           -1
% 7.88/1.48  bmc1_merge_next_fun:                    0
% 7.88/1.48  bmc1_unsat_core_clauses_time:           0.
% 7.88/1.48  
% 7.88/1.48  ------ Instantiation
% 7.88/1.48  
% 7.88/1.48  inst_num_of_clauses:                    2796
% 7.88/1.48  inst_num_in_passive:                    1528
% 7.88/1.48  inst_num_in_active:                     1035
% 7.88/1.48  inst_num_in_unprocessed:                233
% 7.88/1.48  inst_num_of_loops:                      1120
% 7.88/1.48  inst_num_of_learning_restarts:          0
% 7.88/1.48  inst_num_moves_active_passive:          81
% 7.88/1.48  inst_lit_activity:                      0
% 7.88/1.48  inst_lit_activity_moves:                0
% 7.88/1.48  inst_num_tautologies:                   0
% 7.88/1.48  inst_num_prop_implied:                  0
% 7.88/1.48  inst_num_existing_simplified:           0
% 7.88/1.48  inst_num_eq_res_simplified:             0
% 7.88/1.48  inst_num_child_elim:                    0
% 7.88/1.48  inst_num_of_dismatching_blockings:      490
% 7.88/1.48  inst_num_of_non_proper_insts:           2715
% 7.88/1.48  inst_num_of_duplicates:                 0
% 7.88/1.48  inst_inst_num_from_inst_to_res:         0
% 7.88/1.48  inst_dismatching_checking_time:         0.
% 7.88/1.48  
% 7.88/1.48  ------ Resolution
% 7.88/1.48  
% 7.88/1.48  res_num_of_clauses:                     0
% 7.88/1.48  res_num_in_passive:                     0
% 7.88/1.48  res_num_in_active:                      0
% 7.88/1.48  res_num_of_loops:                       108
% 7.88/1.48  res_forward_subset_subsumed:            648
% 7.88/1.48  res_backward_subset_subsumed:           2
% 7.88/1.48  res_forward_subsumed:                   0
% 7.88/1.48  res_backward_subsumed:                  0
% 7.88/1.48  res_forward_subsumption_resolution:     0
% 7.88/1.48  res_backward_subsumption_resolution:    0
% 7.88/1.48  res_clause_to_clause_subsumption:       6643
% 7.88/1.48  res_orphan_elimination:                 0
% 7.88/1.48  res_tautology_del:                      317
% 7.88/1.48  res_num_eq_res_simplified:              0
% 7.88/1.48  res_num_sel_changes:                    0
% 7.88/1.48  res_moves_from_active_to_pass:          0
% 7.88/1.48  
% 7.88/1.48  ------ Superposition
% 7.88/1.48  
% 7.88/1.48  sup_time_total:                         0.
% 7.88/1.48  sup_time_generating:                    0.
% 7.88/1.48  sup_time_sim_full:                      0.
% 7.88/1.48  sup_time_sim_immed:                     0.
% 7.88/1.48  
% 7.88/1.48  sup_num_of_clauses:                     1333
% 7.88/1.48  sup_num_in_active:                      153
% 7.88/1.48  sup_num_in_passive:                     1180
% 7.88/1.48  sup_num_of_loops:                       223
% 7.88/1.48  sup_fw_superposition:                   3388
% 7.88/1.48  sup_bw_superposition:                   3655
% 7.88/1.48  sup_immediate_simplified:               3931
% 7.88/1.48  sup_given_eliminated:                   2
% 7.88/1.48  comparisons_done:                       0
% 7.88/1.48  comparisons_avoided:                    0
% 7.88/1.48  
% 7.88/1.48  ------ Simplifications
% 7.88/1.48  
% 7.88/1.48  
% 7.88/1.48  sim_fw_subset_subsumed:                 51
% 7.88/1.48  sim_bw_subset_subsumed:                 78
% 7.88/1.48  sim_fw_subsumed:                        230
% 7.88/1.48  sim_bw_subsumed:                        4
% 7.88/1.48  sim_fw_subsumption_res:                 0
% 7.88/1.48  sim_bw_subsumption_res:                 0
% 7.88/1.48  sim_tautology_del:                      2
% 7.88/1.48  sim_eq_tautology_del:                   668
% 7.88/1.48  sim_eq_res_simp:                        0
% 7.88/1.48  sim_fw_demodulated:                     2574
% 7.88/1.48  sim_bw_demodulated:                     87
% 7.88/1.48  sim_light_normalised:                   2795
% 7.88/1.48  sim_joinable_taut:                      0
% 7.88/1.48  sim_joinable_simp:                      0
% 7.88/1.48  sim_ac_normalised:                      0
% 7.88/1.48  sim_smt_subsumption:                    0
% 7.88/1.48  
%------------------------------------------------------------------------------
