%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:50:01 EST 2020

% Result     : Theorem 39.67s
% Output     : CNFRefutation 39.67s
% Verified   : 
% Statistics : Number of formulae       :  204 (37462 expanded)
%              Number of clauses        :  147 (16997 expanded)
%              Number of leaves         :   17 (7243 expanded)
%              Depth                    :   34
%              Number of atoms          :  321 (57180 expanded)
%              Number of equality atoms :  229 (32266 expanded)
%              Maximal formula depth    :    8 (   2 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    8 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(pure_predicate_removal,[],[f18])).

fof(f59,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f21])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f12,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k5_relat_1(k6_relat_1(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f65,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f47,f43])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_relat_1(X1),k4_xboole_0(k1_relat_1(X1),X0)) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f57,f43])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f62,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f38,f43,f43])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f63,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f42,f43])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f56,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f52,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f34])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f69,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f39])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k8_relat_1(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f49,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f19,conjecture,(
    ! [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
    inference(negated_conjecture,[],[f19])).

fof(f33,plain,(
    ? [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) != k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
    inference(ennf_transformation,[],[f20])).

fof(f36,plain,
    ( ? [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) != k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))
   => k6_relat_1(k3_xboole_0(sK0,sK1)) != k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    k6_relat_1(k3_xboole_0(sK0,sK1)) != k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f33,f36])).

fof(f60,plain,(
    k6_relat_1(k3_xboole_0(sK0,sK1)) != k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f37])).

fof(f67,plain,(
    k6_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) != k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) ),
    inference(definition_unfolding,[],[f60,f43])).

cnf(c_18,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_529,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_536,plain,
    ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2179,plain,
    ( k5_relat_1(k6_relat_1(X0),k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(k6_relat_1(X0),X1),X2)
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_529,c_536])).

cnf(c_8644,plain,
    ( k5_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),X2) = k5_relat_1(k6_relat_1(X0),k5_relat_1(k6_relat_1(X1),X2))
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_529,c_2179])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X1,X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_538,plain,
    ( k5_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X1,X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1784,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k8_relat_1(X1,k6_relat_1(X0)) ),
    inference(superposition,[status(thm)],[c_529,c_538])).

cnf(c_8657,plain,
    ( k5_relat_1(k6_relat_1(X0),k5_relat_1(k6_relat_1(X1),X2)) = k5_relat_1(k8_relat_1(X1,k6_relat_1(X0)),X2)
    | v1_relat_1(X2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8644,c_1784])).

cnf(c_138742,plain,
    ( k5_relat_1(k6_relat_1(X0),k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) = k5_relat_1(k8_relat_1(X1,k6_relat_1(X0)),k6_relat_1(X2)) ),
    inference(superposition,[status(thm)],[c_529,c_8657])).

cnf(c_12,plain,
    ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_535,plain,
    ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2080,plain,
    ( r1_tarski(k8_relat_1(X0,k6_relat_1(X1)),k6_relat_1(X0)) = iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1784,c_535])).

cnf(c_20,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2822,plain,
    ( r1_tarski(k8_relat_1(X0,k6_relat_1(X1)),k6_relat_1(X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2080,c_20])).

cnf(c_11,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_14,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k6_relat_1(X1),X0) = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_533,plain,
    ( k5_relat_1(k6_relat_1(X0),X1) = X1
    | r1_tarski(k1_relat_1(X1),X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2259,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k6_relat_1(X1)
    | r1_tarski(X1,X0) != iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11,c_533])).

cnf(c_2260,plain,
    ( k8_relat_1(X0,k6_relat_1(X1)) = k6_relat_1(X0)
    | r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2259,c_1784])).

cnf(c_5636,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | k8_relat_1(X0,k6_relat_1(X1)) = k6_relat_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2260,c_20])).

cnf(c_5637,plain,
    ( k8_relat_1(X0,k6_relat_1(X1)) = k6_relat_1(X0)
    | r1_tarski(X0,X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_5636])).

cnf(c_5646,plain,
    ( k8_relat_1(k8_relat_1(X0,k6_relat_1(X1)),k6_relat_1(k6_relat_1(X0))) = k6_relat_1(k8_relat_1(X0,k6_relat_1(X1))) ),
    inference(superposition,[status(thm)],[c_2822,c_5637])).

cnf(c_17,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_530,plain,
    ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1546,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(superposition,[status(thm)],[c_529,c_530])).

cnf(c_1876,plain,
    ( k7_relat_1(k6_relat_1(X0),X1) = k8_relat_1(X0,k6_relat_1(X1)) ),
    inference(light_normalisation,[status(thm)],[c_1546,c_1784])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_539,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_16,plain,
    ( ~ v1_relat_1(X0)
    | k4_xboole_0(k1_relat_1(X0),k4_xboole_0(k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_531,plain,
    ( k4_xboole_0(k1_relat_1(X0),k4_xboole_0(k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_986,plain,
    ( k4_xboole_0(k1_relat_1(k6_relat_1(X0)),k4_xboole_0(k1_relat_1(k6_relat_1(X0)),X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(superposition,[status(thm)],[c_529,c_531])).

cnf(c_987,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(light_normalisation,[status(thm)],[c_986,c_11])).

cnf(c_0,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1119,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
    inference(demodulation,[status(thm)],[c_987,c_0])).

cnf(c_1787,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X1),X0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_539,c_1119])).

cnf(c_1884,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1876,c_1787])).

cnf(c_5677,plain,
    ( v1_relat_1(k1_relat_1(k6_relat_1(k8_relat_1(X0,k6_relat_1(X1))))) = iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5646,c_1884])).

cnf(c_5712,plain,
    ( v1_relat_1(k8_relat_1(X0,k6_relat_1(X1))) = iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5677,c_11])).

cnf(c_5909,plain,
    ( v1_relat_1(k8_relat_1(X0,k6_relat_1(X1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5712,c_20])).

cnf(c_5927,plain,
    ( k5_relat_1(k8_relat_1(X0,k6_relat_1(X1)),k6_relat_1(X2)) = k8_relat_1(X2,k8_relat_1(X0,k6_relat_1(X1))) ),
    inference(superposition,[status(thm)],[c_5909,c_538])).

cnf(c_5930,plain,
    ( k5_relat_1(k6_relat_1(X0),k8_relat_1(X1,k6_relat_1(X2))) = k7_relat_1(k8_relat_1(X1,k6_relat_1(X2)),X0) ),
    inference(superposition,[status(thm)],[c_5909,c_530])).

cnf(c_138876,plain,
    ( k7_relat_1(k8_relat_1(X0,k6_relat_1(X1)),X2) = k8_relat_1(X0,k8_relat_1(X1,k6_relat_1(X2))) ),
    inference(demodulation,[status(thm)],[c_138742,c_1784,c_5927,c_5930])).

cnf(c_4,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_540,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1120,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_987,c_540])).

cnf(c_1880,plain,
    ( r1_tarski(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))),X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1876,c_1120])).

cnf(c_2257,plain,
    ( k5_relat_1(k6_relat_1(X0),k8_relat_1(X0,k6_relat_1(X1))) = k8_relat_1(X0,k6_relat_1(X1))
    | v1_relat_1(k8_relat_1(X0,k6_relat_1(X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1880,c_533])).

cnf(c_5931,plain,
    ( k5_relat_1(k6_relat_1(X0),k8_relat_1(X0,k6_relat_1(X1))) = k8_relat_1(X0,k6_relat_1(X1)) ),
    inference(superposition,[status(thm)],[c_5909,c_2257])).

cnf(c_7091,plain,
    ( k7_relat_1(k8_relat_1(X0,k6_relat_1(X1)),X0) = k8_relat_1(X0,k6_relat_1(X1)) ),
    inference(superposition,[status(thm)],[c_5930,c_5931])).

cnf(c_140506,plain,
    ( k8_relat_1(X0,k8_relat_1(X1,k6_relat_1(X0))) = k8_relat_1(X0,k6_relat_1(X1)) ),
    inference(superposition,[status(thm)],[c_138876,c_7091])).

cnf(c_15,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_532,plain,
    ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1502,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(k2_relat_1(k6_relat_1(X0)))) = k6_relat_1(X0) ),
    inference(superposition,[status(thm)],[c_529,c_532])).

cnf(c_10,plain,
    ( k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1503,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X0)) = k6_relat_1(X0) ),
    inference(light_normalisation,[status(thm)],[c_1502,c_10])).

cnf(c_2081,plain,
    ( k8_relat_1(X0,k6_relat_1(X0)) = k6_relat_1(X0) ),
    inference(superposition,[status(thm)],[c_1784,c_1503])).

cnf(c_3,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_541,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1193,plain,
    ( k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
    inference(superposition,[status(thm)],[c_1119,c_987])).

cnf(c_1879,plain,
    ( k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))) = k1_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
    inference(demodulation,[status(thm)],[c_1876,c_1193])).

cnf(c_1887,plain,
    ( k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))) = k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))) ),
    inference(demodulation,[status(thm)],[c_1879,c_1876])).

cnf(c_2427,plain,
    ( k5_relat_1(k6_relat_1(X0),k8_relat_1(X1,k6_relat_1(X2))) = k8_relat_1(X1,k6_relat_1(X2))
    | r1_tarski(k1_relat_1(k8_relat_1(X2,k6_relat_1(X1))),X0) != iProver_top
    | v1_relat_1(k8_relat_1(X1,k6_relat_1(X2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1887,c_533])).

cnf(c_17219,plain,
    ( k7_relat_1(k8_relat_1(X0,k6_relat_1(X1)),X2) = k8_relat_1(X0,k6_relat_1(X1))
    | r1_tarski(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))),X2) != iProver_top
    | v1_relat_1(k8_relat_1(X0,k6_relat_1(X1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2427,c_5930])).

cnf(c_17221,plain,
    ( r1_tarski(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))),X2) != iProver_top
    | k7_relat_1(k8_relat_1(X0,k6_relat_1(X1)),X2) = k8_relat_1(X0,k6_relat_1(X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_17219,c_20,c_5712])).

cnf(c_17222,plain,
    ( k7_relat_1(k8_relat_1(X0,k6_relat_1(X1)),X2) = k8_relat_1(X0,k6_relat_1(X1))
    | r1_tarski(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))),X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_17221])).

cnf(c_17225,plain,
    ( k7_relat_1(k8_relat_1(X0,k6_relat_1(X1)),k1_relat_1(k8_relat_1(X1,k6_relat_1(X0)))) = k8_relat_1(X0,k6_relat_1(X1)) ),
    inference(superposition,[status(thm)],[c_541,c_17222])).

cnf(c_140509,plain,
    ( k8_relat_1(X0,k8_relat_1(X1,k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0)))))) = k8_relat_1(X0,k6_relat_1(X1)) ),
    inference(superposition,[status(thm)],[c_138876,c_17225])).

cnf(c_5643,plain,
    ( k8_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))),k6_relat_1(X0)) = k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))) ),
    inference(superposition,[status(thm)],[c_1880,c_5637])).

cnf(c_896,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_540])).

cnf(c_1118,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_987,c_896])).

cnf(c_1881,plain,
    ( r1_tarski(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))),X1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1876,c_1118])).

cnf(c_5644,plain,
    ( k8_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))),k6_relat_1(X1)) = k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))) ),
    inference(superposition,[status(thm)],[c_1881,c_5637])).

cnf(c_10771,plain,
    ( k6_relat_1(k1_relat_1(k8_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))),k6_relat_1(X0)))) = k8_relat_1(k1_relat_1(k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))))),k6_relat_1(X0)) ),
    inference(superposition,[status(thm)],[c_5643,c_5644])).

cnf(c_10839,plain,
    ( k1_relat_1(k8_relat_1(X0,k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0)))))) = k1_relat_1(k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))))) ),
    inference(superposition,[status(thm)],[c_5644,c_1887])).

cnf(c_9139,plain,
    ( k1_relat_1(k8_relat_1(X0,k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))))) = k1_relat_1(k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))))) ),
    inference(superposition,[status(thm)],[c_5643,c_1887])).

cnf(c_9147,plain,
    ( k1_relat_1(k8_relat_1(X0,k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))))) = k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))) ),
    inference(demodulation,[status(thm)],[c_9139,c_11])).

cnf(c_1882,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))) ),
    inference(demodulation,[status(thm)],[c_1876,c_987])).

cnf(c_2107,plain,
    ( k1_relat_1(k8_relat_1(X0,k6_relat_1(k4_xboole_0(X0,X1)))) = k4_xboole_0(X0,k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))) ),
    inference(superposition,[status(thm)],[c_1882,c_1882])).

cnf(c_2911,plain,
    ( k4_xboole_0(X0,k1_relat_1(k8_relat_1(X0,k6_relat_1(k4_xboole_0(X0,X1))))) = k1_relat_1(k8_relat_1(X0,k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))))) ),
    inference(superposition,[status(thm)],[c_2107,c_1882])).

cnf(c_3824,plain,
    ( k1_relat_1(k8_relat_1(X0,k6_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = k1_relat_1(k8_relat_1(X0,k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))))) ),
    inference(superposition,[status(thm)],[c_2911,c_2107])).

cnf(c_1885,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))) ),
    inference(demodulation,[status(thm)],[c_1876,c_1119])).

cnf(c_3825,plain,
    ( k1_relat_1(k8_relat_1(X0,k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0)))))) = k1_relat_1(k8_relat_1(X0,k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))))) ),
    inference(light_normalisation,[status(thm)],[c_3824,c_1885])).

cnf(c_10023,plain,
    ( k1_relat_1(k8_relat_1(X0,k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0)))))) = k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))) ),
    inference(demodulation,[status(thm)],[c_9147,c_3825])).

cnf(c_10846,plain,
    ( k1_relat_1(k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))))) = k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))) ),
    inference(light_normalisation,[status(thm)],[c_10839,c_10023])).

cnf(c_10905,plain,
    ( k6_relat_1(k1_relat_1(k8_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))),k6_relat_1(X0)))) = k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0)))) ),
    inference(demodulation,[status(thm)],[c_10771,c_5644,c_10846])).

cnf(c_10906,plain,
    ( k6_relat_1(k1_relat_1(k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))))) = k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0)))) ),
    inference(light_normalisation,[status(thm)],[c_10905,c_5643])).

cnf(c_10907,plain,
    ( k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))) = k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0)))) ),
    inference(demodulation,[status(thm)],[c_10906,c_11])).

cnf(c_8,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k8_relat_1(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_537,plain,
    ( k8_relat_1(X0,X1) = X1
    | r1_tarski(k2_relat_1(X1),X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2250,plain,
    ( k8_relat_1(X0,k6_relat_1(X1)) = k6_relat_1(X1)
    | r1_tarski(X1,X0) != iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_10,c_537])).

cnf(c_2367,plain,
    ( k8_relat_1(X0,k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))))) = k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))))
    | v1_relat_1(k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1881,c_2250])).

cnf(c_15145,plain,
    ( k8_relat_1(X0,k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))))) = k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0)))) ),
    inference(superposition,[status(thm)],[c_529,c_2367])).

cnf(c_17421,plain,
    ( k8_relat_1(X0,k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))))) = k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0)))) ),
    inference(superposition,[status(thm)],[c_10907,c_15145])).

cnf(c_140513,plain,
    ( k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))) = k8_relat_1(X1,k6_relat_1(X0)) ),
    inference(demodulation,[status(thm)],[c_140509,c_17421])).

cnf(c_9068,plain,
    ( k8_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))),k6_relat_1(X1)) = k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0)))) ),
    inference(superposition,[status(thm)],[c_1887,c_5643])).

cnf(c_2249,plain,
    ( k8_relat_1(k2_relat_1(X0),X0) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_541,c_537])).

cnf(c_5925,plain,
    ( k8_relat_1(k2_relat_1(k8_relat_1(X0,k6_relat_1(X1))),k8_relat_1(X0,k6_relat_1(X1))) = k8_relat_1(X0,k6_relat_1(X1)) ),
    inference(superposition,[status(thm)],[c_5909,c_2249])).

cnf(c_14537,plain,
    ( k8_relat_1(k2_relat_1(k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))))),k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))))) = k8_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))),k6_relat_1(X0)) ),
    inference(superposition,[status(thm)],[c_9068,c_5925])).

cnf(c_14650,plain,
    ( k8_relat_1(k2_relat_1(k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))))),k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))))) = k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))) ),
    inference(demodulation,[status(thm)],[c_14537,c_9068])).

cnf(c_11375,plain,
    ( k2_relat_1(k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))))) = k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))) ),
    inference(superposition,[status(thm)],[c_10907,c_10])).

cnf(c_14651,plain,
    ( k8_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))),k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))))) = k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0)))) ),
    inference(light_normalisation,[status(thm)],[c_14650,c_11375])).

cnf(c_5641,plain,
    ( k8_relat_1(k5_relat_1(k6_relat_1(X0),X1),k6_relat_1(X1)) = k6_relat_1(k5_relat_1(k6_relat_1(X0),X1))
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_535,c_5637])).

cnf(c_7807,plain,
    ( k8_relat_1(k5_relat_1(k6_relat_1(X0),k8_relat_1(X1,k6_relat_1(X2))),k6_relat_1(k8_relat_1(X1,k6_relat_1(X2)))) = k6_relat_1(k5_relat_1(k6_relat_1(X0),k8_relat_1(X1,k6_relat_1(X2)))) ),
    inference(superposition,[status(thm)],[c_5909,c_5641])).

cnf(c_7817,plain,
    ( k8_relat_1(k7_relat_1(k8_relat_1(X0,k6_relat_1(X1)),X2),k6_relat_1(k8_relat_1(X0,k6_relat_1(X1)))) = k6_relat_1(k7_relat_1(k8_relat_1(X0,k6_relat_1(X1)),X2)) ),
    inference(light_normalisation,[status(thm)],[c_7807,c_5930])).

cnf(c_110055,plain,
    ( k8_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))),X2),k6_relat_1(k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))))) = k6_relat_1(k7_relat_1(k8_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))),k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))))),X2)) ),
    inference(superposition,[status(thm)],[c_14651,c_7817])).

cnf(c_11369,plain,
    ( k7_relat_1(k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))),X2) = k8_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))),k6_relat_1(X2)) ),
    inference(superposition,[status(thm)],[c_10907,c_1876])).

cnf(c_110975,plain,
    ( k8_relat_1(k8_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))),k6_relat_1(X2)),k6_relat_1(k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0)))))) = k6_relat_1(k7_relat_1(k8_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))),k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))))),X2)) ),
    inference(light_normalisation,[status(thm)],[c_110055,c_11369])).

cnf(c_29171,plain,
    ( k8_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))),k6_relat_1(X2)) = k8_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))),k6_relat_1(X2)) ),
    inference(superposition,[status(thm)],[c_11369,c_1876])).

cnf(c_40814,plain,
    ( k8_relat_1(k8_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))),k6_relat_1(X2)),k6_relat_1(k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0)))))) = k6_relat_1(k8_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))),k6_relat_1(X2))) ),
    inference(superposition,[status(thm)],[c_29171,c_5646])).

cnf(c_110976,plain,
    ( k6_relat_1(k8_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))),k6_relat_1(X2))) = k6_relat_1(k8_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))),k6_relat_1(X2))) ),
    inference(demodulation,[status(thm)],[c_110975,c_11369,c_14651,c_40814])).

cnf(c_117063,plain,
    ( k1_relat_1(k6_relat_1(k8_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))),k6_relat_1(X2)))) = k8_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))),k6_relat_1(X2)) ),
    inference(superposition,[status(thm)],[c_110976,c_11])).

cnf(c_142003,plain,
    ( k1_relat_1(k6_relat_1(k8_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))),k8_relat_1(X2,k6_relat_1(X3))))) = k8_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))),k6_relat_1(k1_relat_1(k8_relat_1(X3,k6_relat_1(X2))))) ),
    inference(superposition,[status(thm)],[c_140513,c_117063])).

cnf(c_141795,plain,
    ( k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))) = k2_relat_1(k8_relat_1(X1,k6_relat_1(X0))) ),
    inference(superposition,[status(thm)],[c_140513,c_10])).

cnf(c_142208,plain,
    ( k1_relat_1(k6_relat_1(k8_relat_1(k2_relat_1(k8_relat_1(X0,k6_relat_1(X1))),k8_relat_1(X2,k6_relat_1(X3))))) = k8_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))),k6_relat_1(k1_relat_1(k8_relat_1(X3,k6_relat_1(X2))))) ),
    inference(light_normalisation,[status(thm)],[c_142003,c_141795])).

cnf(c_10758,plain,
    ( k8_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))),k6_relat_1(X0)) = k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0)))) ),
    inference(superposition,[status(thm)],[c_1887,c_5644])).

cnf(c_140928,plain,
    ( k8_relat_1(X0,k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))))) = k8_relat_1(X0,k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))))) ),
    inference(superposition,[status(thm)],[c_10758,c_140506])).

cnf(c_2366,plain,
    ( k8_relat_1(X0,k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))))) = k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))))
    | v1_relat_1(k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1880,c_2250])).

cnf(c_13242,plain,
    ( k8_relat_1(X0,k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))))) = k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))) ),
    inference(superposition,[status(thm)],[c_529,c_2366])).

cnf(c_15348,plain,
    ( k8_relat_1(X0,k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))))) = k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))) ),
    inference(superposition,[status(thm)],[c_10907,c_13242])).

cnf(c_141001,plain,
    ( k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))) = k8_relat_1(X0,k6_relat_1(X1)) ),
    inference(light_normalisation,[status(thm)],[c_140928,c_15348,c_17421,c_140513])).

cnf(c_142209,plain,
    ( k8_relat_1(k2_relat_1(k8_relat_1(X0,k6_relat_1(X1))),k8_relat_1(X2,k6_relat_1(X3))) = k8_relat_1(k2_relat_1(k8_relat_1(X1,k6_relat_1(X0))),k8_relat_1(X3,k6_relat_1(X2))) ),
    inference(demodulation,[status(thm)],[c_142208,c_11,c_141001,c_141795])).

cnf(c_142021,plain,
    ( k8_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))),k6_relat_1(k1_relat_1(k8_relat_1(X2,k6_relat_1(X3))))) = k8_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))),k8_relat_1(X3,k6_relat_1(X2))) ),
    inference(superposition,[status(thm)],[c_140513,c_29171])).

cnf(c_142174,plain,
    ( k8_relat_1(k2_relat_1(k8_relat_1(X0,k6_relat_1(X1))),k6_relat_1(k1_relat_1(k8_relat_1(X2,k6_relat_1(X3))))) = k8_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))),k8_relat_1(X3,k6_relat_1(X2))) ),
    inference(light_normalisation,[status(thm)],[c_142021,c_141795])).

cnf(c_141269,plain,
    ( k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))) = k2_relat_1(k8_relat_1(X0,k6_relat_1(X1))) ),
    inference(demodulation,[status(thm)],[c_140513,c_11375])).

cnf(c_11442,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X2))))) = k8_relat_1(k1_relat_1(k8_relat_1(X2,k6_relat_1(X1))),k6_relat_1(X0)) ),
    inference(superposition,[status(thm)],[c_10907,c_1784])).

cnf(c_141320,plain,
    ( k8_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))),k6_relat_1(X2)) = k5_relat_1(k6_relat_1(X2),k8_relat_1(X0,k6_relat_1(X1))) ),
    inference(demodulation,[status(thm)],[c_140513,c_11442])).

cnf(c_140308,plain,
    ( k5_relat_1(k6_relat_1(X0),k8_relat_1(X1,k6_relat_1(X2))) = k8_relat_1(X1,k8_relat_1(X2,k6_relat_1(X0))) ),
    inference(demodulation,[status(thm)],[c_138876,c_5930])).

cnf(c_141321,plain,
    ( k8_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))),k6_relat_1(X2)) = k8_relat_1(X0,k8_relat_1(X1,k6_relat_1(X2))) ),
    inference(demodulation,[status(thm)],[c_141320,c_140308])).

cnf(c_141348,plain,
    ( k8_relat_1(k2_relat_1(k8_relat_1(X0,k6_relat_1(X1))),k6_relat_1(X2)) = k8_relat_1(X0,k8_relat_1(X1,k6_relat_1(X2))) ),
    inference(demodulation,[status(thm)],[c_141269,c_141321])).

cnf(c_142175,plain,
    ( k8_relat_1(k2_relat_1(k8_relat_1(X0,k6_relat_1(X1))),k8_relat_1(X2,k6_relat_1(X3))) = k8_relat_1(X1,k8_relat_1(X0,k8_relat_1(X3,k6_relat_1(X2)))) ),
    inference(demodulation,[status(thm)],[c_142174,c_141001,c_141348,c_141795])).

cnf(c_143794,plain,
    ( k8_relat_1(k2_relat_1(k8_relat_1(X0,k6_relat_1(X1))),k8_relat_1(X2,k6_relat_1(X3))) = k8_relat_1(X0,k8_relat_1(X1,k8_relat_1(X2,k6_relat_1(X3)))) ),
    inference(light_normalisation,[status(thm)],[c_142209,c_142175])).

cnf(c_143798,plain,
    ( k8_relat_1(X0,k8_relat_1(X0,k8_relat_1(X1,k6_relat_1(X2)))) = k8_relat_1(k2_relat_1(k6_relat_1(X0)),k8_relat_1(X1,k6_relat_1(X2))) ),
    inference(superposition,[status(thm)],[c_2081,c_143794])).

cnf(c_143911,plain,
    ( k8_relat_1(X0,k8_relat_1(X0,k8_relat_1(X1,k6_relat_1(X2)))) = k8_relat_1(X0,k8_relat_1(X1,k6_relat_1(X2))) ),
    inference(light_normalisation,[status(thm)],[c_143798,c_10])).

cnf(c_144187,plain,
    ( k8_relat_1(X0,k8_relat_1(X0,k6_relat_1(X1))) = k8_relat_1(X0,k8_relat_1(X1,k6_relat_1(X0))) ),
    inference(superposition,[status(thm)],[c_140506,c_143911])).

cnf(c_140442,plain,
    ( k8_relat_1(X0,k8_relat_1(X0,k6_relat_1(X1))) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(superposition,[status(thm)],[c_2081,c_138876])).

cnf(c_140564,plain,
    ( k8_relat_1(X0,k8_relat_1(X0,k6_relat_1(X1))) = k8_relat_1(X0,k6_relat_1(X1)) ),
    inference(light_normalisation,[status(thm)],[c_140442,c_1876])).

cnf(c_141263,plain,
    ( k8_relat_1(X0,k8_relat_1(X1,k6_relat_1(X0))) = k8_relat_1(X1,k6_relat_1(X0)) ),
    inference(demodulation,[status(thm)],[c_140513,c_13242])).

cnf(c_144236,plain,
    ( k8_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X1,k6_relat_1(X0)) ),
    inference(light_normalisation,[status(thm)],[c_144187,c_140564,c_141263])).

cnf(c_19,negated_conjecture,
    ( k6_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) != k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1122,plain,
    ( k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(sK0),sK1))) != k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) ),
    inference(demodulation,[status(thm)],[c_987,c_19])).

cnf(c_1878,plain,
    ( k6_relat_1(k1_relat_1(k8_relat_1(sK0,k6_relat_1(sK1)))) != k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) ),
    inference(demodulation,[status(thm)],[c_1876,c_1122])).

cnf(c_1888,plain,
    ( k6_relat_1(k1_relat_1(k8_relat_1(sK0,k6_relat_1(sK1)))) != k8_relat_1(sK0,k6_relat_1(sK1)) ),
    inference(demodulation,[status(thm)],[c_1878,c_1784])).

cnf(c_141184,plain,
    ( k8_relat_1(sK1,k6_relat_1(sK0)) != k8_relat_1(sK0,k6_relat_1(sK1)) ),
    inference(demodulation,[status(thm)],[c_140513,c_1888])).

cnf(c_144577,plain,
    ( k8_relat_1(sK0,k6_relat_1(sK1)) != k8_relat_1(sK0,k6_relat_1(sK1)) ),
    inference(demodulation,[status(thm)],[c_144236,c_141184])).

cnf(c_144583,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_144577])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n023.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 12:06:51 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 39.67/5.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 39.67/5.49  
% 39.67/5.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 39.67/5.49  
% 39.67/5.49  ------  iProver source info
% 39.67/5.49  
% 39.67/5.49  git: date: 2020-06-30 10:37:57 +0100
% 39.67/5.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 39.67/5.49  git: non_committed_changes: false
% 39.67/5.49  git: last_make_outside_of_git: false
% 39.67/5.49  
% 39.67/5.49  ------ 
% 39.67/5.49  
% 39.67/5.49  ------ Input Options
% 39.67/5.49  
% 39.67/5.49  --out_options                           all
% 39.67/5.49  --tptp_safe_out                         true
% 39.67/5.49  --problem_path                          ""
% 39.67/5.49  --include_path                          ""
% 39.67/5.49  --clausifier                            res/vclausify_rel
% 39.67/5.49  --clausifier_options                    ""
% 39.67/5.49  --stdin                                 false
% 39.67/5.49  --stats_out                             all
% 39.67/5.49  
% 39.67/5.49  ------ General Options
% 39.67/5.49  
% 39.67/5.49  --fof                                   false
% 39.67/5.49  --time_out_real                         305.
% 39.67/5.49  --time_out_virtual                      -1.
% 39.67/5.49  --symbol_type_check                     false
% 39.67/5.49  --clausify_out                          false
% 39.67/5.49  --sig_cnt_out                           false
% 39.67/5.49  --trig_cnt_out                          false
% 39.67/5.49  --trig_cnt_out_tolerance                1.
% 39.67/5.49  --trig_cnt_out_sk_spl                   false
% 39.67/5.49  --abstr_cl_out                          false
% 39.67/5.49  
% 39.67/5.49  ------ Global Options
% 39.67/5.49  
% 39.67/5.49  --schedule                              default
% 39.67/5.49  --add_important_lit                     false
% 39.67/5.49  --prop_solver_per_cl                    1000
% 39.67/5.49  --min_unsat_core                        false
% 39.67/5.49  --soft_assumptions                      false
% 39.67/5.49  --soft_lemma_size                       3
% 39.67/5.49  --prop_impl_unit_size                   0
% 39.67/5.49  --prop_impl_unit                        []
% 39.67/5.49  --share_sel_clauses                     true
% 39.67/5.49  --reset_solvers                         false
% 39.67/5.49  --bc_imp_inh                            [conj_cone]
% 39.67/5.49  --conj_cone_tolerance                   3.
% 39.67/5.49  --extra_neg_conj                        none
% 39.67/5.49  --large_theory_mode                     true
% 39.67/5.49  --prolific_symb_bound                   200
% 39.67/5.49  --lt_threshold                          2000
% 39.67/5.49  --clause_weak_htbl                      true
% 39.67/5.49  --gc_record_bc_elim                     false
% 39.67/5.49  
% 39.67/5.49  ------ Preprocessing Options
% 39.67/5.49  
% 39.67/5.49  --preprocessing_flag                    true
% 39.67/5.49  --time_out_prep_mult                    0.1
% 39.67/5.49  --splitting_mode                        input
% 39.67/5.49  --splitting_grd                         true
% 39.67/5.49  --splitting_cvd                         false
% 39.67/5.49  --splitting_cvd_svl                     false
% 39.67/5.49  --splitting_nvd                         32
% 39.67/5.49  --sub_typing                            true
% 39.67/5.49  --prep_gs_sim                           true
% 39.67/5.49  --prep_unflatten                        true
% 39.67/5.49  --prep_res_sim                          true
% 39.67/5.49  --prep_upred                            true
% 39.67/5.49  --prep_sem_filter                       exhaustive
% 39.67/5.49  --prep_sem_filter_out                   false
% 39.67/5.49  --pred_elim                             true
% 39.67/5.49  --res_sim_input                         true
% 39.67/5.49  --eq_ax_congr_red                       true
% 39.67/5.49  --pure_diseq_elim                       true
% 39.67/5.49  --brand_transform                       false
% 39.67/5.49  --non_eq_to_eq                          false
% 39.67/5.49  --prep_def_merge                        true
% 39.67/5.49  --prep_def_merge_prop_impl              false
% 39.67/5.49  --prep_def_merge_mbd                    true
% 39.67/5.49  --prep_def_merge_tr_red                 false
% 39.67/5.49  --prep_def_merge_tr_cl                  false
% 39.67/5.49  --smt_preprocessing                     true
% 39.67/5.49  --smt_ac_axioms                         fast
% 39.67/5.49  --preprocessed_out                      false
% 39.67/5.49  --preprocessed_stats                    false
% 39.67/5.49  
% 39.67/5.49  ------ Abstraction refinement Options
% 39.67/5.49  
% 39.67/5.49  --abstr_ref                             []
% 39.67/5.49  --abstr_ref_prep                        false
% 39.67/5.49  --abstr_ref_until_sat                   false
% 39.67/5.49  --abstr_ref_sig_restrict                funpre
% 39.67/5.49  --abstr_ref_af_restrict_to_split_sk     false
% 39.67/5.49  --abstr_ref_under                       []
% 39.67/5.49  
% 39.67/5.49  ------ SAT Options
% 39.67/5.49  
% 39.67/5.49  --sat_mode                              false
% 39.67/5.49  --sat_fm_restart_options                ""
% 39.67/5.49  --sat_gr_def                            false
% 39.67/5.49  --sat_epr_types                         true
% 39.67/5.49  --sat_non_cyclic_types                  false
% 39.67/5.49  --sat_finite_models                     false
% 39.67/5.49  --sat_fm_lemmas                         false
% 39.67/5.49  --sat_fm_prep                           false
% 39.67/5.49  --sat_fm_uc_incr                        true
% 39.67/5.49  --sat_out_model                         small
% 39.67/5.49  --sat_out_clauses                       false
% 39.67/5.49  
% 39.67/5.49  ------ QBF Options
% 39.67/5.49  
% 39.67/5.49  --qbf_mode                              false
% 39.67/5.49  --qbf_elim_univ                         false
% 39.67/5.49  --qbf_dom_inst                          none
% 39.67/5.49  --qbf_dom_pre_inst                      false
% 39.67/5.49  --qbf_sk_in                             false
% 39.67/5.49  --qbf_pred_elim                         true
% 39.67/5.49  --qbf_split                             512
% 39.67/5.49  
% 39.67/5.49  ------ BMC1 Options
% 39.67/5.49  
% 39.67/5.49  --bmc1_incremental                      false
% 39.67/5.49  --bmc1_axioms                           reachable_all
% 39.67/5.49  --bmc1_min_bound                        0
% 39.67/5.49  --bmc1_max_bound                        -1
% 39.67/5.49  --bmc1_max_bound_default                -1
% 39.67/5.49  --bmc1_symbol_reachability              true
% 39.67/5.49  --bmc1_property_lemmas                  false
% 39.67/5.49  --bmc1_k_induction                      false
% 39.67/5.49  --bmc1_non_equiv_states                 false
% 39.67/5.49  --bmc1_deadlock                         false
% 39.67/5.49  --bmc1_ucm                              false
% 39.67/5.49  --bmc1_add_unsat_core                   none
% 39.67/5.49  --bmc1_unsat_core_children              false
% 39.67/5.49  --bmc1_unsat_core_extrapolate_axioms    false
% 39.67/5.49  --bmc1_out_stat                         full
% 39.67/5.49  --bmc1_ground_init                      false
% 39.67/5.49  --bmc1_pre_inst_next_state              false
% 39.67/5.49  --bmc1_pre_inst_state                   false
% 39.67/5.49  --bmc1_pre_inst_reach_state             false
% 39.67/5.49  --bmc1_out_unsat_core                   false
% 39.67/5.49  --bmc1_aig_witness_out                  false
% 39.67/5.49  --bmc1_verbose                          false
% 39.67/5.49  --bmc1_dump_clauses_tptp                false
% 39.67/5.49  --bmc1_dump_unsat_core_tptp             false
% 39.67/5.49  --bmc1_dump_file                        -
% 39.67/5.49  --bmc1_ucm_expand_uc_limit              128
% 39.67/5.49  --bmc1_ucm_n_expand_iterations          6
% 39.67/5.49  --bmc1_ucm_extend_mode                  1
% 39.67/5.49  --bmc1_ucm_init_mode                    2
% 39.67/5.49  --bmc1_ucm_cone_mode                    none
% 39.67/5.49  --bmc1_ucm_reduced_relation_type        0
% 39.67/5.49  --bmc1_ucm_relax_model                  4
% 39.67/5.49  --bmc1_ucm_full_tr_after_sat            true
% 39.67/5.49  --bmc1_ucm_expand_neg_assumptions       false
% 39.67/5.49  --bmc1_ucm_layered_model                none
% 39.67/5.49  --bmc1_ucm_max_lemma_size               10
% 39.67/5.49  
% 39.67/5.49  ------ AIG Options
% 39.67/5.49  
% 39.67/5.49  --aig_mode                              false
% 39.67/5.49  
% 39.67/5.49  ------ Instantiation Options
% 39.67/5.49  
% 39.67/5.49  --instantiation_flag                    true
% 39.67/5.49  --inst_sos_flag                         true
% 39.67/5.49  --inst_sos_phase                        true
% 39.67/5.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 39.67/5.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 39.67/5.49  --inst_lit_sel_side                     num_symb
% 39.67/5.49  --inst_solver_per_active                1400
% 39.67/5.49  --inst_solver_calls_frac                1.
% 39.67/5.49  --inst_passive_queue_type               priority_queues
% 39.67/5.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 39.67/5.49  --inst_passive_queues_freq              [25;2]
% 39.67/5.49  --inst_dismatching                      true
% 39.67/5.49  --inst_eager_unprocessed_to_passive     true
% 39.67/5.49  --inst_prop_sim_given                   true
% 39.67/5.49  --inst_prop_sim_new                     false
% 39.67/5.49  --inst_subs_new                         false
% 39.67/5.49  --inst_eq_res_simp                      false
% 39.67/5.49  --inst_subs_given                       false
% 39.67/5.49  --inst_orphan_elimination               true
% 39.67/5.49  --inst_learning_loop_flag               true
% 39.67/5.49  --inst_learning_start                   3000
% 39.67/5.49  --inst_learning_factor                  2
% 39.67/5.49  --inst_start_prop_sim_after_learn       3
% 39.67/5.49  --inst_sel_renew                        solver
% 39.67/5.49  --inst_lit_activity_flag                true
% 39.67/5.49  --inst_restr_to_given                   false
% 39.67/5.49  --inst_activity_threshold               500
% 39.67/5.49  --inst_out_proof                        true
% 39.67/5.49  
% 39.67/5.49  ------ Resolution Options
% 39.67/5.49  
% 39.67/5.49  --resolution_flag                       true
% 39.67/5.49  --res_lit_sel                           adaptive
% 39.67/5.49  --res_lit_sel_side                      none
% 39.67/5.49  --res_ordering                          kbo
% 39.67/5.49  --res_to_prop_solver                    active
% 39.67/5.49  --res_prop_simpl_new                    false
% 39.67/5.49  --res_prop_simpl_given                  true
% 39.67/5.49  --res_passive_queue_type                priority_queues
% 39.67/5.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 39.67/5.49  --res_passive_queues_freq               [15;5]
% 39.67/5.49  --res_forward_subs                      full
% 39.67/5.49  --res_backward_subs                     full
% 39.67/5.49  --res_forward_subs_resolution           true
% 39.67/5.49  --res_backward_subs_resolution          true
% 39.67/5.49  --res_orphan_elimination                true
% 39.67/5.49  --res_time_limit                        2.
% 39.67/5.49  --res_out_proof                         true
% 39.67/5.49  
% 39.67/5.49  ------ Superposition Options
% 39.67/5.49  
% 39.67/5.49  --superposition_flag                    true
% 39.67/5.49  --sup_passive_queue_type                priority_queues
% 39.67/5.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 39.67/5.49  --sup_passive_queues_freq               [8;1;4]
% 39.67/5.49  --demod_completeness_check              fast
% 39.67/5.49  --demod_use_ground                      true
% 39.67/5.49  --sup_to_prop_solver                    passive
% 39.67/5.49  --sup_prop_simpl_new                    true
% 39.67/5.49  --sup_prop_simpl_given                  true
% 39.67/5.49  --sup_fun_splitting                     true
% 39.67/5.49  --sup_smt_interval                      50000
% 39.67/5.49  
% 39.67/5.49  ------ Superposition Simplification Setup
% 39.67/5.49  
% 39.67/5.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 39.67/5.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 39.67/5.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 39.67/5.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 39.67/5.49  --sup_full_triv                         [TrivRules;PropSubs]
% 39.67/5.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 39.67/5.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 39.67/5.49  --sup_immed_triv                        [TrivRules]
% 39.67/5.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 39.67/5.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 39.67/5.49  --sup_immed_bw_main                     []
% 39.67/5.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 39.67/5.49  --sup_input_triv                        [Unflattening;TrivRules]
% 39.67/5.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 39.67/5.49  --sup_input_bw                          []
% 39.67/5.49  
% 39.67/5.49  ------ Combination Options
% 39.67/5.49  
% 39.67/5.49  --comb_res_mult                         3
% 39.67/5.49  --comb_sup_mult                         2
% 39.67/5.49  --comb_inst_mult                        10
% 39.67/5.49  
% 39.67/5.49  ------ Debug Options
% 39.67/5.49  
% 39.67/5.49  --dbg_backtrace                         false
% 39.67/5.49  --dbg_dump_prop_clauses                 false
% 39.67/5.49  --dbg_dump_prop_clauses_file            -
% 39.67/5.49  --dbg_out_stat                          false
% 39.67/5.49  ------ Parsing...
% 39.67/5.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 39.67/5.49  
% 39.67/5.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 39.67/5.49  
% 39.67/5.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 39.67/5.49  
% 39.67/5.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 39.67/5.49  ------ Proving...
% 39.67/5.49  ------ Problem Properties 
% 39.67/5.49  
% 39.67/5.49  
% 39.67/5.49  clauses                                 19
% 39.67/5.49  conjectures                             1
% 39.67/5.49  EPR                                     2
% 39.67/5.49  Horn                                    19
% 39.67/5.49  unary                                   8
% 39.67/5.49  binary                                  7
% 39.67/5.49  lits                                    35
% 39.67/5.49  lits eq                                 13
% 39.67/5.49  fd_pure                                 0
% 39.67/5.49  fd_pseudo                               0
% 39.67/5.49  fd_cond                                 0
% 39.67/5.49  fd_pseudo_cond                          1
% 39.67/5.49  AC symbols                              0
% 39.67/5.49  
% 39.67/5.49  ------ Schedule dynamic 5 is on 
% 39.67/5.49  
% 39.67/5.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 39.67/5.49  
% 39.67/5.49  
% 39.67/5.49  ------ 
% 39.67/5.49  Current options:
% 39.67/5.49  ------ 
% 39.67/5.49  
% 39.67/5.49  ------ Input Options
% 39.67/5.49  
% 39.67/5.49  --out_options                           all
% 39.67/5.49  --tptp_safe_out                         true
% 39.67/5.49  --problem_path                          ""
% 39.67/5.49  --include_path                          ""
% 39.67/5.49  --clausifier                            res/vclausify_rel
% 39.67/5.49  --clausifier_options                    ""
% 39.67/5.49  --stdin                                 false
% 39.67/5.49  --stats_out                             all
% 39.67/5.49  
% 39.67/5.49  ------ General Options
% 39.67/5.49  
% 39.67/5.49  --fof                                   false
% 39.67/5.49  --time_out_real                         305.
% 39.67/5.49  --time_out_virtual                      -1.
% 39.67/5.49  --symbol_type_check                     false
% 39.67/5.49  --clausify_out                          false
% 39.67/5.49  --sig_cnt_out                           false
% 39.67/5.49  --trig_cnt_out                          false
% 39.67/5.49  --trig_cnt_out_tolerance                1.
% 39.67/5.49  --trig_cnt_out_sk_spl                   false
% 39.67/5.49  --abstr_cl_out                          false
% 39.67/5.49  
% 39.67/5.49  ------ Global Options
% 39.67/5.49  
% 39.67/5.49  --schedule                              default
% 39.67/5.49  --add_important_lit                     false
% 39.67/5.49  --prop_solver_per_cl                    1000
% 39.67/5.49  --min_unsat_core                        false
% 39.67/5.49  --soft_assumptions                      false
% 39.67/5.49  --soft_lemma_size                       3
% 39.67/5.49  --prop_impl_unit_size                   0
% 39.67/5.49  --prop_impl_unit                        []
% 39.67/5.49  --share_sel_clauses                     true
% 39.67/5.49  --reset_solvers                         false
% 39.67/5.49  --bc_imp_inh                            [conj_cone]
% 39.67/5.49  --conj_cone_tolerance                   3.
% 39.67/5.49  --extra_neg_conj                        none
% 39.67/5.49  --large_theory_mode                     true
% 39.67/5.49  --prolific_symb_bound                   200
% 39.67/5.49  --lt_threshold                          2000
% 39.67/5.49  --clause_weak_htbl                      true
% 39.67/5.49  --gc_record_bc_elim                     false
% 39.67/5.49  
% 39.67/5.49  ------ Preprocessing Options
% 39.67/5.49  
% 39.67/5.49  --preprocessing_flag                    true
% 39.67/5.49  --time_out_prep_mult                    0.1
% 39.67/5.49  --splitting_mode                        input
% 39.67/5.49  --splitting_grd                         true
% 39.67/5.49  --splitting_cvd                         false
% 39.67/5.49  --splitting_cvd_svl                     false
% 39.67/5.49  --splitting_nvd                         32
% 39.67/5.49  --sub_typing                            true
% 39.67/5.49  --prep_gs_sim                           true
% 39.67/5.49  --prep_unflatten                        true
% 39.67/5.49  --prep_res_sim                          true
% 39.67/5.49  --prep_upred                            true
% 39.67/5.49  --prep_sem_filter                       exhaustive
% 39.67/5.49  --prep_sem_filter_out                   false
% 39.67/5.49  --pred_elim                             true
% 39.67/5.49  --res_sim_input                         true
% 39.67/5.49  --eq_ax_congr_red                       true
% 39.67/5.49  --pure_diseq_elim                       true
% 39.67/5.49  --brand_transform                       false
% 39.67/5.49  --non_eq_to_eq                          false
% 39.67/5.49  --prep_def_merge                        true
% 39.67/5.49  --prep_def_merge_prop_impl              false
% 39.67/5.49  --prep_def_merge_mbd                    true
% 39.67/5.49  --prep_def_merge_tr_red                 false
% 39.67/5.49  --prep_def_merge_tr_cl                  false
% 39.67/5.49  --smt_preprocessing                     true
% 39.67/5.49  --smt_ac_axioms                         fast
% 39.67/5.49  --preprocessed_out                      false
% 39.67/5.49  --preprocessed_stats                    false
% 39.67/5.49  
% 39.67/5.49  ------ Abstraction refinement Options
% 39.67/5.49  
% 39.67/5.49  --abstr_ref                             []
% 39.67/5.49  --abstr_ref_prep                        false
% 39.67/5.49  --abstr_ref_until_sat                   false
% 39.67/5.49  --abstr_ref_sig_restrict                funpre
% 39.67/5.49  --abstr_ref_af_restrict_to_split_sk     false
% 39.67/5.49  --abstr_ref_under                       []
% 39.67/5.49  
% 39.67/5.49  ------ SAT Options
% 39.67/5.49  
% 39.67/5.49  --sat_mode                              false
% 39.67/5.49  --sat_fm_restart_options                ""
% 39.67/5.49  --sat_gr_def                            false
% 39.67/5.49  --sat_epr_types                         true
% 39.67/5.49  --sat_non_cyclic_types                  false
% 39.67/5.49  --sat_finite_models                     false
% 39.67/5.49  --sat_fm_lemmas                         false
% 39.67/5.49  --sat_fm_prep                           false
% 39.67/5.49  --sat_fm_uc_incr                        true
% 39.67/5.49  --sat_out_model                         small
% 39.67/5.49  --sat_out_clauses                       false
% 39.67/5.49  
% 39.67/5.49  ------ QBF Options
% 39.67/5.49  
% 39.67/5.49  --qbf_mode                              false
% 39.67/5.49  --qbf_elim_univ                         false
% 39.67/5.49  --qbf_dom_inst                          none
% 39.67/5.49  --qbf_dom_pre_inst                      false
% 39.67/5.49  --qbf_sk_in                             false
% 39.67/5.49  --qbf_pred_elim                         true
% 39.67/5.49  --qbf_split                             512
% 39.67/5.49  
% 39.67/5.49  ------ BMC1 Options
% 39.67/5.49  
% 39.67/5.49  --bmc1_incremental                      false
% 39.67/5.49  --bmc1_axioms                           reachable_all
% 39.67/5.49  --bmc1_min_bound                        0
% 39.67/5.49  --bmc1_max_bound                        -1
% 39.67/5.49  --bmc1_max_bound_default                -1
% 39.67/5.49  --bmc1_symbol_reachability              true
% 39.67/5.49  --bmc1_property_lemmas                  false
% 39.67/5.49  --bmc1_k_induction                      false
% 39.67/5.49  --bmc1_non_equiv_states                 false
% 39.67/5.49  --bmc1_deadlock                         false
% 39.67/5.49  --bmc1_ucm                              false
% 39.67/5.49  --bmc1_add_unsat_core                   none
% 39.67/5.49  --bmc1_unsat_core_children              false
% 39.67/5.49  --bmc1_unsat_core_extrapolate_axioms    false
% 39.67/5.49  --bmc1_out_stat                         full
% 39.67/5.49  --bmc1_ground_init                      false
% 39.67/5.49  --bmc1_pre_inst_next_state              false
% 39.67/5.49  --bmc1_pre_inst_state                   false
% 39.67/5.49  --bmc1_pre_inst_reach_state             false
% 39.67/5.49  --bmc1_out_unsat_core                   false
% 39.67/5.49  --bmc1_aig_witness_out                  false
% 39.67/5.49  --bmc1_verbose                          false
% 39.67/5.49  --bmc1_dump_clauses_tptp                false
% 39.67/5.49  --bmc1_dump_unsat_core_tptp             false
% 39.67/5.49  --bmc1_dump_file                        -
% 39.67/5.49  --bmc1_ucm_expand_uc_limit              128
% 39.67/5.49  --bmc1_ucm_n_expand_iterations          6
% 39.67/5.49  --bmc1_ucm_extend_mode                  1
% 39.67/5.49  --bmc1_ucm_init_mode                    2
% 39.67/5.49  --bmc1_ucm_cone_mode                    none
% 39.67/5.49  --bmc1_ucm_reduced_relation_type        0
% 39.67/5.49  --bmc1_ucm_relax_model                  4
% 39.67/5.49  --bmc1_ucm_full_tr_after_sat            true
% 39.67/5.49  --bmc1_ucm_expand_neg_assumptions       false
% 39.67/5.49  --bmc1_ucm_layered_model                none
% 39.67/5.49  --bmc1_ucm_max_lemma_size               10
% 39.67/5.49  
% 39.67/5.49  ------ AIG Options
% 39.67/5.49  
% 39.67/5.49  --aig_mode                              false
% 39.67/5.49  
% 39.67/5.49  ------ Instantiation Options
% 39.67/5.49  
% 39.67/5.49  --instantiation_flag                    true
% 39.67/5.49  --inst_sos_flag                         true
% 39.67/5.49  --inst_sos_phase                        true
% 39.67/5.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 39.67/5.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 39.67/5.49  --inst_lit_sel_side                     none
% 39.67/5.49  --inst_solver_per_active                1400
% 39.67/5.49  --inst_solver_calls_frac                1.
% 39.67/5.49  --inst_passive_queue_type               priority_queues
% 39.67/5.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 39.67/5.49  --inst_passive_queues_freq              [25;2]
% 39.67/5.49  --inst_dismatching                      true
% 39.67/5.49  --inst_eager_unprocessed_to_passive     true
% 39.67/5.49  --inst_prop_sim_given                   true
% 39.67/5.49  --inst_prop_sim_new                     false
% 39.67/5.49  --inst_subs_new                         false
% 39.67/5.49  --inst_eq_res_simp                      false
% 39.67/5.49  --inst_subs_given                       false
% 39.67/5.49  --inst_orphan_elimination               true
% 39.67/5.49  --inst_learning_loop_flag               true
% 39.67/5.49  --inst_learning_start                   3000
% 39.67/5.49  --inst_learning_factor                  2
% 39.67/5.49  --inst_start_prop_sim_after_learn       3
% 39.67/5.49  --inst_sel_renew                        solver
% 39.67/5.49  --inst_lit_activity_flag                true
% 39.67/5.49  --inst_restr_to_given                   false
% 39.67/5.49  --inst_activity_threshold               500
% 39.67/5.49  --inst_out_proof                        true
% 39.67/5.49  
% 39.67/5.49  ------ Resolution Options
% 39.67/5.49  
% 39.67/5.49  --resolution_flag                       false
% 39.67/5.49  --res_lit_sel                           adaptive
% 39.67/5.49  --res_lit_sel_side                      none
% 39.67/5.49  --res_ordering                          kbo
% 39.67/5.49  --res_to_prop_solver                    active
% 39.67/5.49  --res_prop_simpl_new                    false
% 39.67/5.49  --res_prop_simpl_given                  true
% 39.67/5.49  --res_passive_queue_type                priority_queues
% 39.67/5.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 39.67/5.49  --res_passive_queues_freq               [15;5]
% 39.67/5.49  --res_forward_subs                      full
% 39.67/5.49  --res_backward_subs                     full
% 39.67/5.49  --res_forward_subs_resolution           true
% 39.67/5.49  --res_backward_subs_resolution          true
% 39.67/5.49  --res_orphan_elimination                true
% 39.67/5.49  --res_time_limit                        2.
% 39.67/5.49  --res_out_proof                         true
% 39.67/5.49  
% 39.67/5.49  ------ Superposition Options
% 39.67/5.49  
% 39.67/5.49  --superposition_flag                    true
% 39.67/5.49  --sup_passive_queue_type                priority_queues
% 39.67/5.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 39.67/5.49  --sup_passive_queues_freq               [8;1;4]
% 39.67/5.49  --demod_completeness_check              fast
% 39.67/5.49  --demod_use_ground                      true
% 39.67/5.49  --sup_to_prop_solver                    passive
% 39.67/5.49  --sup_prop_simpl_new                    true
% 39.67/5.49  --sup_prop_simpl_given                  true
% 39.67/5.49  --sup_fun_splitting                     true
% 39.67/5.49  --sup_smt_interval                      50000
% 39.67/5.49  
% 39.67/5.49  ------ Superposition Simplification Setup
% 39.67/5.49  
% 39.67/5.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 39.67/5.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 39.67/5.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 39.67/5.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 39.67/5.49  --sup_full_triv                         [TrivRules;PropSubs]
% 39.67/5.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 39.67/5.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 39.67/5.49  --sup_immed_triv                        [TrivRules]
% 39.67/5.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 39.67/5.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 39.67/5.49  --sup_immed_bw_main                     []
% 39.67/5.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 39.67/5.49  --sup_input_triv                        [Unflattening;TrivRules]
% 39.67/5.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 39.67/5.49  --sup_input_bw                          []
% 39.67/5.49  
% 39.67/5.49  ------ Combination Options
% 39.67/5.49  
% 39.67/5.49  --comb_res_mult                         3
% 39.67/5.49  --comb_sup_mult                         2
% 39.67/5.49  --comb_inst_mult                        10
% 39.67/5.49  
% 39.67/5.49  ------ Debug Options
% 39.67/5.49  
% 39.67/5.49  --dbg_backtrace                         false
% 39.67/5.49  --dbg_dump_prop_clauses                 false
% 39.67/5.49  --dbg_dump_prop_clauses_file            -
% 39.67/5.49  --dbg_out_stat                          false
% 39.67/5.49  
% 39.67/5.49  
% 39.67/5.49  
% 39.67/5.49  
% 39.67/5.49  ------ Proving...
% 39.67/5.49  
% 39.67/5.49  
% 39.67/5.49  % SZS status Theorem for theBenchmark.p
% 39.67/5.49  
% 39.67/5.49   Resolution empty clause
% 39.67/5.49  
% 39.67/5.49  % SZS output start CNFRefutation for theBenchmark.p
% 39.67/5.49  
% 39.67/5.49  fof(f18,axiom,(
% 39.67/5.49    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 39.67/5.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.67/5.49  
% 39.67/5.49  fof(f21,plain,(
% 39.67/5.49    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 39.67/5.49    inference(pure_predicate_removal,[],[f18])).
% 39.67/5.49  
% 39.67/5.49  fof(f59,plain,(
% 39.67/5.49    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 39.67/5.49    inference(cnf_transformation,[],[f21])).
% 39.67/5.49  
% 39.67/5.49  fof(f11,axiom,(
% 39.67/5.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2))))),
% 39.67/5.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.67/5.49  
% 39.67/5.49  fof(f26,plain,(
% 39.67/5.49    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 39.67/5.49    inference(ennf_transformation,[],[f11])).
% 39.67/5.49  
% 39.67/5.49  fof(f50,plain,(
% 39.67/5.49    ( ! [X2,X0,X1] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 39.67/5.49    inference(cnf_transformation,[],[f26])).
% 39.67/5.49  
% 39.67/5.49  fof(f9,axiom,(
% 39.67/5.49    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 39.67/5.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.67/5.49  
% 39.67/5.49  fof(f23,plain,(
% 39.67/5.49    ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 39.67/5.49    inference(ennf_transformation,[],[f9])).
% 39.67/5.49  
% 39.67/5.49  fof(f48,plain,(
% 39.67/5.49    ( ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1)) )),
% 39.67/5.49    inference(cnf_transformation,[],[f23])).
% 39.67/5.49  
% 39.67/5.49  fof(f13,axiom,(
% 39.67/5.49    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)))),
% 39.67/5.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.67/5.49  
% 39.67/5.49  fof(f27,plain,(
% 39.67/5.49    ! [X0,X1] : ((r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)) | ~v1_relat_1(X1))),
% 39.67/5.49    inference(ennf_transformation,[],[f13])).
% 39.67/5.49  
% 39.67/5.49  fof(f54,plain,(
% 39.67/5.49    ( ! [X0,X1] : (r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) | ~v1_relat_1(X1)) )),
% 39.67/5.49    inference(cnf_transformation,[],[f27])).
% 39.67/5.49  
% 39.67/5.49  fof(f12,axiom,(
% 39.67/5.49    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 39.67/5.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.67/5.49  
% 39.67/5.49  fof(f51,plain,(
% 39.67/5.49    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 39.67/5.49    inference(cnf_transformation,[],[f12])).
% 39.67/5.49  
% 39.67/5.49  fof(f14,axiom,(
% 39.67/5.49    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k5_relat_1(k6_relat_1(X0),X1) = X1))),
% 39.67/5.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.67/5.49  
% 39.67/5.49  fof(f28,plain,(
% 39.67/5.49    ! [X0,X1] : ((k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 39.67/5.49    inference(ennf_transformation,[],[f14])).
% 39.67/5.49  
% 39.67/5.49  fof(f29,plain,(
% 39.67/5.49    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 39.67/5.49    inference(flattening,[],[f28])).
% 39.67/5.49  
% 39.67/5.49  fof(f55,plain,(
% 39.67/5.49    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 39.67/5.49    inference(cnf_transformation,[],[f29])).
% 39.67/5.49  
% 39.67/5.49  fof(f17,axiom,(
% 39.67/5.49    ! [X0,X1] : (v1_relat_1(X1) => k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0))),
% 39.67/5.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.67/5.49  
% 39.67/5.49  fof(f32,plain,(
% 39.67/5.49    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 39.67/5.49    inference(ennf_transformation,[],[f17])).
% 39.67/5.49  
% 39.67/5.49  fof(f58,plain,(
% 39.67/5.49    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 39.67/5.49    inference(cnf_transformation,[],[f32])).
% 39.67/5.49  
% 39.67/5.49  fof(f8,axiom,(
% 39.67/5.49    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k3_xboole_0(X0,X1)))),
% 39.67/5.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.67/5.49  
% 39.67/5.49  fof(f22,plain,(
% 39.67/5.49    ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 39.67/5.49    inference(ennf_transformation,[],[f8])).
% 39.67/5.49  
% 39.67/5.49  fof(f47,plain,(
% 39.67/5.49    ( ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0)) )),
% 39.67/5.49    inference(cnf_transformation,[],[f22])).
% 39.67/5.49  
% 39.67/5.49  fof(f4,axiom,(
% 39.67/5.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 39.67/5.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.67/5.49  
% 39.67/5.49  fof(f43,plain,(
% 39.67/5.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 39.67/5.49    inference(cnf_transformation,[],[f4])).
% 39.67/5.49  
% 39.67/5.49  fof(f65,plain,(
% 39.67/5.49    ( ! [X0,X1] : (v1_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,X1))) | ~v1_relat_1(X0)) )),
% 39.67/5.49    inference(definition_unfolding,[],[f47,f43])).
% 39.67/5.49  
% 39.67/5.49  fof(f16,axiom,(
% 39.67/5.49    ! [X0,X1] : (v1_relat_1(X1) => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)))),
% 39.67/5.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.67/5.49  
% 39.67/5.49  fof(f31,plain,(
% 39.67/5.49    ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 39.67/5.49    inference(ennf_transformation,[],[f16])).
% 39.67/5.49  
% 39.67/5.49  fof(f57,plain,(
% 39.67/5.49    ( ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 39.67/5.49    inference(cnf_transformation,[],[f31])).
% 39.67/5.49  
% 39.67/5.49  fof(f66,plain,(
% 39.67/5.49    ( ! [X0,X1] : (k4_xboole_0(k1_relat_1(X1),k4_xboole_0(k1_relat_1(X1),X0)) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 39.67/5.49    inference(definition_unfolding,[],[f57,f43])).
% 39.67/5.49  
% 39.67/5.49  fof(f1,axiom,(
% 39.67/5.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 39.67/5.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.67/5.49  
% 39.67/5.49  fof(f38,plain,(
% 39.67/5.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 39.67/5.49    inference(cnf_transformation,[],[f1])).
% 39.67/5.49  
% 39.67/5.49  fof(f62,plain,(
% 39.67/5.49    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 39.67/5.49    inference(definition_unfolding,[],[f38,f43,f43])).
% 39.67/5.49  
% 39.67/5.49  fof(f3,axiom,(
% 39.67/5.49    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 39.67/5.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.67/5.49  
% 39.67/5.49  fof(f42,plain,(
% 39.67/5.49    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 39.67/5.49    inference(cnf_transformation,[],[f3])).
% 39.67/5.49  
% 39.67/5.49  fof(f63,plain,(
% 39.67/5.49    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) )),
% 39.67/5.49    inference(definition_unfolding,[],[f42,f43])).
% 39.67/5.49  
% 39.67/5.49  fof(f15,axiom,(
% 39.67/5.49    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 39.67/5.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.67/5.49  
% 39.67/5.49  fof(f30,plain,(
% 39.67/5.49    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 39.67/5.49    inference(ennf_transformation,[],[f15])).
% 39.67/5.49  
% 39.67/5.49  fof(f56,plain,(
% 39.67/5.49    ( ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 39.67/5.49    inference(cnf_transformation,[],[f30])).
% 39.67/5.49  
% 39.67/5.49  fof(f52,plain,(
% 39.67/5.49    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 39.67/5.49    inference(cnf_transformation,[],[f12])).
% 39.67/5.49  
% 39.67/5.49  fof(f2,axiom,(
% 39.67/5.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 39.67/5.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.67/5.49  
% 39.67/5.49  fof(f34,plain,(
% 39.67/5.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 39.67/5.49    inference(nnf_transformation,[],[f2])).
% 39.67/5.49  
% 39.67/5.49  fof(f35,plain,(
% 39.67/5.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 39.67/5.49    inference(flattening,[],[f34])).
% 39.67/5.49  
% 39.67/5.49  fof(f39,plain,(
% 39.67/5.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 39.67/5.49    inference(cnf_transformation,[],[f35])).
% 39.67/5.49  
% 39.67/5.49  fof(f69,plain,(
% 39.67/5.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 39.67/5.49    inference(equality_resolution,[],[f39])).
% 39.67/5.49  
% 39.67/5.49  fof(f10,axiom,(
% 39.67/5.49    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k8_relat_1(X0,X1) = X1))),
% 39.67/5.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.67/5.49  
% 39.67/5.49  fof(f24,plain,(
% 39.67/5.49    ! [X0,X1] : ((k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 39.67/5.49    inference(ennf_transformation,[],[f10])).
% 39.67/5.49  
% 39.67/5.49  fof(f25,plain,(
% 39.67/5.49    ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 39.67/5.49    inference(flattening,[],[f24])).
% 39.67/5.49  
% 39.67/5.49  fof(f49,plain,(
% 39.67/5.49    ( ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 39.67/5.49    inference(cnf_transformation,[],[f25])).
% 39.67/5.49  
% 39.67/5.49  fof(f19,conjecture,(
% 39.67/5.49    ! [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))),
% 39.67/5.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.67/5.49  
% 39.67/5.49  fof(f20,negated_conjecture,(
% 39.67/5.49    ~! [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))),
% 39.67/5.49    inference(negated_conjecture,[],[f19])).
% 39.67/5.49  
% 39.67/5.49  fof(f33,plain,(
% 39.67/5.49    ? [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) != k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))),
% 39.67/5.49    inference(ennf_transformation,[],[f20])).
% 39.67/5.49  
% 39.67/5.49  fof(f36,plain,(
% 39.67/5.49    ? [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) != k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) => k6_relat_1(k3_xboole_0(sK0,sK1)) != k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0))),
% 39.67/5.49    introduced(choice_axiom,[])).
% 39.67/5.49  
% 39.67/5.49  fof(f37,plain,(
% 39.67/5.49    k6_relat_1(k3_xboole_0(sK0,sK1)) != k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0))),
% 39.67/5.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f33,f36])).
% 39.67/5.49  
% 39.67/5.49  fof(f60,plain,(
% 39.67/5.49    k6_relat_1(k3_xboole_0(sK0,sK1)) != k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0))),
% 39.67/5.49    inference(cnf_transformation,[],[f37])).
% 39.67/5.49  
% 39.67/5.49  fof(f67,plain,(
% 39.67/5.49    k6_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) != k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0))),
% 39.67/5.49    inference(definition_unfolding,[],[f60,f43])).
% 39.67/5.49  
% 39.67/5.49  cnf(c_18,plain,
% 39.67/5.49      ( v1_relat_1(k6_relat_1(X0)) ),
% 39.67/5.49      inference(cnf_transformation,[],[f59]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_529,plain,
% 39.67/5.49      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 39.67/5.49      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_9,plain,
% 39.67/5.49      ( ~ v1_relat_1(X0)
% 39.67/5.49      | ~ v1_relat_1(X1)
% 39.67/5.49      | ~ v1_relat_1(X2)
% 39.67/5.49      | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ),
% 39.67/5.49      inference(cnf_transformation,[],[f50]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_536,plain,
% 39.67/5.49      ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
% 39.67/5.49      | v1_relat_1(X0) != iProver_top
% 39.67/5.49      | v1_relat_1(X1) != iProver_top
% 39.67/5.49      | v1_relat_1(X2) != iProver_top ),
% 39.67/5.49      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_2179,plain,
% 39.67/5.49      ( k5_relat_1(k6_relat_1(X0),k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(k6_relat_1(X0),X1),X2)
% 39.67/5.49      | v1_relat_1(X1) != iProver_top
% 39.67/5.49      | v1_relat_1(X2) != iProver_top ),
% 39.67/5.49      inference(superposition,[status(thm)],[c_529,c_536]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_8644,plain,
% 39.67/5.49      ( k5_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),X2) = k5_relat_1(k6_relat_1(X0),k5_relat_1(k6_relat_1(X1),X2))
% 39.67/5.49      | v1_relat_1(X2) != iProver_top ),
% 39.67/5.49      inference(superposition,[status(thm)],[c_529,c_2179]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_7,plain,
% 39.67/5.49      ( ~ v1_relat_1(X0) | k5_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X1,X0) ),
% 39.67/5.49      inference(cnf_transformation,[],[f48]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_538,plain,
% 39.67/5.49      ( k5_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X1,X0)
% 39.67/5.49      | v1_relat_1(X0) != iProver_top ),
% 39.67/5.49      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_1784,plain,
% 39.67/5.49      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k8_relat_1(X1,k6_relat_1(X0)) ),
% 39.67/5.49      inference(superposition,[status(thm)],[c_529,c_538]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_8657,plain,
% 39.67/5.49      ( k5_relat_1(k6_relat_1(X0),k5_relat_1(k6_relat_1(X1),X2)) = k5_relat_1(k8_relat_1(X1,k6_relat_1(X0)),X2)
% 39.67/5.49      | v1_relat_1(X2) != iProver_top ),
% 39.67/5.49      inference(light_normalisation,[status(thm)],[c_8644,c_1784]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_138742,plain,
% 39.67/5.49      ( k5_relat_1(k6_relat_1(X0),k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) = k5_relat_1(k8_relat_1(X1,k6_relat_1(X0)),k6_relat_1(X2)) ),
% 39.67/5.49      inference(superposition,[status(thm)],[c_529,c_8657]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_12,plain,
% 39.67/5.49      ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) | ~ v1_relat_1(X1) ),
% 39.67/5.49      inference(cnf_transformation,[],[f54]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_535,plain,
% 39.67/5.49      ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) = iProver_top
% 39.67/5.49      | v1_relat_1(X1) != iProver_top ),
% 39.67/5.49      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_2080,plain,
% 39.67/5.49      ( r1_tarski(k8_relat_1(X0,k6_relat_1(X1)),k6_relat_1(X0)) = iProver_top
% 39.67/5.49      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 39.67/5.49      inference(superposition,[status(thm)],[c_1784,c_535]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_20,plain,
% 39.67/5.49      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 39.67/5.49      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_2822,plain,
% 39.67/5.49      ( r1_tarski(k8_relat_1(X0,k6_relat_1(X1)),k6_relat_1(X0)) = iProver_top ),
% 39.67/5.49      inference(global_propositional_subsumption,[status(thm)],[c_2080,c_20]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_11,plain,
% 39.67/5.49      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 39.67/5.49      inference(cnf_transformation,[],[f51]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_14,plain,
% 39.67/5.49      ( ~ r1_tarski(k1_relat_1(X0),X1)
% 39.67/5.49      | ~ v1_relat_1(X0)
% 39.67/5.49      | k5_relat_1(k6_relat_1(X1),X0) = X0 ),
% 39.67/5.49      inference(cnf_transformation,[],[f55]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_533,plain,
% 39.67/5.49      ( k5_relat_1(k6_relat_1(X0),X1) = X1
% 39.67/5.49      | r1_tarski(k1_relat_1(X1),X0) != iProver_top
% 39.67/5.49      | v1_relat_1(X1) != iProver_top ),
% 39.67/5.49      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_2259,plain,
% 39.67/5.49      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k6_relat_1(X1)
% 39.67/5.49      | r1_tarski(X1,X0) != iProver_top
% 39.67/5.49      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 39.67/5.49      inference(superposition,[status(thm)],[c_11,c_533]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_2260,plain,
% 39.67/5.49      ( k8_relat_1(X0,k6_relat_1(X1)) = k6_relat_1(X0)
% 39.67/5.49      | r1_tarski(X0,X1) != iProver_top
% 39.67/5.49      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 39.67/5.49      inference(demodulation,[status(thm)],[c_2259,c_1784]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_5636,plain,
% 39.67/5.49      ( r1_tarski(X0,X1) != iProver_top
% 39.67/5.49      | k8_relat_1(X0,k6_relat_1(X1)) = k6_relat_1(X0) ),
% 39.67/5.49      inference(global_propositional_subsumption,[status(thm)],[c_2260,c_20]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_5637,plain,
% 39.67/5.49      ( k8_relat_1(X0,k6_relat_1(X1)) = k6_relat_1(X0)
% 39.67/5.49      | r1_tarski(X0,X1) != iProver_top ),
% 39.67/5.49      inference(renaming,[status(thm)],[c_5636]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_5646,plain,
% 39.67/5.49      ( k8_relat_1(k8_relat_1(X0,k6_relat_1(X1)),k6_relat_1(k6_relat_1(X0))) = k6_relat_1(k8_relat_1(X0,k6_relat_1(X1))) ),
% 39.67/5.49      inference(superposition,[status(thm)],[c_2822,c_5637]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_17,plain,
% 39.67/5.49      ( ~ v1_relat_1(X0) | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
% 39.67/5.49      inference(cnf_transformation,[],[f58]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_530,plain,
% 39.67/5.49      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
% 39.67/5.49      | v1_relat_1(X1) != iProver_top ),
% 39.67/5.49      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_1546,plain,
% 39.67/5.49      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
% 39.67/5.49      inference(superposition,[status(thm)],[c_529,c_530]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_1876,plain,
% 39.67/5.49      ( k7_relat_1(k6_relat_1(X0),X1) = k8_relat_1(X0,k6_relat_1(X1)) ),
% 39.67/5.49      inference(light_normalisation,[status(thm)],[c_1546,c_1784]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_6,plain,
% 39.67/5.49      ( ~ v1_relat_1(X0) | v1_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 39.67/5.49      inference(cnf_transformation,[],[f65]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_539,plain,
% 39.67/5.49      ( v1_relat_1(X0) != iProver_top
% 39.67/5.49      | v1_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,X1))) = iProver_top ),
% 39.67/5.49      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_16,plain,
% 39.67/5.49      ( ~ v1_relat_1(X0)
% 39.67/5.49      | k4_xboole_0(k1_relat_1(X0),k4_xboole_0(k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1)) ),
% 39.67/5.49      inference(cnf_transformation,[],[f66]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_531,plain,
% 39.67/5.49      ( k4_xboole_0(k1_relat_1(X0),k4_xboole_0(k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1))
% 39.67/5.49      | v1_relat_1(X0) != iProver_top ),
% 39.67/5.49      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_986,plain,
% 39.67/5.49      ( k4_xboole_0(k1_relat_1(k6_relat_1(X0)),k4_xboole_0(k1_relat_1(k6_relat_1(X0)),X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
% 39.67/5.49      inference(superposition,[status(thm)],[c_529,c_531]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_987,plain,
% 39.67/5.49      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
% 39.67/5.49      inference(light_normalisation,[status(thm)],[c_986,c_11]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_0,plain,
% 39.67/5.49      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 39.67/5.49      inference(cnf_transformation,[],[f62]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_1119,plain,
% 39.67/5.49      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
% 39.67/5.49      inference(demodulation,[status(thm)],[c_987,c_0]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_1787,plain,
% 39.67/5.49      ( v1_relat_1(X0) != iProver_top
% 39.67/5.49      | v1_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X1),X0))) = iProver_top ),
% 39.67/5.49      inference(light_normalisation,[status(thm)],[c_539,c_1119]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_1884,plain,
% 39.67/5.49      ( v1_relat_1(X0) != iProver_top
% 39.67/5.49      | v1_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0)))) = iProver_top ),
% 39.67/5.49      inference(demodulation,[status(thm)],[c_1876,c_1787]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_5677,plain,
% 39.67/5.49      ( v1_relat_1(k1_relat_1(k6_relat_1(k8_relat_1(X0,k6_relat_1(X1))))) = iProver_top
% 39.67/5.49      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 39.67/5.49      inference(superposition,[status(thm)],[c_5646,c_1884]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_5712,plain,
% 39.67/5.49      ( v1_relat_1(k8_relat_1(X0,k6_relat_1(X1))) = iProver_top
% 39.67/5.49      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 39.67/5.49      inference(demodulation,[status(thm)],[c_5677,c_11]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_5909,plain,
% 39.67/5.49      ( v1_relat_1(k8_relat_1(X0,k6_relat_1(X1))) = iProver_top ),
% 39.67/5.49      inference(global_propositional_subsumption,[status(thm)],[c_5712,c_20]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_5927,plain,
% 39.67/5.49      ( k5_relat_1(k8_relat_1(X0,k6_relat_1(X1)),k6_relat_1(X2)) = k8_relat_1(X2,k8_relat_1(X0,k6_relat_1(X1))) ),
% 39.67/5.49      inference(superposition,[status(thm)],[c_5909,c_538]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_5930,plain,
% 39.67/5.49      ( k5_relat_1(k6_relat_1(X0),k8_relat_1(X1,k6_relat_1(X2))) = k7_relat_1(k8_relat_1(X1,k6_relat_1(X2)),X0) ),
% 39.67/5.49      inference(superposition,[status(thm)],[c_5909,c_530]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_138876,plain,
% 39.67/5.49      ( k7_relat_1(k8_relat_1(X0,k6_relat_1(X1)),X2) = k8_relat_1(X0,k8_relat_1(X1,k6_relat_1(X2))) ),
% 39.67/5.49      inference(demodulation,[status(thm)],[c_138742,c_1784,c_5927,c_5930]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_4,plain,
% 39.67/5.49      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
% 39.67/5.49      inference(cnf_transformation,[],[f63]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_540,plain,
% 39.67/5.49      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = iProver_top ),
% 39.67/5.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_1120,plain,
% 39.67/5.49      ( r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X0) = iProver_top ),
% 39.67/5.49      inference(demodulation,[status(thm)],[c_987,c_540]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_1880,plain,
% 39.67/5.49      ( r1_tarski(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))),X0) = iProver_top ),
% 39.67/5.49      inference(demodulation,[status(thm)],[c_1876,c_1120]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_2257,plain,
% 39.67/5.49      ( k5_relat_1(k6_relat_1(X0),k8_relat_1(X0,k6_relat_1(X1))) = k8_relat_1(X0,k6_relat_1(X1))
% 39.67/5.49      | v1_relat_1(k8_relat_1(X0,k6_relat_1(X1))) != iProver_top ),
% 39.67/5.49      inference(superposition,[status(thm)],[c_1880,c_533]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_5931,plain,
% 39.67/5.49      ( k5_relat_1(k6_relat_1(X0),k8_relat_1(X0,k6_relat_1(X1))) = k8_relat_1(X0,k6_relat_1(X1)) ),
% 39.67/5.49      inference(superposition,[status(thm)],[c_5909,c_2257]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_7091,plain,
% 39.67/5.49      ( k7_relat_1(k8_relat_1(X0,k6_relat_1(X1)),X0) = k8_relat_1(X0,k6_relat_1(X1)) ),
% 39.67/5.49      inference(superposition,[status(thm)],[c_5930,c_5931]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_140506,plain,
% 39.67/5.49      ( k8_relat_1(X0,k8_relat_1(X1,k6_relat_1(X0))) = k8_relat_1(X0,k6_relat_1(X1)) ),
% 39.67/5.49      inference(superposition,[status(thm)],[c_138876,c_7091]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_15,plain,
% 39.67/5.49      ( ~ v1_relat_1(X0) | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ),
% 39.67/5.49      inference(cnf_transformation,[],[f56]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_532,plain,
% 39.67/5.49      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
% 39.67/5.49      | v1_relat_1(X0) != iProver_top ),
% 39.67/5.49      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_1502,plain,
% 39.67/5.49      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(k2_relat_1(k6_relat_1(X0)))) = k6_relat_1(X0) ),
% 39.67/5.49      inference(superposition,[status(thm)],[c_529,c_532]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_10,plain,
% 39.67/5.49      ( k2_relat_1(k6_relat_1(X0)) = X0 ),
% 39.67/5.49      inference(cnf_transformation,[],[f52]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_1503,plain,
% 39.67/5.49      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X0)) = k6_relat_1(X0) ),
% 39.67/5.49      inference(light_normalisation,[status(thm)],[c_1502,c_10]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_2081,plain,
% 39.67/5.49      ( k8_relat_1(X0,k6_relat_1(X0)) = k6_relat_1(X0) ),
% 39.67/5.49      inference(superposition,[status(thm)],[c_1784,c_1503]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_3,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f69]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_541,plain,
% 39.67/5.49      ( r1_tarski(X0,X0) = iProver_top ),
% 39.67/5.49      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_1193,plain,
% 39.67/5.49      ( k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
% 39.67/5.49      inference(superposition,[status(thm)],[c_1119,c_987]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_1879,plain,
% 39.67/5.49      ( k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))) = k1_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
% 39.67/5.49      inference(demodulation,[status(thm)],[c_1876,c_1193]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_1887,plain,
% 39.67/5.49      ( k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))) = k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))) ),
% 39.67/5.49      inference(demodulation,[status(thm)],[c_1879,c_1876]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_2427,plain,
% 39.67/5.49      ( k5_relat_1(k6_relat_1(X0),k8_relat_1(X1,k6_relat_1(X2))) = k8_relat_1(X1,k6_relat_1(X2))
% 39.67/5.49      | r1_tarski(k1_relat_1(k8_relat_1(X2,k6_relat_1(X1))),X0) != iProver_top
% 39.67/5.49      | v1_relat_1(k8_relat_1(X1,k6_relat_1(X2))) != iProver_top ),
% 39.67/5.49      inference(superposition,[status(thm)],[c_1887,c_533]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_17219,plain,
% 39.67/5.49      ( k7_relat_1(k8_relat_1(X0,k6_relat_1(X1)),X2) = k8_relat_1(X0,k6_relat_1(X1))
% 39.67/5.49      | r1_tarski(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))),X2) != iProver_top
% 39.67/5.49      | v1_relat_1(k8_relat_1(X0,k6_relat_1(X1))) != iProver_top ),
% 39.67/5.49      inference(demodulation,[status(thm)],[c_2427,c_5930]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_17221,plain,
% 39.67/5.49      ( r1_tarski(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))),X2) != iProver_top
% 39.67/5.49      | k7_relat_1(k8_relat_1(X0,k6_relat_1(X1)),X2) = k8_relat_1(X0,k6_relat_1(X1)) ),
% 39.67/5.49      inference(global_propositional_subsumption,
% 39.67/5.49                [status(thm)],
% 39.67/5.49                [c_17219,c_20,c_5712]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_17222,plain,
% 39.67/5.49      ( k7_relat_1(k8_relat_1(X0,k6_relat_1(X1)),X2) = k8_relat_1(X0,k6_relat_1(X1))
% 39.67/5.49      | r1_tarski(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))),X2) != iProver_top ),
% 39.67/5.49      inference(renaming,[status(thm)],[c_17221]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_17225,plain,
% 39.67/5.49      ( k7_relat_1(k8_relat_1(X0,k6_relat_1(X1)),k1_relat_1(k8_relat_1(X1,k6_relat_1(X0)))) = k8_relat_1(X0,k6_relat_1(X1)) ),
% 39.67/5.49      inference(superposition,[status(thm)],[c_541,c_17222]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_140509,plain,
% 39.67/5.49      ( k8_relat_1(X0,k8_relat_1(X1,k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0)))))) = k8_relat_1(X0,k6_relat_1(X1)) ),
% 39.67/5.49      inference(superposition,[status(thm)],[c_138876,c_17225]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_5643,plain,
% 39.67/5.49      ( k8_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))),k6_relat_1(X0)) = k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))) ),
% 39.67/5.49      inference(superposition,[status(thm)],[c_1880,c_5637]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_896,plain,
% 39.67/5.49      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = iProver_top ),
% 39.67/5.49      inference(superposition,[status(thm)],[c_0,c_540]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_1118,plain,
% 39.67/5.49      ( r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X1) = iProver_top ),
% 39.67/5.49      inference(demodulation,[status(thm)],[c_987,c_896]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_1881,plain,
% 39.67/5.49      ( r1_tarski(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))),X1) = iProver_top ),
% 39.67/5.49      inference(demodulation,[status(thm)],[c_1876,c_1118]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_5644,plain,
% 39.67/5.49      ( k8_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))),k6_relat_1(X1)) = k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))) ),
% 39.67/5.49      inference(superposition,[status(thm)],[c_1881,c_5637]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_10771,plain,
% 39.67/5.49      ( k6_relat_1(k1_relat_1(k8_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))),k6_relat_1(X0)))) = k8_relat_1(k1_relat_1(k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))))),k6_relat_1(X0)) ),
% 39.67/5.49      inference(superposition,[status(thm)],[c_5643,c_5644]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_10839,plain,
% 39.67/5.49      ( k1_relat_1(k8_relat_1(X0,k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0)))))) = k1_relat_1(k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))))) ),
% 39.67/5.49      inference(superposition,[status(thm)],[c_5644,c_1887]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_9139,plain,
% 39.67/5.49      ( k1_relat_1(k8_relat_1(X0,k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))))) = k1_relat_1(k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))))) ),
% 39.67/5.49      inference(superposition,[status(thm)],[c_5643,c_1887]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_9147,plain,
% 39.67/5.49      ( k1_relat_1(k8_relat_1(X0,k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))))) = k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))) ),
% 39.67/5.49      inference(demodulation,[status(thm)],[c_9139,c_11]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_1882,plain,
% 39.67/5.49      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))) ),
% 39.67/5.49      inference(demodulation,[status(thm)],[c_1876,c_987]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_2107,plain,
% 39.67/5.49      ( k1_relat_1(k8_relat_1(X0,k6_relat_1(k4_xboole_0(X0,X1)))) = k4_xboole_0(X0,k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))) ),
% 39.67/5.49      inference(superposition,[status(thm)],[c_1882,c_1882]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_2911,plain,
% 39.67/5.49      ( k4_xboole_0(X0,k1_relat_1(k8_relat_1(X0,k6_relat_1(k4_xboole_0(X0,X1))))) = k1_relat_1(k8_relat_1(X0,k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))))) ),
% 39.67/5.49      inference(superposition,[status(thm)],[c_2107,c_1882]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_3824,plain,
% 39.67/5.49      ( k1_relat_1(k8_relat_1(X0,k6_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = k1_relat_1(k8_relat_1(X0,k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))))) ),
% 39.67/5.49      inference(superposition,[status(thm)],[c_2911,c_2107]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_1885,plain,
% 39.67/5.49      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))) ),
% 39.67/5.49      inference(demodulation,[status(thm)],[c_1876,c_1119]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_3825,plain,
% 39.67/5.49      ( k1_relat_1(k8_relat_1(X0,k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0)))))) = k1_relat_1(k8_relat_1(X0,k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))))) ),
% 39.67/5.49      inference(light_normalisation,[status(thm)],[c_3824,c_1885]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_10023,plain,
% 39.67/5.49      ( k1_relat_1(k8_relat_1(X0,k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0)))))) = k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))) ),
% 39.67/5.49      inference(demodulation,[status(thm)],[c_9147,c_3825]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_10846,plain,
% 39.67/5.49      ( k1_relat_1(k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))))) = k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))) ),
% 39.67/5.49      inference(light_normalisation,[status(thm)],[c_10839,c_10023]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_10905,plain,
% 39.67/5.49      ( k6_relat_1(k1_relat_1(k8_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))),k6_relat_1(X0)))) = k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0)))) ),
% 39.67/5.49      inference(demodulation,[status(thm)],[c_10771,c_5644,c_10846]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_10906,plain,
% 39.67/5.49      ( k6_relat_1(k1_relat_1(k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))))) = k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0)))) ),
% 39.67/5.49      inference(light_normalisation,[status(thm)],[c_10905,c_5643]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_10907,plain,
% 39.67/5.49      ( k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))) = k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0)))) ),
% 39.67/5.49      inference(demodulation,[status(thm)],[c_10906,c_11]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_8,plain,
% 39.67/5.49      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 39.67/5.49      | ~ v1_relat_1(X0)
% 39.67/5.49      | k8_relat_1(X1,X0) = X0 ),
% 39.67/5.49      inference(cnf_transformation,[],[f49]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_537,plain,
% 39.67/5.49      ( k8_relat_1(X0,X1) = X1
% 39.67/5.49      | r1_tarski(k2_relat_1(X1),X0) != iProver_top
% 39.67/5.49      | v1_relat_1(X1) != iProver_top ),
% 39.67/5.49      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_2250,plain,
% 39.67/5.49      ( k8_relat_1(X0,k6_relat_1(X1)) = k6_relat_1(X1)
% 39.67/5.49      | r1_tarski(X1,X0) != iProver_top
% 39.67/5.49      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 39.67/5.49      inference(superposition,[status(thm)],[c_10,c_537]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_2367,plain,
% 39.67/5.49      ( k8_relat_1(X0,k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))))) = k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))))
% 39.67/5.49      | v1_relat_1(k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))))) != iProver_top ),
% 39.67/5.49      inference(superposition,[status(thm)],[c_1881,c_2250]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_15145,plain,
% 39.67/5.49      ( k8_relat_1(X0,k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))))) = k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0)))) ),
% 39.67/5.49      inference(superposition,[status(thm)],[c_529,c_2367]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_17421,plain,
% 39.67/5.49      ( k8_relat_1(X0,k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))))) = k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0)))) ),
% 39.67/5.49      inference(superposition,[status(thm)],[c_10907,c_15145]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_140513,plain,
% 39.67/5.49      ( k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))) = k8_relat_1(X1,k6_relat_1(X0)) ),
% 39.67/5.49      inference(demodulation,[status(thm)],[c_140509,c_17421]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_9068,plain,
% 39.67/5.49      ( k8_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))),k6_relat_1(X1)) = k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0)))) ),
% 39.67/5.49      inference(superposition,[status(thm)],[c_1887,c_5643]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_2249,plain,
% 39.67/5.49      ( k8_relat_1(k2_relat_1(X0),X0) = X0 | v1_relat_1(X0) != iProver_top ),
% 39.67/5.49      inference(superposition,[status(thm)],[c_541,c_537]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_5925,plain,
% 39.67/5.49      ( k8_relat_1(k2_relat_1(k8_relat_1(X0,k6_relat_1(X1))),k8_relat_1(X0,k6_relat_1(X1))) = k8_relat_1(X0,k6_relat_1(X1)) ),
% 39.67/5.49      inference(superposition,[status(thm)],[c_5909,c_2249]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_14537,plain,
% 39.67/5.49      ( k8_relat_1(k2_relat_1(k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))))),k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))))) = k8_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))),k6_relat_1(X0)) ),
% 39.67/5.49      inference(superposition,[status(thm)],[c_9068,c_5925]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_14650,plain,
% 39.67/5.49      ( k8_relat_1(k2_relat_1(k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))))),k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))))) = k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))) ),
% 39.67/5.49      inference(demodulation,[status(thm)],[c_14537,c_9068]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_11375,plain,
% 39.67/5.49      ( k2_relat_1(k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))))) = k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))) ),
% 39.67/5.49      inference(superposition,[status(thm)],[c_10907,c_10]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_14651,plain,
% 39.67/5.49      ( k8_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))),k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))))) = k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0)))) ),
% 39.67/5.49      inference(light_normalisation,[status(thm)],[c_14650,c_11375]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_5641,plain,
% 39.67/5.49      ( k8_relat_1(k5_relat_1(k6_relat_1(X0),X1),k6_relat_1(X1)) = k6_relat_1(k5_relat_1(k6_relat_1(X0),X1))
% 39.67/5.49      | v1_relat_1(X1) != iProver_top ),
% 39.67/5.49      inference(superposition,[status(thm)],[c_535,c_5637]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_7807,plain,
% 39.67/5.49      ( k8_relat_1(k5_relat_1(k6_relat_1(X0),k8_relat_1(X1,k6_relat_1(X2))),k6_relat_1(k8_relat_1(X1,k6_relat_1(X2)))) = k6_relat_1(k5_relat_1(k6_relat_1(X0),k8_relat_1(X1,k6_relat_1(X2)))) ),
% 39.67/5.49      inference(superposition,[status(thm)],[c_5909,c_5641]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_7817,plain,
% 39.67/5.49      ( k8_relat_1(k7_relat_1(k8_relat_1(X0,k6_relat_1(X1)),X2),k6_relat_1(k8_relat_1(X0,k6_relat_1(X1)))) = k6_relat_1(k7_relat_1(k8_relat_1(X0,k6_relat_1(X1)),X2)) ),
% 39.67/5.49      inference(light_normalisation,[status(thm)],[c_7807,c_5930]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_110055,plain,
% 39.67/5.49      ( k8_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))),X2),k6_relat_1(k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))))) = k6_relat_1(k7_relat_1(k8_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))),k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))))),X2)) ),
% 39.67/5.49      inference(superposition,[status(thm)],[c_14651,c_7817]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_11369,plain,
% 39.67/5.49      ( k7_relat_1(k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))),X2) = k8_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))),k6_relat_1(X2)) ),
% 39.67/5.49      inference(superposition,[status(thm)],[c_10907,c_1876]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_110975,plain,
% 39.67/5.49      ( k8_relat_1(k8_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))),k6_relat_1(X2)),k6_relat_1(k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0)))))) = k6_relat_1(k7_relat_1(k8_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))),k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))))),X2)) ),
% 39.67/5.49      inference(light_normalisation,[status(thm)],[c_110055,c_11369]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_29171,plain,
% 39.67/5.49      ( k8_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))),k6_relat_1(X2)) = k8_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))),k6_relat_1(X2)) ),
% 39.67/5.49      inference(superposition,[status(thm)],[c_11369,c_1876]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_40814,plain,
% 39.67/5.49      ( k8_relat_1(k8_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))),k6_relat_1(X2)),k6_relat_1(k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0)))))) = k6_relat_1(k8_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))),k6_relat_1(X2))) ),
% 39.67/5.49      inference(superposition,[status(thm)],[c_29171,c_5646]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_110976,plain,
% 39.67/5.49      ( k6_relat_1(k8_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))),k6_relat_1(X2))) = k6_relat_1(k8_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))),k6_relat_1(X2))) ),
% 39.67/5.49      inference(demodulation,[status(thm)],[c_110975,c_11369,c_14651,c_40814]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_117063,plain,
% 39.67/5.49      ( k1_relat_1(k6_relat_1(k8_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))),k6_relat_1(X2)))) = k8_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))),k6_relat_1(X2)) ),
% 39.67/5.49      inference(superposition,[status(thm)],[c_110976,c_11]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_142003,plain,
% 39.67/5.49      ( k1_relat_1(k6_relat_1(k8_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))),k8_relat_1(X2,k6_relat_1(X3))))) = k8_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))),k6_relat_1(k1_relat_1(k8_relat_1(X3,k6_relat_1(X2))))) ),
% 39.67/5.49      inference(superposition,[status(thm)],[c_140513,c_117063]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_141795,plain,
% 39.67/5.49      ( k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))) = k2_relat_1(k8_relat_1(X1,k6_relat_1(X0))) ),
% 39.67/5.49      inference(superposition,[status(thm)],[c_140513,c_10]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_142208,plain,
% 39.67/5.49      ( k1_relat_1(k6_relat_1(k8_relat_1(k2_relat_1(k8_relat_1(X0,k6_relat_1(X1))),k8_relat_1(X2,k6_relat_1(X3))))) = k8_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))),k6_relat_1(k1_relat_1(k8_relat_1(X3,k6_relat_1(X2))))) ),
% 39.67/5.49      inference(light_normalisation,[status(thm)],[c_142003,c_141795]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_10758,plain,
% 39.67/5.49      ( k8_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))),k6_relat_1(X0)) = k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0)))) ),
% 39.67/5.49      inference(superposition,[status(thm)],[c_1887,c_5644]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_140928,plain,
% 39.67/5.49      ( k8_relat_1(X0,k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))))) = k8_relat_1(X0,k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))))) ),
% 39.67/5.49      inference(superposition,[status(thm)],[c_10758,c_140506]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_2366,plain,
% 39.67/5.49      ( k8_relat_1(X0,k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))))) = k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))))
% 39.67/5.49      | v1_relat_1(k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))))) != iProver_top ),
% 39.67/5.49      inference(superposition,[status(thm)],[c_1880,c_2250]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_13242,plain,
% 39.67/5.49      ( k8_relat_1(X0,k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))))) = k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))) ),
% 39.67/5.49      inference(superposition,[status(thm)],[c_529,c_2366]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_15348,plain,
% 39.67/5.49      ( k8_relat_1(X0,k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))))) = k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))) ),
% 39.67/5.49      inference(superposition,[status(thm)],[c_10907,c_13242]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_141001,plain,
% 39.67/5.49      ( k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))) = k8_relat_1(X0,k6_relat_1(X1)) ),
% 39.67/5.49      inference(light_normalisation,
% 39.67/5.49                [status(thm)],
% 39.67/5.49                [c_140928,c_15348,c_17421,c_140513]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_142209,plain,
% 39.67/5.49      ( k8_relat_1(k2_relat_1(k8_relat_1(X0,k6_relat_1(X1))),k8_relat_1(X2,k6_relat_1(X3))) = k8_relat_1(k2_relat_1(k8_relat_1(X1,k6_relat_1(X0))),k8_relat_1(X3,k6_relat_1(X2))) ),
% 39.67/5.49      inference(demodulation,[status(thm)],[c_142208,c_11,c_141001,c_141795]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_142021,plain,
% 39.67/5.49      ( k8_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))),k6_relat_1(k1_relat_1(k8_relat_1(X2,k6_relat_1(X3))))) = k8_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))),k8_relat_1(X3,k6_relat_1(X2))) ),
% 39.67/5.49      inference(superposition,[status(thm)],[c_140513,c_29171]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_142174,plain,
% 39.67/5.49      ( k8_relat_1(k2_relat_1(k8_relat_1(X0,k6_relat_1(X1))),k6_relat_1(k1_relat_1(k8_relat_1(X2,k6_relat_1(X3))))) = k8_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))),k8_relat_1(X3,k6_relat_1(X2))) ),
% 39.67/5.49      inference(light_normalisation,[status(thm)],[c_142021,c_141795]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_141269,plain,
% 39.67/5.49      ( k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))) = k2_relat_1(k8_relat_1(X0,k6_relat_1(X1))) ),
% 39.67/5.49      inference(demodulation,[status(thm)],[c_140513,c_11375]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_11442,plain,
% 39.67/5.49      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X2))))) = k8_relat_1(k1_relat_1(k8_relat_1(X2,k6_relat_1(X1))),k6_relat_1(X0)) ),
% 39.67/5.49      inference(superposition,[status(thm)],[c_10907,c_1784]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_141320,plain,
% 39.67/5.49      ( k8_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))),k6_relat_1(X2)) = k5_relat_1(k6_relat_1(X2),k8_relat_1(X0,k6_relat_1(X1))) ),
% 39.67/5.49      inference(demodulation,[status(thm)],[c_140513,c_11442]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_140308,plain,
% 39.67/5.49      ( k5_relat_1(k6_relat_1(X0),k8_relat_1(X1,k6_relat_1(X2))) = k8_relat_1(X1,k8_relat_1(X2,k6_relat_1(X0))) ),
% 39.67/5.49      inference(demodulation,[status(thm)],[c_138876,c_5930]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_141321,plain,
% 39.67/5.49      ( k8_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))),k6_relat_1(X2)) = k8_relat_1(X0,k8_relat_1(X1,k6_relat_1(X2))) ),
% 39.67/5.49      inference(demodulation,[status(thm)],[c_141320,c_140308]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_141348,plain,
% 39.67/5.49      ( k8_relat_1(k2_relat_1(k8_relat_1(X0,k6_relat_1(X1))),k6_relat_1(X2)) = k8_relat_1(X0,k8_relat_1(X1,k6_relat_1(X2))) ),
% 39.67/5.49      inference(demodulation,[status(thm)],[c_141269,c_141321]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_142175,plain,
% 39.67/5.49      ( k8_relat_1(k2_relat_1(k8_relat_1(X0,k6_relat_1(X1))),k8_relat_1(X2,k6_relat_1(X3))) = k8_relat_1(X1,k8_relat_1(X0,k8_relat_1(X3,k6_relat_1(X2)))) ),
% 39.67/5.49      inference(demodulation,
% 39.67/5.49                [status(thm)],
% 39.67/5.49                [c_142174,c_141001,c_141348,c_141795]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_143794,plain,
% 39.67/5.49      ( k8_relat_1(k2_relat_1(k8_relat_1(X0,k6_relat_1(X1))),k8_relat_1(X2,k6_relat_1(X3))) = k8_relat_1(X0,k8_relat_1(X1,k8_relat_1(X2,k6_relat_1(X3)))) ),
% 39.67/5.49      inference(light_normalisation,[status(thm)],[c_142209,c_142175]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_143798,plain,
% 39.67/5.49      ( k8_relat_1(X0,k8_relat_1(X0,k8_relat_1(X1,k6_relat_1(X2)))) = k8_relat_1(k2_relat_1(k6_relat_1(X0)),k8_relat_1(X1,k6_relat_1(X2))) ),
% 39.67/5.49      inference(superposition,[status(thm)],[c_2081,c_143794]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_143911,plain,
% 39.67/5.49      ( k8_relat_1(X0,k8_relat_1(X0,k8_relat_1(X1,k6_relat_1(X2)))) = k8_relat_1(X0,k8_relat_1(X1,k6_relat_1(X2))) ),
% 39.67/5.49      inference(light_normalisation,[status(thm)],[c_143798,c_10]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_144187,plain,
% 39.67/5.49      ( k8_relat_1(X0,k8_relat_1(X0,k6_relat_1(X1))) = k8_relat_1(X0,k8_relat_1(X1,k6_relat_1(X0))) ),
% 39.67/5.49      inference(superposition,[status(thm)],[c_140506,c_143911]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_140442,plain,
% 39.67/5.49      ( k8_relat_1(X0,k8_relat_1(X0,k6_relat_1(X1))) = k7_relat_1(k6_relat_1(X0),X1) ),
% 39.67/5.49      inference(superposition,[status(thm)],[c_2081,c_138876]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_140564,plain,
% 39.67/5.49      ( k8_relat_1(X0,k8_relat_1(X0,k6_relat_1(X1))) = k8_relat_1(X0,k6_relat_1(X1)) ),
% 39.67/5.49      inference(light_normalisation,[status(thm)],[c_140442,c_1876]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_141263,plain,
% 39.67/5.49      ( k8_relat_1(X0,k8_relat_1(X1,k6_relat_1(X0))) = k8_relat_1(X1,k6_relat_1(X0)) ),
% 39.67/5.49      inference(demodulation,[status(thm)],[c_140513,c_13242]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_144236,plain,
% 39.67/5.49      ( k8_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X1,k6_relat_1(X0)) ),
% 39.67/5.49      inference(light_normalisation,[status(thm)],[c_144187,c_140564,c_141263]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_19,negated_conjecture,
% 39.67/5.49      ( k6_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) != k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) ),
% 39.67/5.49      inference(cnf_transformation,[],[f67]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_1122,plain,
% 39.67/5.49      ( k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(sK0),sK1))) != k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) ),
% 39.67/5.49      inference(demodulation,[status(thm)],[c_987,c_19]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_1878,plain,
% 39.67/5.49      ( k6_relat_1(k1_relat_1(k8_relat_1(sK0,k6_relat_1(sK1)))) != k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) ),
% 39.67/5.49      inference(demodulation,[status(thm)],[c_1876,c_1122]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_1888,plain,
% 39.67/5.49      ( k6_relat_1(k1_relat_1(k8_relat_1(sK0,k6_relat_1(sK1)))) != k8_relat_1(sK0,k6_relat_1(sK1)) ),
% 39.67/5.49      inference(demodulation,[status(thm)],[c_1878,c_1784]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_141184,plain,
% 39.67/5.49      ( k8_relat_1(sK1,k6_relat_1(sK0)) != k8_relat_1(sK0,k6_relat_1(sK1)) ),
% 39.67/5.49      inference(demodulation,[status(thm)],[c_140513,c_1888]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_144577,plain,
% 39.67/5.49      ( k8_relat_1(sK0,k6_relat_1(sK1)) != k8_relat_1(sK0,k6_relat_1(sK1)) ),
% 39.67/5.49      inference(demodulation,[status(thm)],[c_144236,c_141184]) ).
% 39.67/5.49  
% 39.67/5.49  cnf(c_144583,plain,
% 39.67/5.49      ( $false ),
% 39.67/5.49      inference(equality_resolution_simp,[status(thm)],[c_144577]) ).
% 39.67/5.49  
% 39.67/5.49  
% 39.67/5.49  % SZS output end CNFRefutation for theBenchmark.p
% 39.67/5.49  
% 39.67/5.49  ------                               Statistics
% 39.67/5.49  
% 39.67/5.49  ------ General
% 39.67/5.49  
% 39.67/5.49  abstr_ref_over_cycles:                  0
% 39.67/5.49  abstr_ref_under_cycles:                 0
% 39.67/5.49  gc_basic_clause_elim:                   0
% 39.67/5.49  forced_gc_time:                         0
% 39.67/5.49  parsing_time:                           0.008
% 39.67/5.49  unif_index_cands_time:                  0.
% 39.67/5.49  unif_index_add_time:                    0.
% 39.67/5.49  orderings_time:                         0.
% 39.67/5.49  out_proof_time:                         0.016
% 39.67/5.49  total_time:                             4.869
% 39.67/5.49  num_of_symbols:                         44
% 39.67/5.49  num_of_terms:                           208748
% 39.67/5.49  
% 39.67/5.49  ------ Preprocessing
% 39.67/5.49  
% 39.67/5.49  num_of_splits:                          0
% 39.67/5.49  num_of_split_atoms:                     0
% 39.67/5.49  num_of_reused_defs:                     0
% 39.67/5.49  num_eq_ax_congr_red:                    27
% 39.67/5.49  num_of_sem_filtered_clauses:            1
% 39.67/5.49  num_of_subtypes:                        0
% 39.67/5.49  monotx_restored_types:                  0
% 39.67/5.49  sat_num_of_epr_types:                   0
% 39.67/5.49  sat_num_of_non_cyclic_types:            0
% 39.67/5.49  sat_guarded_non_collapsed_types:        0
% 39.67/5.49  num_pure_diseq_elim:                    0
% 39.67/5.49  simp_replaced_by:                       0
% 39.67/5.49  res_preprocessed:                       97
% 39.67/5.49  prep_upred:                             0
% 39.67/5.49  prep_unflattend:                        0
% 39.67/5.49  smt_new_axioms:                         0
% 39.67/5.49  pred_elim_cands:                        2
% 39.67/5.49  pred_elim:                              0
% 39.67/5.49  pred_elim_cl:                           0
% 39.67/5.49  pred_elim_cycles:                       2
% 39.67/5.49  merged_defs:                            0
% 39.67/5.49  merged_defs_ncl:                        0
% 39.67/5.49  bin_hyper_res:                          0
% 39.67/5.49  prep_cycles:                            4
% 39.67/5.49  pred_elim_time:                         0.
% 39.67/5.49  splitting_time:                         0.
% 39.67/5.49  sem_filter_time:                        0.
% 39.67/5.49  monotx_time:                            0.
% 39.67/5.49  subtype_inf_time:                       0.
% 39.67/5.49  
% 39.67/5.49  ------ Problem properties
% 39.67/5.49  
% 39.67/5.49  clauses:                                19
% 39.67/5.49  conjectures:                            1
% 39.67/5.49  epr:                                    2
% 39.67/5.49  horn:                                   19
% 39.67/5.49  ground:                                 1
% 39.67/5.49  unary:                                  8
% 39.67/5.49  binary:                                 7
% 39.67/5.49  lits:                                   35
% 39.67/5.49  lits_eq:                                13
% 39.67/5.49  fd_pure:                                0
% 39.67/5.49  fd_pseudo:                              0
% 39.67/5.49  fd_cond:                                0
% 39.67/5.49  fd_pseudo_cond:                         1
% 39.67/5.49  ac_symbols:                             0
% 39.67/5.49  
% 39.67/5.49  ------ Propositional Solver
% 39.67/5.49  
% 39.67/5.49  prop_solver_calls:                      44
% 39.67/5.49  prop_fast_solver_calls:                 1110
% 39.67/5.49  smt_solver_calls:                       0
% 39.67/5.49  smt_fast_solver_calls:                  0
% 39.67/5.49  prop_num_of_clauses:                    43238
% 39.67/5.49  prop_preprocess_simplified:             39343
% 39.67/5.49  prop_fo_subsumed:                       7
% 39.67/5.49  prop_solver_time:                       0.
% 39.67/5.49  smt_solver_time:                        0.
% 39.67/5.49  smt_fast_solver_time:                   0.
% 39.67/5.49  prop_fast_solver_time:                  0.
% 39.67/5.49  prop_unsat_core_time:                   0.
% 39.67/5.49  
% 39.67/5.49  ------ QBF
% 39.67/5.49  
% 39.67/5.49  qbf_q_res:                              0
% 39.67/5.49  qbf_num_tautologies:                    0
% 39.67/5.49  qbf_prep_cycles:                        0
% 39.67/5.49  
% 39.67/5.49  ------ BMC1
% 39.67/5.49  
% 39.67/5.49  bmc1_current_bound:                     -1
% 39.67/5.49  bmc1_last_solved_bound:                 -1
% 39.67/5.49  bmc1_unsat_core_size:                   -1
% 39.67/5.49  bmc1_unsat_core_parents_size:           -1
% 39.67/5.49  bmc1_merge_next_fun:                    0
% 39.67/5.49  bmc1_unsat_core_clauses_time:           0.
% 39.67/5.49  
% 39.67/5.49  ------ Instantiation
% 39.67/5.49  
% 39.67/5.49  inst_num_of_clauses:                    7537
% 39.67/5.49  inst_num_in_passive:                    4523
% 39.67/5.49  inst_num_in_active:                     2678
% 39.67/5.49  inst_num_in_unprocessed:                336
% 39.67/5.49  inst_num_of_loops:                      2810
% 39.67/5.49  inst_num_of_learning_restarts:          0
% 39.67/5.49  inst_num_moves_active_passive:          130
% 39.67/5.49  inst_lit_activity:                      0
% 39.67/5.49  inst_lit_activity_moves:                0
% 39.67/5.49  inst_num_tautologies:                   0
% 39.67/5.49  inst_num_prop_implied:                  0
% 39.67/5.49  inst_num_existing_simplified:           0
% 39.67/5.49  inst_num_eq_res_simplified:             0
% 39.67/5.49  inst_num_child_elim:                    0
% 39.67/5.49  inst_num_of_dismatching_blockings:      3290
% 39.67/5.49  inst_num_of_non_proper_insts:           8805
% 39.67/5.49  inst_num_of_duplicates:                 0
% 39.67/5.49  inst_inst_num_from_inst_to_res:         0
% 39.67/5.49  inst_dismatching_checking_time:         0.
% 39.67/5.49  
% 39.67/5.49  ------ Resolution
% 39.67/5.49  
% 39.67/5.49  res_num_of_clauses:                     0
% 39.67/5.49  res_num_in_passive:                     0
% 39.67/5.49  res_num_in_active:                      0
% 39.67/5.49  res_num_of_loops:                       101
% 39.67/5.49  res_forward_subset_subsumed:            1030
% 39.67/5.49  res_backward_subset_subsumed:           0
% 39.67/5.49  res_forward_subsumed:                   0
% 39.67/5.49  res_backward_subsumed:                  0
% 39.67/5.49  res_forward_subsumption_resolution:     0
% 39.67/5.49  res_backward_subsumption_resolution:    0
% 39.67/5.49  res_clause_to_clause_subsumption:       61344
% 39.67/5.49  res_orphan_elimination:                 0
% 39.67/5.49  res_tautology_del:                      1362
% 39.67/5.49  res_num_eq_res_simplified:              0
% 39.67/5.49  res_num_sel_changes:                    0
% 39.67/5.49  res_moves_from_active_to_pass:          0
% 39.67/5.49  
% 39.67/5.49  ------ Superposition
% 39.67/5.49  
% 39.67/5.49  sup_time_total:                         0.
% 39.67/5.49  sup_time_generating:                    0.
% 39.67/5.49  sup_time_sim_full:                      0.
% 39.67/5.49  sup_time_sim_immed:                     0.
% 39.67/5.49  
% 39.67/5.49  sup_num_of_clauses:                     10810
% 39.67/5.49  sup_num_in_active:                      243
% 39.67/5.49  sup_num_in_passive:                     10567
% 39.67/5.49  sup_num_of_loops:                       561
% 39.67/5.49  sup_fw_superposition:                   31843
% 39.67/5.49  sup_bw_superposition:                   32601
% 39.67/5.49  sup_immediate_simplified:               23562
% 39.67/5.49  sup_given_eliminated:                   4
% 39.67/5.49  comparisons_done:                       0
% 39.67/5.49  comparisons_avoided:                    0
% 39.67/5.49  
% 39.67/5.49  ------ Simplifications
% 39.67/5.49  
% 39.67/5.49  
% 39.67/5.49  sim_fw_subset_subsumed:                 183
% 39.67/5.49  sim_bw_subset_subsumed:                 144
% 39.67/5.49  sim_fw_subsumed:                        7187
% 39.67/5.49  sim_bw_subsumed:                        16
% 39.67/5.49  sim_fw_subsumption_res:                 0
% 39.67/5.49  sim_bw_subsumption_res:                 0
% 39.67/5.49  sim_tautology_del:                      95
% 39.67/5.49  sim_eq_tautology_del:                   5036
% 39.67/5.49  sim_eq_res_simp:                        0
% 39.67/5.49  sim_fw_demodulated:                     17084
% 39.67/5.49  sim_bw_demodulated:                     469
% 39.67/5.49  sim_light_normalised:                   10496
% 39.67/5.49  sim_joinable_taut:                      0
% 39.67/5.49  sim_joinable_simp:                      0
% 39.67/5.49  sim_ac_normalised:                      0
% 39.67/5.49  sim_smt_subsumption:                    0
% 39.67/5.49  
%------------------------------------------------------------------------------
