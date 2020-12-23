%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:50:01 EST 2020

% Result     : Theorem 43.41s
% Output     : CNFRefutation 43.41s
% Verified   : 
% Statistics : Number of formulae       :  203 (35141 expanded)
%              Number of clauses        :  147 (16997 expanded)
%              Number of leaves         :   17 (7243 expanded)
%              Depth                    :   34
%              Number of atoms          :  319 (52538 expanded)
%              Number of equality atoms :  229 (32266 expanded)
%              Maximal formula depth    :    8 (   2 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    8 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f13,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k5_relat_1(k6_relat_1(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f64,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f47,f42])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_relat_1(X1),k4_xboole_0(k1_relat_1(X1),X0)) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f57,f42])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f61,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f37,f42,f42])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f62,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f41,f42])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f56,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f52,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f33])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f68,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f38])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k8_relat_1(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f19,conjecture,(
    ! [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
    inference(negated_conjecture,[],[f19])).

fof(f32,plain,(
    ? [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) != k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
    inference(ennf_transformation,[],[f20])).

fof(f35,plain,
    ( ? [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) != k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))
   => k6_relat_1(k3_xboole_0(sK0,sK1)) != k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    k6_relat_1(k3_xboole_0(sK0,sK1)) != k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f32,f35])).

fof(f59,plain,(
    k6_relat_1(k3_xboole_0(sK0,sK1)) != k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f36])).

fof(f66,plain,(
    k6_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) != k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) ),
    inference(definition_unfolding,[],[f59,f42])).

cnf(c_6,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_539,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_10,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_535,plain,
    ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2173,plain,
    ( k5_relat_1(k6_relat_1(X0),k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(k6_relat_1(X0),X1),X2)
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_539,c_535])).

cnf(c_8542,plain,
    ( k5_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),X2) = k5_relat_1(k6_relat_1(X0),k5_relat_1(k6_relat_1(X1),X2))
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_539,c_2173])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X1,X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_537,plain,
    ( k5_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X1,X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1786,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k8_relat_1(X1,k6_relat_1(X0)) ),
    inference(superposition,[status(thm)],[c_539,c_537])).

cnf(c_8555,plain,
    ( k5_relat_1(k6_relat_1(X0),k5_relat_1(k6_relat_1(X1),X2)) = k5_relat_1(k8_relat_1(X1,k6_relat_1(X0)),X2)
    | v1_relat_1(X2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8542,c_1786])).

cnf(c_138989,plain,
    ( k5_relat_1(k6_relat_1(X0),k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) = k5_relat_1(k8_relat_1(X1,k6_relat_1(X0)),k6_relat_1(X2)) ),
    inference(superposition,[status(thm)],[c_539,c_8555])).

cnf(c_13,plain,
    ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_534,plain,
    ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2070,plain,
    ( r1_tarski(k8_relat_1(X0,k6_relat_1(X1)),k6_relat_1(X0)) = iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1786,c_534])).

cnf(c_52,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2817,plain,
    ( r1_tarski(k8_relat_1(X0,k6_relat_1(X1)),k6_relat_1(X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2070,c_52])).

cnf(c_12,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_15,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k6_relat_1(X1),X0) = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_532,plain,
    ( k5_relat_1(k6_relat_1(X0),X1) = X1
    | r1_tarski(k1_relat_1(X1),X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2256,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k6_relat_1(X1)
    | r1_tarski(X1,X0) != iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_12,c_532])).

cnf(c_2257,plain,
    ( k8_relat_1(X0,k6_relat_1(X1)) = k6_relat_1(X0)
    | r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2256,c_1786])).

cnf(c_5596,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | k8_relat_1(X0,k6_relat_1(X1)) = k6_relat_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2257,c_52])).

cnf(c_5597,plain,
    ( k8_relat_1(X0,k6_relat_1(X1)) = k6_relat_1(X0)
    | r1_tarski(X0,X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_5596])).

cnf(c_5606,plain,
    ( k8_relat_1(k8_relat_1(X0,k6_relat_1(X1)),k6_relat_1(k6_relat_1(X0))) = k6_relat_1(k8_relat_1(X0,k6_relat_1(X1))) ),
    inference(superposition,[status(thm)],[c_2817,c_5597])).

cnf(c_18,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_529,plain,
    ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1541,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(superposition,[status(thm)],[c_539,c_529])).

cnf(c_1885,plain,
    ( k7_relat_1(k6_relat_1(X0),X1) = k8_relat_1(X0,k6_relat_1(X1)) ),
    inference(light_normalisation,[status(thm)],[c_1541,c_1786])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_538,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_17,plain,
    ( ~ v1_relat_1(X0)
    | k4_xboole_0(k1_relat_1(X0),k4_xboole_0(k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_530,plain,
    ( k4_xboole_0(k1_relat_1(X0),k4_xboole_0(k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1005,plain,
    ( k4_xboole_0(k1_relat_1(k6_relat_1(X0)),k4_xboole_0(k1_relat_1(k6_relat_1(X0)),X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(superposition,[status(thm)],[c_539,c_530])).

cnf(c_1006,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(light_normalisation,[status(thm)],[c_1005,c_12])).

cnf(c_0,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1112,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
    inference(demodulation,[status(thm)],[c_1006,c_0])).

cnf(c_1789,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X1),X0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_538,c_1112])).

cnf(c_1893,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1885,c_1789])).

cnf(c_5637,plain,
    ( v1_relat_1(k1_relat_1(k6_relat_1(k8_relat_1(X0,k6_relat_1(X1))))) = iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5606,c_1893])).

cnf(c_5672,plain,
    ( v1_relat_1(k8_relat_1(X0,k6_relat_1(X1))) = iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5637,c_12])).

cnf(c_5864,plain,
    ( v1_relat_1(k8_relat_1(X0,k6_relat_1(X1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5672,c_52])).

cnf(c_5882,plain,
    ( k5_relat_1(k8_relat_1(X0,k6_relat_1(X1)),k6_relat_1(X2)) = k8_relat_1(X2,k8_relat_1(X0,k6_relat_1(X1))) ),
    inference(superposition,[status(thm)],[c_5864,c_537])).

cnf(c_5885,plain,
    ( k5_relat_1(k6_relat_1(X0),k8_relat_1(X1,k6_relat_1(X2))) = k7_relat_1(k8_relat_1(X1,k6_relat_1(X2)),X0) ),
    inference(superposition,[status(thm)],[c_5864,c_529])).

cnf(c_139123,plain,
    ( k7_relat_1(k8_relat_1(X0,k6_relat_1(X1)),X2) = k8_relat_1(X0,k8_relat_1(X1,k6_relat_1(X2))) ),
    inference(demodulation,[status(thm)],[c_138989,c_1786,c_5882,c_5885])).

cnf(c_4,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_540,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1113,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1006,c_540])).

cnf(c_1889,plain,
    ( r1_tarski(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))),X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1885,c_1113])).

cnf(c_2254,plain,
    ( k5_relat_1(k6_relat_1(X0),k8_relat_1(X0,k6_relat_1(X1))) = k8_relat_1(X0,k6_relat_1(X1))
    | v1_relat_1(k8_relat_1(X0,k6_relat_1(X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1889,c_532])).

cnf(c_5886,plain,
    ( k5_relat_1(k6_relat_1(X0),k8_relat_1(X0,k6_relat_1(X1))) = k8_relat_1(X0,k6_relat_1(X1)) ),
    inference(superposition,[status(thm)],[c_5864,c_2254])).

cnf(c_7061,plain,
    ( k7_relat_1(k8_relat_1(X0,k6_relat_1(X1)),X0) = k8_relat_1(X0,k6_relat_1(X1)) ),
    inference(superposition,[status(thm)],[c_5885,c_5886])).

cnf(c_140839,plain,
    ( k8_relat_1(X0,k8_relat_1(X1,k6_relat_1(X0))) = k8_relat_1(X0,k6_relat_1(X1)) ),
    inference(superposition,[status(thm)],[c_139123,c_7061])).

cnf(c_16,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_531,plain,
    ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1500,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(k2_relat_1(k6_relat_1(X0)))) = k6_relat_1(X0) ),
    inference(superposition,[status(thm)],[c_539,c_531])).

cnf(c_11,plain,
    ( k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1501,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X0)) = k6_relat_1(X0) ),
    inference(light_normalisation,[status(thm)],[c_1500,c_11])).

cnf(c_2071,plain,
    ( k8_relat_1(X0,k6_relat_1(X0)) = k6_relat_1(X0) ),
    inference(superposition,[status(thm)],[c_1786,c_1501])).

cnf(c_3,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_541,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1192,plain,
    ( k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
    inference(superposition,[status(thm)],[c_1112,c_1006])).

cnf(c_1888,plain,
    ( k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))) = k1_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
    inference(demodulation,[status(thm)],[c_1885,c_1192])).

cnf(c_1896,plain,
    ( k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))) = k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))) ),
    inference(demodulation,[status(thm)],[c_1888,c_1885])).

cnf(c_2439,plain,
    ( k5_relat_1(k6_relat_1(X0),k8_relat_1(X1,k6_relat_1(X2))) = k8_relat_1(X1,k6_relat_1(X2))
    | r1_tarski(k1_relat_1(k8_relat_1(X2,k6_relat_1(X1))),X0) != iProver_top
    | v1_relat_1(k8_relat_1(X1,k6_relat_1(X2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1896,c_532])).

cnf(c_17178,plain,
    ( k7_relat_1(k8_relat_1(X0,k6_relat_1(X1)),X2) = k8_relat_1(X0,k6_relat_1(X1))
    | r1_tarski(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))),X2) != iProver_top
    | v1_relat_1(k8_relat_1(X0,k6_relat_1(X1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2439,c_5885])).

cnf(c_17180,plain,
    ( r1_tarski(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))),X2) != iProver_top
    | k7_relat_1(k8_relat_1(X0,k6_relat_1(X1)),X2) = k8_relat_1(X0,k6_relat_1(X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_17178,c_52,c_5672])).

cnf(c_17181,plain,
    ( k7_relat_1(k8_relat_1(X0,k6_relat_1(X1)),X2) = k8_relat_1(X0,k6_relat_1(X1))
    | r1_tarski(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))),X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_17180])).

cnf(c_17184,plain,
    ( k7_relat_1(k8_relat_1(X0,k6_relat_1(X1)),k1_relat_1(k8_relat_1(X1,k6_relat_1(X0)))) = k8_relat_1(X0,k6_relat_1(X1)) ),
    inference(superposition,[status(thm)],[c_541,c_17181])).

cnf(c_140842,plain,
    ( k8_relat_1(X0,k8_relat_1(X1,k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0)))))) = k8_relat_1(X0,k6_relat_1(X1)) ),
    inference(superposition,[status(thm)],[c_139123,c_17184])).

cnf(c_5603,plain,
    ( k8_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))),k6_relat_1(X0)) = k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))) ),
    inference(superposition,[status(thm)],[c_1889,c_5597])).

cnf(c_891,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_540])).

cnf(c_1111,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1006,c_891])).

cnf(c_1890,plain,
    ( r1_tarski(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))),X1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1885,c_1111])).

cnf(c_5604,plain,
    ( k8_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))),k6_relat_1(X1)) = k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))) ),
    inference(superposition,[status(thm)],[c_1890,c_5597])).

cnf(c_10771,plain,
    ( k8_relat_1(k1_relat_1(k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))))),k6_relat_1(X0)) = k6_relat_1(k1_relat_1(k8_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))),k6_relat_1(X0)))) ),
    inference(superposition,[status(thm)],[c_5603,c_5604])).

cnf(c_10839,plain,
    ( k1_relat_1(k8_relat_1(X0,k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0)))))) = k1_relat_1(k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))))) ),
    inference(superposition,[status(thm)],[c_5604,c_1896])).

cnf(c_9222,plain,
    ( k1_relat_1(k8_relat_1(X0,k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))))) = k1_relat_1(k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))))) ),
    inference(superposition,[status(thm)],[c_5603,c_1896])).

cnf(c_9230,plain,
    ( k1_relat_1(k8_relat_1(X0,k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))))) = k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))) ),
    inference(demodulation,[status(thm)],[c_9222,c_12])).

cnf(c_1891,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))) ),
    inference(demodulation,[status(thm)],[c_1885,c_1006])).

cnf(c_2118,plain,
    ( k1_relat_1(k8_relat_1(X0,k6_relat_1(k4_xboole_0(X0,X1)))) = k4_xboole_0(X0,k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))) ),
    inference(superposition,[status(thm)],[c_1891,c_1891])).

cnf(c_2914,plain,
    ( k4_xboole_0(X0,k1_relat_1(k8_relat_1(X0,k6_relat_1(k4_xboole_0(X0,X1))))) = k1_relat_1(k8_relat_1(X0,k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))))) ),
    inference(superposition,[status(thm)],[c_2118,c_1891])).

cnf(c_3784,plain,
    ( k1_relat_1(k8_relat_1(X0,k6_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = k1_relat_1(k8_relat_1(X0,k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))))) ),
    inference(superposition,[status(thm)],[c_2914,c_2118])).

cnf(c_1894,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))) ),
    inference(demodulation,[status(thm)],[c_1885,c_1112])).

cnf(c_3785,plain,
    ( k1_relat_1(k8_relat_1(X0,k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0)))))) = k1_relat_1(k8_relat_1(X0,k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))))) ),
    inference(light_normalisation,[status(thm)],[c_3784,c_1894])).

cnf(c_10140,plain,
    ( k1_relat_1(k8_relat_1(X0,k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0)))))) = k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))) ),
    inference(demodulation,[status(thm)],[c_9230,c_3785])).

cnf(c_10846,plain,
    ( k1_relat_1(k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))))) = k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))) ),
    inference(light_normalisation,[status(thm)],[c_10839,c_10140])).

cnf(c_10905,plain,
    ( k6_relat_1(k1_relat_1(k8_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))),k6_relat_1(X0)))) = k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0)))) ),
    inference(demodulation,[status(thm)],[c_10771,c_5604,c_10846])).

cnf(c_10906,plain,
    ( k6_relat_1(k1_relat_1(k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))))) = k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0)))) ),
    inference(light_normalisation,[status(thm)],[c_10905,c_5603])).

cnf(c_10907,plain,
    ( k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))) = k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0)))) ),
    inference(demodulation,[status(thm)],[c_10906,c_12])).

cnf(c_9,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k8_relat_1(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_536,plain,
    ( k8_relat_1(X0,X1) = X1
    | r1_tarski(k2_relat_1(X1),X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2247,plain,
    ( k8_relat_1(X0,k6_relat_1(X1)) = k6_relat_1(X1)
    | r1_tarski(X1,X0) != iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11,c_536])).

cnf(c_2366,plain,
    ( k8_relat_1(X0,k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))))) = k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))))
    | v1_relat_1(k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1890,c_2247])).

cnf(c_15102,plain,
    ( k8_relat_1(X0,k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))))) = k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0)))) ),
    inference(superposition,[status(thm)],[c_539,c_2366])).

cnf(c_17374,plain,
    ( k8_relat_1(X0,k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))))) = k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0)))) ),
    inference(superposition,[status(thm)],[c_10907,c_15102])).

cnf(c_140846,plain,
    ( k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))) = k8_relat_1(X1,k6_relat_1(X0)) ),
    inference(demodulation,[status(thm)],[c_140842,c_17374])).

cnf(c_9151,plain,
    ( k8_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))),k6_relat_1(X1)) = k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0)))) ),
    inference(superposition,[status(thm)],[c_1896,c_5603])).

cnf(c_2246,plain,
    ( k8_relat_1(k2_relat_1(X0),X0) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_541,c_536])).

cnf(c_5880,plain,
    ( k8_relat_1(k2_relat_1(k8_relat_1(X0,k6_relat_1(X1))),k8_relat_1(X0,k6_relat_1(X1))) = k8_relat_1(X0,k6_relat_1(X1)) ),
    inference(superposition,[status(thm)],[c_5864,c_2246])).

cnf(c_14539,plain,
    ( k8_relat_1(k2_relat_1(k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))))),k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))))) = k8_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))),k6_relat_1(X0)) ),
    inference(superposition,[status(thm)],[c_9151,c_5880])).

cnf(c_14652,plain,
    ( k8_relat_1(k2_relat_1(k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))))),k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))))) = k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))) ),
    inference(demodulation,[status(thm)],[c_14539,c_9151])).

cnf(c_11323,plain,
    ( k2_relat_1(k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))))) = k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))) ),
    inference(superposition,[status(thm)],[c_10907,c_11])).

cnf(c_14653,plain,
    ( k8_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))),k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))))) = k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0)))) ),
    inference(light_normalisation,[status(thm)],[c_14652,c_11323])).

cnf(c_5601,plain,
    ( k8_relat_1(k5_relat_1(k6_relat_1(X0),X1),k6_relat_1(X1)) = k6_relat_1(k5_relat_1(k6_relat_1(X0),X1))
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_534,c_5597])).

cnf(c_7768,plain,
    ( k8_relat_1(k5_relat_1(k6_relat_1(X0),k8_relat_1(X1,k6_relat_1(X2))),k6_relat_1(k8_relat_1(X1,k6_relat_1(X2)))) = k6_relat_1(k5_relat_1(k6_relat_1(X0),k8_relat_1(X1,k6_relat_1(X2)))) ),
    inference(superposition,[status(thm)],[c_5864,c_5601])).

cnf(c_7778,plain,
    ( k8_relat_1(k7_relat_1(k8_relat_1(X0,k6_relat_1(X1)),X2),k6_relat_1(k8_relat_1(X0,k6_relat_1(X1)))) = k6_relat_1(k7_relat_1(k8_relat_1(X0,k6_relat_1(X1)),X2)) ),
    inference(light_normalisation,[status(thm)],[c_7768,c_5885])).

cnf(c_109898,plain,
    ( k8_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))),X2),k6_relat_1(k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))))) = k6_relat_1(k7_relat_1(k8_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))),k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))))),X2)) ),
    inference(superposition,[status(thm)],[c_14653,c_7778])).

cnf(c_11317,plain,
    ( k7_relat_1(k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))),X2) = k8_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))),k6_relat_1(X2)) ),
    inference(superposition,[status(thm)],[c_10907,c_1885])).

cnf(c_110818,plain,
    ( k8_relat_1(k8_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))),k6_relat_1(X2)),k6_relat_1(k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0)))))) = k6_relat_1(k7_relat_1(k8_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))),k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))))),X2)) ),
    inference(light_normalisation,[status(thm)],[c_109898,c_11317])).

cnf(c_29302,plain,
    ( k8_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))),k6_relat_1(X2)) = k8_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))),k6_relat_1(X2)) ),
    inference(superposition,[status(thm)],[c_11317,c_1885])).

cnf(c_41628,plain,
    ( k8_relat_1(k8_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))),k6_relat_1(X2)),k6_relat_1(k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0)))))) = k6_relat_1(k8_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))),k6_relat_1(X2))) ),
    inference(superposition,[status(thm)],[c_29302,c_5606])).

cnf(c_110819,plain,
    ( k6_relat_1(k8_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))),k6_relat_1(X2))) = k6_relat_1(k8_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))),k6_relat_1(X2))) ),
    inference(demodulation,[status(thm)],[c_110818,c_11317,c_14653,c_41628])).

cnf(c_116820,plain,
    ( k1_relat_1(k6_relat_1(k8_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))),k6_relat_1(X2)))) = k8_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))),k6_relat_1(X2)) ),
    inference(superposition,[status(thm)],[c_110819,c_12])).

cnf(c_142487,plain,
    ( k1_relat_1(k6_relat_1(k8_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))),k8_relat_1(X2,k6_relat_1(X3))))) = k8_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))),k6_relat_1(k1_relat_1(k8_relat_1(X3,k6_relat_1(X2))))) ),
    inference(superposition,[status(thm)],[c_140846,c_116820])).

cnf(c_142279,plain,
    ( k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))) = k2_relat_1(k8_relat_1(X1,k6_relat_1(X0))) ),
    inference(superposition,[status(thm)],[c_140846,c_11])).

cnf(c_142692,plain,
    ( k1_relat_1(k6_relat_1(k8_relat_1(k2_relat_1(k8_relat_1(X0,k6_relat_1(X1))),k8_relat_1(X2,k6_relat_1(X3))))) = k8_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))),k6_relat_1(k1_relat_1(k8_relat_1(X3,k6_relat_1(X2))))) ),
    inference(light_normalisation,[status(thm)],[c_142487,c_142279])).

cnf(c_10758,plain,
    ( k8_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))),k6_relat_1(X0)) = k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0)))) ),
    inference(superposition,[status(thm)],[c_1896,c_5604])).

cnf(c_141319,plain,
    ( k8_relat_1(X0,k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))))) = k8_relat_1(X0,k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))))) ),
    inference(superposition,[status(thm)],[c_10758,c_140839])).

cnf(c_2365,plain,
    ( k8_relat_1(X0,k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))))) = k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))))
    | v1_relat_1(k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1889,c_2247])).

cnf(c_13375,plain,
    ( k8_relat_1(X0,k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))))) = k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))) ),
    inference(superposition,[status(thm)],[c_539,c_2365])).

cnf(c_15348,plain,
    ( k8_relat_1(X0,k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))))) = k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))) ),
    inference(superposition,[status(thm)],[c_10907,c_13375])).

cnf(c_141392,plain,
    ( k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))) = k8_relat_1(X0,k6_relat_1(X1)) ),
    inference(light_normalisation,[status(thm)],[c_141319,c_15348,c_17374,c_140846])).

cnf(c_142693,plain,
    ( k8_relat_1(k2_relat_1(k8_relat_1(X0,k6_relat_1(X1))),k8_relat_1(X2,k6_relat_1(X3))) = k8_relat_1(k2_relat_1(k8_relat_1(X1,k6_relat_1(X0))),k8_relat_1(X3,k6_relat_1(X2))) ),
    inference(demodulation,[status(thm)],[c_142692,c_12,c_141392,c_142279])).

cnf(c_142505,plain,
    ( k8_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))),k6_relat_1(k1_relat_1(k8_relat_1(X2,k6_relat_1(X3))))) = k8_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))),k8_relat_1(X3,k6_relat_1(X2))) ),
    inference(superposition,[status(thm)],[c_140846,c_29302])).

cnf(c_142658,plain,
    ( k8_relat_1(k2_relat_1(k8_relat_1(X0,k6_relat_1(X1))),k6_relat_1(k1_relat_1(k8_relat_1(X2,k6_relat_1(X3))))) = k8_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))),k8_relat_1(X3,k6_relat_1(X2))) ),
    inference(light_normalisation,[status(thm)],[c_142505,c_142279])).

cnf(c_141753,plain,
    ( k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))) = k2_relat_1(k8_relat_1(X0,k6_relat_1(X1))) ),
    inference(demodulation,[status(thm)],[c_140846,c_11323])).

cnf(c_11390,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X2))))) = k8_relat_1(k1_relat_1(k8_relat_1(X2,k6_relat_1(X1))),k6_relat_1(X0)) ),
    inference(superposition,[status(thm)],[c_10907,c_1786])).

cnf(c_141804,plain,
    ( k8_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))),k6_relat_1(X2)) = k5_relat_1(k6_relat_1(X2),k8_relat_1(X0,k6_relat_1(X1))) ),
    inference(demodulation,[status(thm)],[c_140846,c_11390])).

cnf(c_140641,plain,
    ( k5_relat_1(k6_relat_1(X0),k8_relat_1(X1,k6_relat_1(X2))) = k8_relat_1(X1,k8_relat_1(X2,k6_relat_1(X0))) ),
    inference(demodulation,[status(thm)],[c_139123,c_5885])).

cnf(c_141805,plain,
    ( k8_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))),k6_relat_1(X2)) = k8_relat_1(X0,k8_relat_1(X1,k6_relat_1(X2))) ),
    inference(demodulation,[status(thm)],[c_141804,c_140641])).

cnf(c_141832,plain,
    ( k8_relat_1(k2_relat_1(k8_relat_1(X0,k6_relat_1(X1))),k6_relat_1(X2)) = k8_relat_1(X0,k8_relat_1(X1,k6_relat_1(X2))) ),
    inference(demodulation,[status(thm)],[c_141753,c_141805])).

cnf(c_142659,plain,
    ( k8_relat_1(k2_relat_1(k8_relat_1(X0,k6_relat_1(X1))),k8_relat_1(X2,k6_relat_1(X3))) = k8_relat_1(X1,k8_relat_1(X0,k8_relat_1(X3,k6_relat_1(X2)))) ),
    inference(demodulation,[status(thm)],[c_142658,c_141392,c_141832,c_142279])).

cnf(c_144583,plain,
    ( k8_relat_1(k2_relat_1(k8_relat_1(X0,k6_relat_1(X1))),k8_relat_1(X2,k6_relat_1(X3))) = k8_relat_1(X0,k8_relat_1(X1,k8_relat_1(X2,k6_relat_1(X3)))) ),
    inference(light_normalisation,[status(thm)],[c_142693,c_142659])).

cnf(c_144587,plain,
    ( k8_relat_1(X0,k8_relat_1(X0,k8_relat_1(X1,k6_relat_1(X2)))) = k8_relat_1(k2_relat_1(k6_relat_1(X0)),k8_relat_1(X1,k6_relat_1(X2))) ),
    inference(superposition,[status(thm)],[c_2071,c_144583])).

cnf(c_144700,plain,
    ( k8_relat_1(X0,k8_relat_1(X0,k8_relat_1(X1,k6_relat_1(X2)))) = k8_relat_1(X0,k8_relat_1(X1,k6_relat_1(X2))) ),
    inference(light_normalisation,[status(thm)],[c_144587,c_11])).

cnf(c_144865,plain,
    ( k8_relat_1(X0,k8_relat_1(X0,k6_relat_1(X1))) = k8_relat_1(X0,k8_relat_1(X1,k6_relat_1(X0))) ),
    inference(superposition,[status(thm)],[c_140839,c_144700])).

cnf(c_140775,plain,
    ( k8_relat_1(X0,k8_relat_1(X0,k6_relat_1(X1))) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(superposition,[status(thm)],[c_2071,c_139123])).

cnf(c_140897,plain,
    ( k8_relat_1(X0,k8_relat_1(X0,k6_relat_1(X1))) = k8_relat_1(X0,k6_relat_1(X1)) ),
    inference(light_normalisation,[status(thm)],[c_140775,c_1885])).

cnf(c_141747,plain,
    ( k8_relat_1(X0,k8_relat_1(X1,k6_relat_1(X0))) = k8_relat_1(X1,k6_relat_1(X0)) ),
    inference(demodulation,[status(thm)],[c_140846,c_13375])).

cnf(c_144914,plain,
    ( k8_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X1,k6_relat_1(X0)) ),
    inference(light_normalisation,[status(thm)],[c_144865,c_140897,c_141747])).

cnf(c_19,negated_conjecture,
    ( k6_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) != k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1115,plain,
    ( k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(sK0),sK1))) != k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) ),
    inference(demodulation,[status(thm)],[c_1006,c_19])).

cnf(c_1887,plain,
    ( k6_relat_1(k1_relat_1(k8_relat_1(sK0,k6_relat_1(sK1)))) != k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) ),
    inference(demodulation,[status(thm)],[c_1885,c_1115])).

cnf(c_1897,plain,
    ( k6_relat_1(k1_relat_1(k8_relat_1(sK0,k6_relat_1(sK1)))) != k8_relat_1(sK0,k6_relat_1(sK1)) ),
    inference(demodulation,[status(thm)],[c_1887,c_1786])).

cnf(c_141668,plain,
    ( k8_relat_1(sK1,k6_relat_1(sK0)) != k8_relat_1(sK0,k6_relat_1(sK1)) ),
    inference(demodulation,[status(thm)],[c_140846,c_1897])).

cnf(c_145116,plain,
    ( k8_relat_1(sK0,k6_relat_1(sK1)) != k8_relat_1(sK0,k6_relat_1(sK1)) ),
    inference(demodulation,[status(thm)],[c_144914,c_141668])).

cnf(c_145122,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_145116])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:30:19 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 43.41/6.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 43.41/6.01  
% 43.41/6.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 43.41/6.01  
% 43.41/6.01  ------  iProver source info
% 43.41/6.01  
% 43.41/6.01  git: date: 2020-06-30 10:37:57 +0100
% 43.41/6.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 43.41/6.01  git: non_committed_changes: false
% 43.41/6.01  git: last_make_outside_of_git: false
% 43.41/6.01  
% 43.41/6.01  ------ 
% 43.41/6.01  
% 43.41/6.01  ------ Input Options
% 43.41/6.01  
% 43.41/6.01  --out_options                           all
% 43.41/6.01  --tptp_safe_out                         true
% 43.41/6.01  --problem_path                          ""
% 43.41/6.01  --include_path                          ""
% 43.41/6.01  --clausifier                            res/vclausify_rel
% 43.41/6.01  --clausifier_options                    ""
% 43.41/6.01  --stdin                                 false
% 43.41/6.01  --stats_out                             all
% 43.41/6.01  
% 43.41/6.01  ------ General Options
% 43.41/6.01  
% 43.41/6.01  --fof                                   false
% 43.41/6.01  --time_out_real                         305.
% 43.41/6.01  --time_out_virtual                      -1.
% 43.41/6.01  --symbol_type_check                     false
% 43.41/6.01  --clausify_out                          false
% 43.41/6.01  --sig_cnt_out                           false
% 43.41/6.01  --trig_cnt_out                          false
% 43.41/6.01  --trig_cnt_out_tolerance                1.
% 43.41/6.01  --trig_cnt_out_sk_spl                   false
% 43.41/6.01  --abstr_cl_out                          false
% 43.41/6.01  
% 43.41/6.01  ------ Global Options
% 43.41/6.01  
% 43.41/6.01  --schedule                              default
% 43.41/6.01  --add_important_lit                     false
% 43.41/6.01  --prop_solver_per_cl                    1000
% 43.41/6.01  --min_unsat_core                        false
% 43.41/6.01  --soft_assumptions                      false
% 43.41/6.01  --soft_lemma_size                       3
% 43.41/6.01  --prop_impl_unit_size                   0
% 43.41/6.01  --prop_impl_unit                        []
% 43.41/6.01  --share_sel_clauses                     true
% 43.41/6.01  --reset_solvers                         false
% 43.41/6.01  --bc_imp_inh                            [conj_cone]
% 43.41/6.01  --conj_cone_tolerance                   3.
% 43.41/6.01  --extra_neg_conj                        none
% 43.41/6.01  --large_theory_mode                     true
% 43.41/6.01  --prolific_symb_bound                   200
% 43.41/6.01  --lt_threshold                          2000
% 43.41/6.01  --clause_weak_htbl                      true
% 43.41/6.01  --gc_record_bc_elim                     false
% 43.41/6.01  
% 43.41/6.01  ------ Preprocessing Options
% 43.41/6.01  
% 43.41/6.01  --preprocessing_flag                    true
% 43.41/6.01  --time_out_prep_mult                    0.1
% 43.41/6.01  --splitting_mode                        input
% 43.41/6.01  --splitting_grd                         true
% 43.41/6.01  --splitting_cvd                         false
% 43.41/6.01  --splitting_cvd_svl                     false
% 43.41/6.01  --splitting_nvd                         32
% 43.41/6.01  --sub_typing                            true
% 43.41/6.01  --prep_gs_sim                           true
% 43.41/6.01  --prep_unflatten                        true
% 43.41/6.01  --prep_res_sim                          true
% 43.41/6.01  --prep_upred                            true
% 43.41/6.01  --prep_sem_filter                       exhaustive
% 43.41/6.01  --prep_sem_filter_out                   false
% 43.41/6.01  --pred_elim                             true
% 43.41/6.01  --res_sim_input                         true
% 43.41/6.01  --eq_ax_congr_red                       true
% 43.41/6.01  --pure_diseq_elim                       true
% 43.41/6.01  --brand_transform                       false
% 43.41/6.01  --non_eq_to_eq                          false
% 43.41/6.01  --prep_def_merge                        true
% 43.41/6.01  --prep_def_merge_prop_impl              false
% 43.41/6.01  --prep_def_merge_mbd                    true
% 43.41/6.01  --prep_def_merge_tr_red                 false
% 43.41/6.01  --prep_def_merge_tr_cl                  false
% 43.41/6.01  --smt_preprocessing                     true
% 43.41/6.01  --smt_ac_axioms                         fast
% 43.41/6.01  --preprocessed_out                      false
% 43.41/6.01  --preprocessed_stats                    false
% 43.41/6.01  
% 43.41/6.01  ------ Abstraction refinement Options
% 43.41/6.01  
% 43.41/6.01  --abstr_ref                             []
% 43.41/6.01  --abstr_ref_prep                        false
% 43.41/6.01  --abstr_ref_until_sat                   false
% 43.41/6.01  --abstr_ref_sig_restrict                funpre
% 43.41/6.01  --abstr_ref_af_restrict_to_split_sk     false
% 43.41/6.01  --abstr_ref_under                       []
% 43.41/6.01  
% 43.41/6.01  ------ SAT Options
% 43.41/6.01  
% 43.41/6.01  --sat_mode                              false
% 43.41/6.01  --sat_fm_restart_options                ""
% 43.41/6.01  --sat_gr_def                            false
% 43.41/6.01  --sat_epr_types                         true
% 43.41/6.01  --sat_non_cyclic_types                  false
% 43.41/6.01  --sat_finite_models                     false
% 43.41/6.01  --sat_fm_lemmas                         false
% 43.41/6.01  --sat_fm_prep                           false
% 43.41/6.01  --sat_fm_uc_incr                        true
% 43.41/6.01  --sat_out_model                         small
% 43.41/6.01  --sat_out_clauses                       false
% 43.41/6.01  
% 43.41/6.01  ------ QBF Options
% 43.41/6.01  
% 43.41/6.01  --qbf_mode                              false
% 43.41/6.01  --qbf_elim_univ                         false
% 43.41/6.01  --qbf_dom_inst                          none
% 43.41/6.01  --qbf_dom_pre_inst                      false
% 43.41/6.01  --qbf_sk_in                             false
% 43.41/6.01  --qbf_pred_elim                         true
% 43.41/6.01  --qbf_split                             512
% 43.41/6.01  
% 43.41/6.01  ------ BMC1 Options
% 43.41/6.01  
% 43.41/6.01  --bmc1_incremental                      false
% 43.41/6.01  --bmc1_axioms                           reachable_all
% 43.41/6.01  --bmc1_min_bound                        0
% 43.41/6.01  --bmc1_max_bound                        -1
% 43.41/6.01  --bmc1_max_bound_default                -1
% 43.41/6.01  --bmc1_symbol_reachability              true
% 43.41/6.01  --bmc1_property_lemmas                  false
% 43.41/6.01  --bmc1_k_induction                      false
% 43.41/6.01  --bmc1_non_equiv_states                 false
% 43.41/6.01  --bmc1_deadlock                         false
% 43.41/6.01  --bmc1_ucm                              false
% 43.41/6.01  --bmc1_add_unsat_core                   none
% 43.41/6.01  --bmc1_unsat_core_children              false
% 43.41/6.01  --bmc1_unsat_core_extrapolate_axioms    false
% 43.41/6.01  --bmc1_out_stat                         full
% 43.41/6.01  --bmc1_ground_init                      false
% 43.41/6.01  --bmc1_pre_inst_next_state              false
% 43.41/6.01  --bmc1_pre_inst_state                   false
% 43.41/6.01  --bmc1_pre_inst_reach_state             false
% 43.41/6.01  --bmc1_out_unsat_core                   false
% 43.41/6.01  --bmc1_aig_witness_out                  false
% 43.41/6.01  --bmc1_verbose                          false
% 43.41/6.01  --bmc1_dump_clauses_tptp                false
% 43.41/6.01  --bmc1_dump_unsat_core_tptp             false
% 43.41/6.01  --bmc1_dump_file                        -
% 43.41/6.01  --bmc1_ucm_expand_uc_limit              128
% 43.41/6.01  --bmc1_ucm_n_expand_iterations          6
% 43.41/6.01  --bmc1_ucm_extend_mode                  1
% 43.41/6.01  --bmc1_ucm_init_mode                    2
% 43.41/6.01  --bmc1_ucm_cone_mode                    none
% 43.41/6.01  --bmc1_ucm_reduced_relation_type        0
% 43.41/6.01  --bmc1_ucm_relax_model                  4
% 43.41/6.01  --bmc1_ucm_full_tr_after_sat            true
% 43.41/6.01  --bmc1_ucm_expand_neg_assumptions       false
% 43.41/6.01  --bmc1_ucm_layered_model                none
% 43.41/6.01  --bmc1_ucm_max_lemma_size               10
% 43.41/6.01  
% 43.41/6.01  ------ AIG Options
% 43.41/6.01  
% 43.41/6.01  --aig_mode                              false
% 43.41/6.01  
% 43.41/6.01  ------ Instantiation Options
% 43.41/6.01  
% 43.41/6.01  --instantiation_flag                    true
% 43.41/6.01  --inst_sos_flag                         true
% 43.41/6.01  --inst_sos_phase                        true
% 43.41/6.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 43.41/6.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 43.41/6.01  --inst_lit_sel_side                     num_symb
% 43.41/6.01  --inst_solver_per_active                1400
% 43.41/6.01  --inst_solver_calls_frac                1.
% 43.41/6.01  --inst_passive_queue_type               priority_queues
% 43.41/6.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 43.41/6.01  --inst_passive_queues_freq              [25;2]
% 43.41/6.01  --inst_dismatching                      true
% 43.41/6.01  --inst_eager_unprocessed_to_passive     true
% 43.41/6.01  --inst_prop_sim_given                   true
% 43.41/6.01  --inst_prop_sim_new                     false
% 43.41/6.01  --inst_subs_new                         false
% 43.41/6.01  --inst_eq_res_simp                      false
% 43.41/6.01  --inst_subs_given                       false
% 43.41/6.01  --inst_orphan_elimination               true
% 43.41/6.01  --inst_learning_loop_flag               true
% 43.41/6.01  --inst_learning_start                   3000
% 43.41/6.01  --inst_learning_factor                  2
% 43.41/6.01  --inst_start_prop_sim_after_learn       3
% 43.41/6.01  --inst_sel_renew                        solver
% 43.41/6.01  --inst_lit_activity_flag                true
% 43.41/6.01  --inst_restr_to_given                   false
% 43.41/6.01  --inst_activity_threshold               500
% 43.41/6.01  --inst_out_proof                        true
% 43.41/6.01  
% 43.41/6.01  ------ Resolution Options
% 43.41/6.01  
% 43.41/6.01  --resolution_flag                       true
% 43.41/6.01  --res_lit_sel                           adaptive
% 43.41/6.01  --res_lit_sel_side                      none
% 43.41/6.01  --res_ordering                          kbo
% 43.41/6.01  --res_to_prop_solver                    active
% 43.41/6.01  --res_prop_simpl_new                    false
% 43.41/6.01  --res_prop_simpl_given                  true
% 43.41/6.01  --res_passive_queue_type                priority_queues
% 43.41/6.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 43.41/6.01  --res_passive_queues_freq               [15;5]
% 43.41/6.01  --res_forward_subs                      full
% 43.41/6.01  --res_backward_subs                     full
% 43.41/6.01  --res_forward_subs_resolution           true
% 43.41/6.01  --res_backward_subs_resolution          true
% 43.41/6.01  --res_orphan_elimination                true
% 43.41/6.01  --res_time_limit                        2.
% 43.41/6.01  --res_out_proof                         true
% 43.41/6.01  
% 43.41/6.01  ------ Superposition Options
% 43.41/6.01  
% 43.41/6.01  --superposition_flag                    true
% 43.41/6.01  --sup_passive_queue_type                priority_queues
% 43.41/6.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 43.41/6.01  --sup_passive_queues_freq               [8;1;4]
% 43.41/6.01  --demod_completeness_check              fast
% 43.41/6.01  --demod_use_ground                      true
% 43.41/6.01  --sup_to_prop_solver                    passive
% 43.41/6.01  --sup_prop_simpl_new                    true
% 43.41/6.01  --sup_prop_simpl_given                  true
% 43.41/6.01  --sup_fun_splitting                     true
% 43.41/6.01  --sup_smt_interval                      50000
% 43.41/6.01  
% 43.41/6.01  ------ Superposition Simplification Setup
% 43.41/6.01  
% 43.41/6.01  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 43.41/6.01  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 43.41/6.01  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 43.41/6.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 43.41/6.01  --sup_full_triv                         [TrivRules;PropSubs]
% 43.41/6.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 43.41/6.01  --sup_full_bw                           [BwDemod;BwSubsumption]
% 43.41/6.01  --sup_immed_triv                        [TrivRules]
% 43.41/6.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 43.41/6.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 43.41/6.01  --sup_immed_bw_main                     []
% 43.41/6.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 43.41/6.01  --sup_input_triv                        [Unflattening;TrivRules]
% 43.41/6.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 43.41/6.01  --sup_input_bw                          []
% 43.41/6.01  
% 43.41/6.01  ------ Combination Options
% 43.41/6.01  
% 43.41/6.01  --comb_res_mult                         3
% 43.41/6.01  --comb_sup_mult                         2
% 43.41/6.01  --comb_inst_mult                        10
% 43.41/6.01  
% 43.41/6.01  ------ Debug Options
% 43.41/6.01  
% 43.41/6.01  --dbg_backtrace                         false
% 43.41/6.01  --dbg_dump_prop_clauses                 false
% 43.41/6.01  --dbg_dump_prop_clauses_file            -
% 43.41/6.01  --dbg_out_stat                          false
% 43.41/6.01  ------ Parsing...
% 43.41/6.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 43.41/6.01  
% 43.41/6.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 43.41/6.01  
% 43.41/6.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 43.41/6.01  
% 43.41/6.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 43.41/6.01  ------ Proving...
% 43.41/6.01  ------ Problem Properties 
% 43.41/6.01  
% 43.41/6.01  
% 43.41/6.01  clauses                                 19
% 43.41/6.01  conjectures                             1
% 43.41/6.01  EPR                                     2
% 43.41/6.01  Horn                                    19
% 43.41/6.01  unary                                   8
% 43.41/6.01  binary                                  7
% 43.41/6.01  lits                                    35
% 43.41/6.01  lits eq                                 13
% 43.41/6.01  fd_pure                                 0
% 43.41/6.01  fd_pseudo                               0
% 43.41/6.01  fd_cond                                 0
% 43.41/6.01  fd_pseudo_cond                          1
% 43.41/6.01  AC symbols                              0
% 43.41/6.01  
% 43.41/6.01  ------ Schedule dynamic 5 is on 
% 43.41/6.01  
% 43.41/6.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 43.41/6.01  
% 43.41/6.01  
% 43.41/6.01  ------ 
% 43.41/6.01  Current options:
% 43.41/6.01  ------ 
% 43.41/6.01  
% 43.41/6.01  ------ Input Options
% 43.41/6.01  
% 43.41/6.01  --out_options                           all
% 43.41/6.01  --tptp_safe_out                         true
% 43.41/6.01  --problem_path                          ""
% 43.41/6.01  --include_path                          ""
% 43.41/6.01  --clausifier                            res/vclausify_rel
% 43.41/6.01  --clausifier_options                    ""
% 43.41/6.01  --stdin                                 false
% 43.41/6.01  --stats_out                             all
% 43.41/6.01  
% 43.41/6.01  ------ General Options
% 43.41/6.01  
% 43.41/6.01  --fof                                   false
% 43.41/6.01  --time_out_real                         305.
% 43.41/6.01  --time_out_virtual                      -1.
% 43.41/6.01  --symbol_type_check                     false
% 43.41/6.01  --clausify_out                          false
% 43.41/6.01  --sig_cnt_out                           false
% 43.41/6.01  --trig_cnt_out                          false
% 43.41/6.01  --trig_cnt_out_tolerance                1.
% 43.41/6.01  --trig_cnt_out_sk_spl                   false
% 43.41/6.01  --abstr_cl_out                          false
% 43.41/6.01  
% 43.41/6.01  ------ Global Options
% 43.41/6.01  
% 43.41/6.01  --schedule                              default
% 43.41/6.01  --add_important_lit                     false
% 43.41/6.01  --prop_solver_per_cl                    1000
% 43.41/6.01  --min_unsat_core                        false
% 43.41/6.01  --soft_assumptions                      false
% 43.41/6.01  --soft_lemma_size                       3
% 43.41/6.01  --prop_impl_unit_size                   0
% 43.41/6.01  --prop_impl_unit                        []
% 43.41/6.01  --share_sel_clauses                     true
% 43.41/6.01  --reset_solvers                         false
% 43.41/6.01  --bc_imp_inh                            [conj_cone]
% 43.41/6.01  --conj_cone_tolerance                   3.
% 43.41/6.01  --extra_neg_conj                        none
% 43.41/6.01  --large_theory_mode                     true
% 43.41/6.01  --prolific_symb_bound                   200
% 43.41/6.01  --lt_threshold                          2000
% 43.41/6.01  --clause_weak_htbl                      true
% 43.41/6.01  --gc_record_bc_elim                     false
% 43.41/6.01  
% 43.41/6.01  ------ Preprocessing Options
% 43.41/6.01  
% 43.41/6.01  --preprocessing_flag                    true
% 43.41/6.01  --time_out_prep_mult                    0.1
% 43.41/6.01  --splitting_mode                        input
% 43.41/6.01  --splitting_grd                         true
% 43.41/6.01  --splitting_cvd                         false
% 43.41/6.01  --splitting_cvd_svl                     false
% 43.41/6.01  --splitting_nvd                         32
% 43.41/6.01  --sub_typing                            true
% 43.41/6.01  --prep_gs_sim                           true
% 43.41/6.01  --prep_unflatten                        true
% 43.41/6.01  --prep_res_sim                          true
% 43.41/6.01  --prep_upred                            true
% 43.41/6.01  --prep_sem_filter                       exhaustive
% 43.41/6.01  --prep_sem_filter_out                   false
% 43.41/6.01  --pred_elim                             true
% 43.41/6.01  --res_sim_input                         true
% 43.41/6.01  --eq_ax_congr_red                       true
% 43.41/6.01  --pure_diseq_elim                       true
% 43.41/6.01  --brand_transform                       false
% 43.41/6.01  --non_eq_to_eq                          false
% 43.41/6.01  --prep_def_merge                        true
% 43.41/6.01  --prep_def_merge_prop_impl              false
% 43.41/6.01  --prep_def_merge_mbd                    true
% 43.41/6.01  --prep_def_merge_tr_red                 false
% 43.41/6.01  --prep_def_merge_tr_cl                  false
% 43.41/6.01  --smt_preprocessing                     true
% 43.41/6.01  --smt_ac_axioms                         fast
% 43.41/6.01  --preprocessed_out                      false
% 43.41/6.01  --preprocessed_stats                    false
% 43.41/6.01  
% 43.41/6.01  ------ Abstraction refinement Options
% 43.41/6.01  
% 43.41/6.01  --abstr_ref                             []
% 43.41/6.01  --abstr_ref_prep                        false
% 43.41/6.01  --abstr_ref_until_sat                   false
% 43.41/6.01  --abstr_ref_sig_restrict                funpre
% 43.41/6.01  --abstr_ref_af_restrict_to_split_sk     false
% 43.41/6.01  --abstr_ref_under                       []
% 43.41/6.01  
% 43.41/6.01  ------ SAT Options
% 43.41/6.01  
% 43.41/6.01  --sat_mode                              false
% 43.41/6.01  --sat_fm_restart_options                ""
% 43.41/6.01  --sat_gr_def                            false
% 43.41/6.01  --sat_epr_types                         true
% 43.41/6.01  --sat_non_cyclic_types                  false
% 43.41/6.01  --sat_finite_models                     false
% 43.41/6.01  --sat_fm_lemmas                         false
% 43.41/6.01  --sat_fm_prep                           false
% 43.41/6.01  --sat_fm_uc_incr                        true
% 43.41/6.01  --sat_out_model                         small
% 43.41/6.01  --sat_out_clauses                       false
% 43.41/6.01  
% 43.41/6.01  ------ QBF Options
% 43.41/6.01  
% 43.41/6.01  --qbf_mode                              false
% 43.41/6.01  --qbf_elim_univ                         false
% 43.41/6.01  --qbf_dom_inst                          none
% 43.41/6.01  --qbf_dom_pre_inst                      false
% 43.41/6.01  --qbf_sk_in                             false
% 43.41/6.01  --qbf_pred_elim                         true
% 43.41/6.01  --qbf_split                             512
% 43.41/6.01  
% 43.41/6.01  ------ BMC1 Options
% 43.41/6.01  
% 43.41/6.01  --bmc1_incremental                      false
% 43.41/6.01  --bmc1_axioms                           reachable_all
% 43.41/6.01  --bmc1_min_bound                        0
% 43.41/6.01  --bmc1_max_bound                        -1
% 43.41/6.01  --bmc1_max_bound_default                -1
% 43.41/6.01  --bmc1_symbol_reachability              true
% 43.41/6.01  --bmc1_property_lemmas                  false
% 43.41/6.01  --bmc1_k_induction                      false
% 43.41/6.01  --bmc1_non_equiv_states                 false
% 43.41/6.01  --bmc1_deadlock                         false
% 43.41/6.01  --bmc1_ucm                              false
% 43.41/6.01  --bmc1_add_unsat_core                   none
% 43.41/6.01  --bmc1_unsat_core_children              false
% 43.41/6.01  --bmc1_unsat_core_extrapolate_axioms    false
% 43.41/6.01  --bmc1_out_stat                         full
% 43.41/6.01  --bmc1_ground_init                      false
% 43.41/6.01  --bmc1_pre_inst_next_state              false
% 43.41/6.01  --bmc1_pre_inst_state                   false
% 43.41/6.01  --bmc1_pre_inst_reach_state             false
% 43.41/6.01  --bmc1_out_unsat_core                   false
% 43.41/6.01  --bmc1_aig_witness_out                  false
% 43.41/6.01  --bmc1_verbose                          false
% 43.41/6.01  --bmc1_dump_clauses_tptp                false
% 43.41/6.01  --bmc1_dump_unsat_core_tptp             false
% 43.41/6.01  --bmc1_dump_file                        -
% 43.41/6.01  --bmc1_ucm_expand_uc_limit              128
% 43.41/6.01  --bmc1_ucm_n_expand_iterations          6
% 43.41/6.01  --bmc1_ucm_extend_mode                  1
% 43.41/6.01  --bmc1_ucm_init_mode                    2
% 43.41/6.01  --bmc1_ucm_cone_mode                    none
% 43.41/6.01  --bmc1_ucm_reduced_relation_type        0
% 43.41/6.01  --bmc1_ucm_relax_model                  4
% 43.41/6.01  --bmc1_ucm_full_tr_after_sat            true
% 43.41/6.01  --bmc1_ucm_expand_neg_assumptions       false
% 43.41/6.01  --bmc1_ucm_layered_model                none
% 43.41/6.01  --bmc1_ucm_max_lemma_size               10
% 43.41/6.01  
% 43.41/6.01  ------ AIG Options
% 43.41/6.01  
% 43.41/6.01  --aig_mode                              false
% 43.41/6.01  
% 43.41/6.01  ------ Instantiation Options
% 43.41/6.01  
% 43.41/6.01  --instantiation_flag                    true
% 43.41/6.01  --inst_sos_flag                         true
% 43.41/6.01  --inst_sos_phase                        true
% 43.41/6.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 43.41/6.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 43.41/6.01  --inst_lit_sel_side                     none
% 43.41/6.01  --inst_solver_per_active                1400
% 43.41/6.01  --inst_solver_calls_frac                1.
% 43.41/6.01  --inst_passive_queue_type               priority_queues
% 43.41/6.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 43.41/6.01  --inst_passive_queues_freq              [25;2]
% 43.41/6.01  --inst_dismatching                      true
% 43.41/6.01  --inst_eager_unprocessed_to_passive     true
% 43.41/6.01  --inst_prop_sim_given                   true
% 43.41/6.01  --inst_prop_sim_new                     false
% 43.41/6.01  --inst_subs_new                         false
% 43.41/6.01  --inst_eq_res_simp                      false
% 43.41/6.01  --inst_subs_given                       false
% 43.41/6.01  --inst_orphan_elimination               true
% 43.41/6.01  --inst_learning_loop_flag               true
% 43.41/6.01  --inst_learning_start                   3000
% 43.41/6.01  --inst_learning_factor                  2
% 43.41/6.01  --inst_start_prop_sim_after_learn       3
% 43.41/6.01  --inst_sel_renew                        solver
% 43.41/6.01  --inst_lit_activity_flag                true
% 43.41/6.01  --inst_restr_to_given                   false
% 43.41/6.01  --inst_activity_threshold               500
% 43.41/6.01  --inst_out_proof                        true
% 43.41/6.01  
% 43.41/6.01  ------ Resolution Options
% 43.41/6.01  
% 43.41/6.01  --resolution_flag                       false
% 43.41/6.01  --res_lit_sel                           adaptive
% 43.41/6.01  --res_lit_sel_side                      none
% 43.41/6.01  --res_ordering                          kbo
% 43.41/6.01  --res_to_prop_solver                    active
% 43.41/6.01  --res_prop_simpl_new                    false
% 43.41/6.01  --res_prop_simpl_given                  true
% 43.41/6.01  --res_passive_queue_type                priority_queues
% 43.41/6.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 43.41/6.01  --res_passive_queues_freq               [15;5]
% 43.41/6.01  --res_forward_subs                      full
% 43.41/6.01  --res_backward_subs                     full
% 43.41/6.01  --res_forward_subs_resolution           true
% 43.41/6.01  --res_backward_subs_resolution          true
% 43.41/6.01  --res_orphan_elimination                true
% 43.41/6.01  --res_time_limit                        2.
% 43.41/6.01  --res_out_proof                         true
% 43.41/6.01  
% 43.41/6.01  ------ Superposition Options
% 43.41/6.01  
% 43.41/6.01  --superposition_flag                    true
% 43.41/6.01  --sup_passive_queue_type                priority_queues
% 43.41/6.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 43.41/6.01  --sup_passive_queues_freq               [8;1;4]
% 43.41/6.01  --demod_completeness_check              fast
% 43.41/6.01  --demod_use_ground                      true
% 43.41/6.01  --sup_to_prop_solver                    passive
% 43.41/6.01  --sup_prop_simpl_new                    true
% 43.41/6.01  --sup_prop_simpl_given                  true
% 43.41/6.01  --sup_fun_splitting                     true
% 43.41/6.01  --sup_smt_interval                      50000
% 43.41/6.01  
% 43.41/6.01  ------ Superposition Simplification Setup
% 43.41/6.01  
% 43.41/6.01  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 43.41/6.01  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 43.41/6.01  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 43.41/6.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 43.41/6.01  --sup_full_triv                         [TrivRules;PropSubs]
% 43.41/6.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 43.41/6.01  --sup_full_bw                           [BwDemod;BwSubsumption]
% 43.41/6.01  --sup_immed_triv                        [TrivRules]
% 43.41/6.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 43.41/6.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 43.41/6.01  --sup_immed_bw_main                     []
% 43.41/6.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 43.41/6.01  --sup_input_triv                        [Unflattening;TrivRules]
% 43.41/6.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 43.41/6.01  --sup_input_bw                          []
% 43.41/6.01  
% 43.41/6.01  ------ Combination Options
% 43.41/6.01  
% 43.41/6.01  --comb_res_mult                         3
% 43.41/6.01  --comb_sup_mult                         2
% 43.41/6.01  --comb_inst_mult                        10
% 43.41/6.01  
% 43.41/6.01  ------ Debug Options
% 43.41/6.01  
% 43.41/6.01  --dbg_backtrace                         false
% 43.41/6.01  --dbg_dump_prop_clauses                 false
% 43.41/6.01  --dbg_dump_prop_clauses_file            -
% 43.41/6.01  --dbg_out_stat                          false
% 43.41/6.01  
% 43.41/6.01  
% 43.41/6.01  
% 43.41/6.01  
% 43.41/6.01  ------ Proving...
% 43.41/6.01  
% 43.41/6.01  
% 43.41/6.01  % SZS status Theorem for theBenchmark.p
% 43.41/6.01  
% 43.41/6.01   Resolution empty clause
% 43.41/6.01  
% 43.41/6.01  % SZS output start CNFRefutation for theBenchmark.p
% 43.41/6.01  
% 43.41/6.01  fof(f8,axiom,(
% 43.41/6.01    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 43.41/6.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.41/6.01  
% 43.41/6.01  fof(f46,plain,(
% 43.41/6.01    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 43.41/6.01    inference(cnf_transformation,[],[f8])).
% 43.41/6.01  
% 43.41/6.01  fof(f12,axiom,(
% 43.41/6.01    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2))))),
% 43.41/6.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.41/6.01  
% 43.41/6.01  fof(f25,plain,(
% 43.41/6.01    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 43.41/6.01    inference(ennf_transformation,[],[f12])).
% 43.41/6.01  
% 43.41/6.01  fof(f50,plain,(
% 43.41/6.01    ( ! [X2,X0,X1] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 43.41/6.01    inference(cnf_transformation,[],[f25])).
% 43.41/6.01  
% 43.41/6.01  fof(f10,axiom,(
% 43.41/6.01    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 43.41/6.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.41/6.01  
% 43.41/6.01  fof(f22,plain,(
% 43.41/6.01    ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 43.41/6.01    inference(ennf_transformation,[],[f10])).
% 43.41/6.01  
% 43.41/6.01  fof(f48,plain,(
% 43.41/6.01    ( ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1)) )),
% 43.41/6.01    inference(cnf_transformation,[],[f22])).
% 43.41/6.01  
% 43.41/6.01  fof(f14,axiom,(
% 43.41/6.01    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)))),
% 43.41/6.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.41/6.01  
% 43.41/6.01  fof(f26,plain,(
% 43.41/6.01    ! [X0,X1] : ((r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)) | ~v1_relat_1(X1))),
% 43.41/6.01    inference(ennf_transformation,[],[f14])).
% 43.41/6.01  
% 43.41/6.01  fof(f54,plain,(
% 43.41/6.01    ( ! [X0,X1] : (r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) | ~v1_relat_1(X1)) )),
% 43.41/6.01    inference(cnf_transformation,[],[f26])).
% 43.41/6.01  
% 43.41/6.01  fof(f13,axiom,(
% 43.41/6.01    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 43.41/6.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.41/6.01  
% 43.41/6.01  fof(f51,plain,(
% 43.41/6.01    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 43.41/6.01    inference(cnf_transformation,[],[f13])).
% 43.41/6.01  
% 43.41/6.01  fof(f15,axiom,(
% 43.41/6.01    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k5_relat_1(k6_relat_1(X0),X1) = X1))),
% 43.41/6.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.41/6.01  
% 43.41/6.01  fof(f27,plain,(
% 43.41/6.01    ! [X0,X1] : ((k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 43.41/6.01    inference(ennf_transformation,[],[f15])).
% 43.41/6.01  
% 43.41/6.01  fof(f28,plain,(
% 43.41/6.01    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 43.41/6.01    inference(flattening,[],[f27])).
% 43.41/6.01  
% 43.41/6.01  fof(f55,plain,(
% 43.41/6.01    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 43.41/6.01    inference(cnf_transformation,[],[f28])).
% 43.41/6.01  
% 43.41/6.01  fof(f18,axiom,(
% 43.41/6.01    ! [X0,X1] : (v1_relat_1(X1) => k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0))),
% 43.41/6.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.41/6.01  
% 43.41/6.01  fof(f31,plain,(
% 43.41/6.01    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 43.41/6.01    inference(ennf_transformation,[],[f18])).
% 43.41/6.01  
% 43.41/6.01  fof(f58,plain,(
% 43.41/6.01    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 43.41/6.01    inference(cnf_transformation,[],[f31])).
% 43.41/6.01  
% 43.41/6.01  fof(f9,axiom,(
% 43.41/6.01    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k3_xboole_0(X0,X1)))),
% 43.41/6.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.41/6.01  
% 43.41/6.01  fof(f21,plain,(
% 43.41/6.01    ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 43.41/6.01    inference(ennf_transformation,[],[f9])).
% 43.41/6.01  
% 43.41/6.01  fof(f47,plain,(
% 43.41/6.01    ( ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0)) )),
% 43.41/6.01    inference(cnf_transformation,[],[f21])).
% 43.41/6.01  
% 43.41/6.01  fof(f4,axiom,(
% 43.41/6.01    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 43.41/6.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.41/6.01  
% 43.41/6.01  fof(f42,plain,(
% 43.41/6.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 43.41/6.01    inference(cnf_transformation,[],[f4])).
% 43.41/6.01  
% 43.41/6.01  fof(f64,plain,(
% 43.41/6.01    ( ! [X0,X1] : (v1_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,X1))) | ~v1_relat_1(X0)) )),
% 43.41/6.01    inference(definition_unfolding,[],[f47,f42])).
% 43.41/6.01  
% 43.41/6.01  fof(f17,axiom,(
% 43.41/6.01    ! [X0,X1] : (v1_relat_1(X1) => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)))),
% 43.41/6.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.41/6.01  
% 43.41/6.01  fof(f30,plain,(
% 43.41/6.01    ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 43.41/6.01    inference(ennf_transformation,[],[f17])).
% 43.41/6.01  
% 43.41/6.01  fof(f57,plain,(
% 43.41/6.01    ( ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 43.41/6.01    inference(cnf_transformation,[],[f30])).
% 43.41/6.01  
% 43.41/6.01  fof(f65,plain,(
% 43.41/6.01    ( ! [X0,X1] : (k4_xboole_0(k1_relat_1(X1),k4_xboole_0(k1_relat_1(X1),X0)) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 43.41/6.01    inference(definition_unfolding,[],[f57,f42])).
% 43.41/6.01  
% 43.41/6.01  fof(f1,axiom,(
% 43.41/6.01    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 43.41/6.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.41/6.01  
% 43.41/6.01  fof(f37,plain,(
% 43.41/6.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 43.41/6.01    inference(cnf_transformation,[],[f1])).
% 43.41/6.01  
% 43.41/6.01  fof(f61,plain,(
% 43.41/6.01    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 43.41/6.01    inference(definition_unfolding,[],[f37,f42,f42])).
% 43.41/6.01  
% 43.41/6.01  fof(f3,axiom,(
% 43.41/6.01    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 43.41/6.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.41/6.01  
% 43.41/6.01  fof(f41,plain,(
% 43.41/6.01    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 43.41/6.01    inference(cnf_transformation,[],[f3])).
% 43.41/6.01  
% 43.41/6.01  fof(f62,plain,(
% 43.41/6.01    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) )),
% 43.41/6.01    inference(definition_unfolding,[],[f41,f42])).
% 43.41/6.01  
% 43.41/6.01  fof(f16,axiom,(
% 43.41/6.01    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 43.41/6.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.41/6.01  
% 43.41/6.01  fof(f29,plain,(
% 43.41/6.01    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 43.41/6.01    inference(ennf_transformation,[],[f16])).
% 43.41/6.01  
% 43.41/6.01  fof(f56,plain,(
% 43.41/6.01    ( ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 43.41/6.01    inference(cnf_transformation,[],[f29])).
% 43.41/6.01  
% 43.41/6.01  fof(f52,plain,(
% 43.41/6.01    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 43.41/6.01    inference(cnf_transformation,[],[f13])).
% 43.41/6.01  
% 43.41/6.01  fof(f2,axiom,(
% 43.41/6.01    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 43.41/6.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.41/6.01  
% 43.41/6.01  fof(f33,plain,(
% 43.41/6.01    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 43.41/6.01    inference(nnf_transformation,[],[f2])).
% 43.41/6.01  
% 43.41/6.01  fof(f34,plain,(
% 43.41/6.01    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 43.41/6.01    inference(flattening,[],[f33])).
% 43.41/6.01  
% 43.41/6.01  fof(f38,plain,(
% 43.41/6.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 43.41/6.01    inference(cnf_transformation,[],[f34])).
% 43.41/6.01  
% 43.41/6.01  fof(f68,plain,(
% 43.41/6.01    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 43.41/6.01    inference(equality_resolution,[],[f38])).
% 43.41/6.01  
% 43.41/6.01  fof(f11,axiom,(
% 43.41/6.01    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k8_relat_1(X0,X1) = X1))),
% 43.41/6.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.41/6.01  
% 43.41/6.01  fof(f23,plain,(
% 43.41/6.01    ! [X0,X1] : ((k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 43.41/6.01    inference(ennf_transformation,[],[f11])).
% 43.41/6.01  
% 43.41/6.01  fof(f24,plain,(
% 43.41/6.01    ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 43.41/6.01    inference(flattening,[],[f23])).
% 43.41/6.01  
% 43.41/6.01  fof(f49,plain,(
% 43.41/6.01    ( ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 43.41/6.01    inference(cnf_transformation,[],[f24])).
% 43.41/6.01  
% 43.41/6.01  fof(f19,conjecture,(
% 43.41/6.01    ! [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))),
% 43.41/6.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.41/6.01  
% 43.41/6.01  fof(f20,negated_conjecture,(
% 43.41/6.01    ~! [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))),
% 43.41/6.01    inference(negated_conjecture,[],[f19])).
% 43.41/6.01  
% 43.41/6.01  fof(f32,plain,(
% 43.41/6.01    ? [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) != k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))),
% 43.41/6.01    inference(ennf_transformation,[],[f20])).
% 43.41/6.01  
% 43.41/6.01  fof(f35,plain,(
% 43.41/6.01    ? [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) != k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) => k6_relat_1(k3_xboole_0(sK0,sK1)) != k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0))),
% 43.41/6.01    introduced(choice_axiom,[])).
% 43.41/6.01  
% 43.41/6.01  fof(f36,plain,(
% 43.41/6.01    k6_relat_1(k3_xboole_0(sK0,sK1)) != k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0))),
% 43.41/6.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f32,f35])).
% 43.41/6.01  
% 43.41/6.01  fof(f59,plain,(
% 43.41/6.01    k6_relat_1(k3_xboole_0(sK0,sK1)) != k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0))),
% 43.41/6.01    inference(cnf_transformation,[],[f36])).
% 43.41/6.01  
% 43.41/6.01  fof(f66,plain,(
% 43.41/6.01    k6_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) != k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0))),
% 43.41/6.01    inference(definition_unfolding,[],[f59,f42])).
% 43.41/6.01  
% 43.41/6.01  cnf(c_6,plain,
% 43.41/6.01      ( v1_relat_1(k6_relat_1(X0)) ),
% 43.41/6.01      inference(cnf_transformation,[],[f46]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_539,plain,
% 43.41/6.01      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 43.41/6.01      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_10,plain,
% 43.41/6.01      ( ~ v1_relat_1(X0)
% 43.41/6.01      | ~ v1_relat_1(X1)
% 43.41/6.01      | ~ v1_relat_1(X2)
% 43.41/6.01      | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ),
% 43.41/6.01      inference(cnf_transformation,[],[f50]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_535,plain,
% 43.41/6.01      ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
% 43.41/6.01      | v1_relat_1(X0) != iProver_top
% 43.41/6.01      | v1_relat_1(X1) != iProver_top
% 43.41/6.01      | v1_relat_1(X2) != iProver_top ),
% 43.41/6.01      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_2173,plain,
% 43.41/6.01      ( k5_relat_1(k6_relat_1(X0),k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(k6_relat_1(X0),X1),X2)
% 43.41/6.01      | v1_relat_1(X1) != iProver_top
% 43.41/6.01      | v1_relat_1(X2) != iProver_top ),
% 43.41/6.01      inference(superposition,[status(thm)],[c_539,c_535]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_8542,plain,
% 43.41/6.01      ( k5_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),X2) = k5_relat_1(k6_relat_1(X0),k5_relat_1(k6_relat_1(X1),X2))
% 43.41/6.01      | v1_relat_1(X2) != iProver_top ),
% 43.41/6.01      inference(superposition,[status(thm)],[c_539,c_2173]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_8,plain,
% 43.41/6.01      ( ~ v1_relat_1(X0) | k5_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X1,X0) ),
% 43.41/6.01      inference(cnf_transformation,[],[f48]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_537,plain,
% 43.41/6.01      ( k5_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X1,X0)
% 43.41/6.01      | v1_relat_1(X0) != iProver_top ),
% 43.41/6.01      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_1786,plain,
% 43.41/6.01      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k8_relat_1(X1,k6_relat_1(X0)) ),
% 43.41/6.01      inference(superposition,[status(thm)],[c_539,c_537]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_8555,plain,
% 43.41/6.01      ( k5_relat_1(k6_relat_1(X0),k5_relat_1(k6_relat_1(X1),X2)) = k5_relat_1(k8_relat_1(X1,k6_relat_1(X0)),X2)
% 43.41/6.01      | v1_relat_1(X2) != iProver_top ),
% 43.41/6.01      inference(light_normalisation,[status(thm)],[c_8542,c_1786]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_138989,plain,
% 43.41/6.01      ( k5_relat_1(k6_relat_1(X0),k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) = k5_relat_1(k8_relat_1(X1,k6_relat_1(X0)),k6_relat_1(X2)) ),
% 43.41/6.01      inference(superposition,[status(thm)],[c_539,c_8555]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_13,plain,
% 43.41/6.01      ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) | ~ v1_relat_1(X1) ),
% 43.41/6.01      inference(cnf_transformation,[],[f54]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_534,plain,
% 43.41/6.01      ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) = iProver_top
% 43.41/6.01      | v1_relat_1(X1) != iProver_top ),
% 43.41/6.01      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_2070,plain,
% 43.41/6.01      ( r1_tarski(k8_relat_1(X0,k6_relat_1(X1)),k6_relat_1(X0)) = iProver_top
% 43.41/6.01      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 43.41/6.01      inference(superposition,[status(thm)],[c_1786,c_534]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_52,plain,
% 43.41/6.01      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 43.41/6.01      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_2817,plain,
% 43.41/6.01      ( r1_tarski(k8_relat_1(X0,k6_relat_1(X1)),k6_relat_1(X0)) = iProver_top ),
% 43.41/6.01      inference(global_propositional_subsumption,[status(thm)],[c_2070,c_52]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_12,plain,
% 43.41/6.01      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 43.41/6.01      inference(cnf_transformation,[],[f51]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_15,plain,
% 43.41/6.01      ( ~ r1_tarski(k1_relat_1(X0),X1)
% 43.41/6.01      | ~ v1_relat_1(X0)
% 43.41/6.01      | k5_relat_1(k6_relat_1(X1),X0) = X0 ),
% 43.41/6.01      inference(cnf_transformation,[],[f55]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_532,plain,
% 43.41/6.01      ( k5_relat_1(k6_relat_1(X0),X1) = X1
% 43.41/6.01      | r1_tarski(k1_relat_1(X1),X0) != iProver_top
% 43.41/6.01      | v1_relat_1(X1) != iProver_top ),
% 43.41/6.01      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_2256,plain,
% 43.41/6.01      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k6_relat_1(X1)
% 43.41/6.01      | r1_tarski(X1,X0) != iProver_top
% 43.41/6.01      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 43.41/6.01      inference(superposition,[status(thm)],[c_12,c_532]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_2257,plain,
% 43.41/6.01      ( k8_relat_1(X0,k6_relat_1(X1)) = k6_relat_1(X0)
% 43.41/6.01      | r1_tarski(X0,X1) != iProver_top
% 43.41/6.01      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 43.41/6.01      inference(demodulation,[status(thm)],[c_2256,c_1786]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_5596,plain,
% 43.41/6.01      ( r1_tarski(X0,X1) != iProver_top
% 43.41/6.01      | k8_relat_1(X0,k6_relat_1(X1)) = k6_relat_1(X0) ),
% 43.41/6.01      inference(global_propositional_subsumption,[status(thm)],[c_2257,c_52]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_5597,plain,
% 43.41/6.01      ( k8_relat_1(X0,k6_relat_1(X1)) = k6_relat_1(X0)
% 43.41/6.01      | r1_tarski(X0,X1) != iProver_top ),
% 43.41/6.01      inference(renaming,[status(thm)],[c_5596]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_5606,plain,
% 43.41/6.01      ( k8_relat_1(k8_relat_1(X0,k6_relat_1(X1)),k6_relat_1(k6_relat_1(X0))) = k6_relat_1(k8_relat_1(X0,k6_relat_1(X1))) ),
% 43.41/6.01      inference(superposition,[status(thm)],[c_2817,c_5597]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_18,plain,
% 43.41/6.01      ( ~ v1_relat_1(X0) | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
% 43.41/6.01      inference(cnf_transformation,[],[f58]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_529,plain,
% 43.41/6.01      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
% 43.41/6.01      | v1_relat_1(X1) != iProver_top ),
% 43.41/6.01      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_1541,plain,
% 43.41/6.01      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
% 43.41/6.01      inference(superposition,[status(thm)],[c_539,c_529]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_1885,plain,
% 43.41/6.01      ( k7_relat_1(k6_relat_1(X0),X1) = k8_relat_1(X0,k6_relat_1(X1)) ),
% 43.41/6.01      inference(light_normalisation,[status(thm)],[c_1541,c_1786]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_7,plain,
% 43.41/6.01      ( ~ v1_relat_1(X0) | v1_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 43.41/6.01      inference(cnf_transformation,[],[f64]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_538,plain,
% 43.41/6.01      ( v1_relat_1(X0) != iProver_top
% 43.41/6.01      | v1_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,X1))) = iProver_top ),
% 43.41/6.01      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_17,plain,
% 43.41/6.01      ( ~ v1_relat_1(X0)
% 43.41/6.01      | k4_xboole_0(k1_relat_1(X0),k4_xboole_0(k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1)) ),
% 43.41/6.01      inference(cnf_transformation,[],[f65]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_530,plain,
% 43.41/6.01      ( k4_xboole_0(k1_relat_1(X0),k4_xboole_0(k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1))
% 43.41/6.01      | v1_relat_1(X0) != iProver_top ),
% 43.41/6.01      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_1005,plain,
% 43.41/6.01      ( k4_xboole_0(k1_relat_1(k6_relat_1(X0)),k4_xboole_0(k1_relat_1(k6_relat_1(X0)),X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
% 43.41/6.01      inference(superposition,[status(thm)],[c_539,c_530]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_1006,plain,
% 43.41/6.01      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
% 43.41/6.01      inference(light_normalisation,[status(thm)],[c_1005,c_12]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_0,plain,
% 43.41/6.01      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 43.41/6.01      inference(cnf_transformation,[],[f61]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_1112,plain,
% 43.41/6.01      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
% 43.41/6.01      inference(demodulation,[status(thm)],[c_1006,c_0]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_1789,plain,
% 43.41/6.01      ( v1_relat_1(X0) != iProver_top
% 43.41/6.01      | v1_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X1),X0))) = iProver_top ),
% 43.41/6.01      inference(light_normalisation,[status(thm)],[c_538,c_1112]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_1893,plain,
% 43.41/6.01      ( v1_relat_1(X0) != iProver_top
% 43.41/6.01      | v1_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0)))) = iProver_top ),
% 43.41/6.01      inference(demodulation,[status(thm)],[c_1885,c_1789]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_5637,plain,
% 43.41/6.01      ( v1_relat_1(k1_relat_1(k6_relat_1(k8_relat_1(X0,k6_relat_1(X1))))) = iProver_top
% 43.41/6.01      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 43.41/6.01      inference(superposition,[status(thm)],[c_5606,c_1893]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_5672,plain,
% 43.41/6.01      ( v1_relat_1(k8_relat_1(X0,k6_relat_1(X1))) = iProver_top
% 43.41/6.01      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 43.41/6.01      inference(demodulation,[status(thm)],[c_5637,c_12]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_5864,plain,
% 43.41/6.01      ( v1_relat_1(k8_relat_1(X0,k6_relat_1(X1))) = iProver_top ),
% 43.41/6.01      inference(global_propositional_subsumption,[status(thm)],[c_5672,c_52]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_5882,plain,
% 43.41/6.01      ( k5_relat_1(k8_relat_1(X0,k6_relat_1(X1)),k6_relat_1(X2)) = k8_relat_1(X2,k8_relat_1(X0,k6_relat_1(X1))) ),
% 43.41/6.01      inference(superposition,[status(thm)],[c_5864,c_537]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_5885,plain,
% 43.41/6.01      ( k5_relat_1(k6_relat_1(X0),k8_relat_1(X1,k6_relat_1(X2))) = k7_relat_1(k8_relat_1(X1,k6_relat_1(X2)),X0) ),
% 43.41/6.01      inference(superposition,[status(thm)],[c_5864,c_529]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_139123,plain,
% 43.41/6.01      ( k7_relat_1(k8_relat_1(X0,k6_relat_1(X1)),X2) = k8_relat_1(X0,k8_relat_1(X1,k6_relat_1(X2))) ),
% 43.41/6.01      inference(demodulation,[status(thm)],[c_138989,c_1786,c_5882,c_5885]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_4,plain,
% 43.41/6.01      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
% 43.41/6.01      inference(cnf_transformation,[],[f62]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_540,plain,
% 43.41/6.01      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = iProver_top ),
% 43.41/6.01      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_1113,plain,
% 43.41/6.01      ( r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X0) = iProver_top ),
% 43.41/6.01      inference(demodulation,[status(thm)],[c_1006,c_540]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_1889,plain,
% 43.41/6.01      ( r1_tarski(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))),X0) = iProver_top ),
% 43.41/6.01      inference(demodulation,[status(thm)],[c_1885,c_1113]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_2254,plain,
% 43.41/6.01      ( k5_relat_1(k6_relat_1(X0),k8_relat_1(X0,k6_relat_1(X1))) = k8_relat_1(X0,k6_relat_1(X1))
% 43.41/6.01      | v1_relat_1(k8_relat_1(X0,k6_relat_1(X1))) != iProver_top ),
% 43.41/6.01      inference(superposition,[status(thm)],[c_1889,c_532]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_5886,plain,
% 43.41/6.01      ( k5_relat_1(k6_relat_1(X0),k8_relat_1(X0,k6_relat_1(X1))) = k8_relat_1(X0,k6_relat_1(X1)) ),
% 43.41/6.01      inference(superposition,[status(thm)],[c_5864,c_2254]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_7061,plain,
% 43.41/6.01      ( k7_relat_1(k8_relat_1(X0,k6_relat_1(X1)),X0) = k8_relat_1(X0,k6_relat_1(X1)) ),
% 43.41/6.01      inference(superposition,[status(thm)],[c_5885,c_5886]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_140839,plain,
% 43.41/6.01      ( k8_relat_1(X0,k8_relat_1(X1,k6_relat_1(X0))) = k8_relat_1(X0,k6_relat_1(X1)) ),
% 43.41/6.01      inference(superposition,[status(thm)],[c_139123,c_7061]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_16,plain,
% 43.41/6.01      ( ~ v1_relat_1(X0) | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ),
% 43.41/6.01      inference(cnf_transformation,[],[f56]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_531,plain,
% 43.41/6.01      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
% 43.41/6.01      | v1_relat_1(X0) != iProver_top ),
% 43.41/6.01      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_1500,plain,
% 43.41/6.01      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(k2_relat_1(k6_relat_1(X0)))) = k6_relat_1(X0) ),
% 43.41/6.01      inference(superposition,[status(thm)],[c_539,c_531]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_11,plain,
% 43.41/6.01      ( k2_relat_1(k6_relat_1(X0)) = X0 ),
% 43.41/6.01      inference(cnf_transformation,[],[f52]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_1501,plain,
% 43.41/6.01      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X0)) = k6_relat_1(X0) ),
% 43.41/6.01      inference(light_normalisation,[status(thm)],[c_1500,c_11]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_2071,plain,
% 43.41/6.01      ( k8_relat_1(X0,k6_relat_1(X0)) = k6_relat_1(X0) ),
% 43.41/6.01      inference(superposition,[status(thm)],[c_1786,c_1501]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_3,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f68]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_541,plain,
% 43.41/6.01      ( r1_tarski(X0,X0) = iProver_top ),
% 43.41/6.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_1192,plain,
% 43.41/6.01      ( k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
% 43.41/6.01      inference(superposition,[status(thm)],[c_1112,c_1006]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_1888,plain,
% 43.41/6.01      ( k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))) = k1_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
% 43.41/6.01      inference(demodulation,[status(thm)],[c_1885,c_1192]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_1896,plain,
% 43.41/6.01      ( k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))) = k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))) ),
% 43.41/6.01      inference(demodulation,[status(thm)],[c_1888,c_1885]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_2439,plain,
% 43.41/6.01      ( k5_relat_1(k6_relat_1(X0),k8_relat_1(X1,k6_relat_1(X2))) = k8_relat_1(X1,k6_relat_1(X2))
% 43.41/6.01      | r1_tarski(k1_relat_1(k8_relat_1(X2,k6_relat_1(X1))),X0) != iProver_top
% 43.41/6.01      | v1_relat_1(k8_relat_1(X1,k6_relat_1(X2))) != iProver_top ),
% 43.41/6.01      inference(superposition,[status(thm)],[c_1896,c_532]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_17178,plain,
% 43.41/6.01      ( k7_relat_1(k8_relat_1(X0,k6_relat_1(X1)),X2) = k8_relat_1(X0,k6_relat_1(X1))
% 43.41/6.01      | r1_tarski(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))),X2) != iProver_top
% 43.41/6.01      | v1_relat_1(k8_relat_1(X0,k6_relat_1(X1))) != iProver_top ),
% 43.41/6.01      inference(demodulation,[status(thm)],[c_2439,c_5885]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_17180,plain,
% 43.41/6.01      ( r1_tarski(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))),X2) != iProver_top
% 43.41/6.01      | k7_relat_1(k8_relat_1(X0,k6_relat_1(X1)),X2) = k8_relat_1(X0,k6_relat_1(X1)) ),
% 43.41/6.01      inference(global_propositional_subsumption,
% 43.41/6.01                [status(thm)],
% 43.41/6.01                [c_17178,c_52,c_5672]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_17181,plain,
% 43.41/6.01      ( k7_relat_1(k8_relat_1(X0,k6_relat_1(X1)),X2) = k8_relat_1(X0,k6_relat_1(X1))
% 43.41/6.01      | r1_tarski(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))),X2) != iProver_top ),
% 43.41/6.01      inference(renaming,[status(thm)],[c_17180]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_17184,plain,
% 43.41/6.01      ( k7_relat_1(k8_relat_1(X0,k6_relat_1(X1)),k1_relat_1(k8_relat_1(X1,k6_relat_1(X0)))) = k8_relat_1(X0,k6_relat_1(X1)) ),
% 43.41/6.01      inference(superposition,[status(thm)],[c_541,c_17181]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_140842,plain,
% 43.41/6.01      ( k8_relat_1(X0,k8_relat_1(X1,k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0)))))) = k8_relat_1(X0,k6_relat_1(X1)) ),
% 43.41/6.01      inference(superposition,[status(thm)],[c_139123,c_17184]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_5603,plain,
% 43.41/6.01      ( k8_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))),k6_relat_1(X0)) = k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))) ),
% 43.41/6.01      inference(superposition,[status(thm)],[c_1889,c_5597]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_891,plain,
% 43.41/6.01      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = iProver_top ),
% 43.41/6.01      inference(superposition,[status(thm)],[c_0,c_540]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_1111,plain,
% 43.41/6.01      ( r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X1) = iProver_top ),
% 43.41/6.01      inference(demodulation,[status(thm)],[c_1006,c_891]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_1890,plain,
% 43.41/6.01      ( r1_tarski(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))),X1) = iProver_top ),
% 43.41/6.01      inference(demodulation,[status(thm)],[c_1885,c_1111]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_5604,plain,
% 43.41/6.01      ( k8_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))),k6_relat_1(X1)) = k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))) ),
% 43.41/6.01      inference(superposition,[status(thm)],[c_1890,c_5597]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_10771,plain,
% 43.41/6.01      ( k8_relat_1(k1_relat_1(k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))))),k6_relat_1(X0)) = k6_relat_1(k1_relat_1(k8_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))),k6_relat_1(X0)))) ),
% 43.41/6.01      inference(superposition,[status(thm)],[c_5603,c_5604]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_10839,plain,
% 43.41/6.01      ( k1_relat_1(k8_relat_1(X0,k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0)))))) = k1_relat_1(k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))))) ),
% 43.41/6.01      inference(superposition,[status(thm)],[c_5604,c_1896]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_9222,plain,
% 43.41/6.01      ( k1_relat_1(k8_relat_1(X0,k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))))) = k1_relat_1(k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))))) ),
% 43.41/6.01      inference(superposition,[status(thm)],[c_5603,c_1896]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_9230,plain,
% 43.41/6.01      ( k1_relat_1(k8_relat_1(X0,k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))))) = k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))) ),
% 43.41/6.01      inference(demodulation,[status(thm)],[c_9222,c_12]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_1891,plain,
% 43.41/6.01      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))) ),
% 43.41/6.01      inference(demodulation,[status(thm)],[c_1885,c_1006]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_2118,plain,
% 43.41/6.01      ( k1_relat_1(k8_relat_1(X0,k6_relat_1(k4_xboole_0(X0,X1)))) = k4_xboole_0(X0,k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))) ),
% 43.41/6.01      inference(superposition,[status(thm)],[c_1891,c_1891]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_2914,plain,
% 43.41/6.01      ( k4_xboole_0(X0,k1_relat_1(k8_relat_1(X0,k6_relat_1(k4_xboole_0(X0,X1))))) = k1_relat_1(k8_relat_1(X0,k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))))) ),
% 43.41/6.01      inference(superposition,[status(thm)],[c_2118,c_1891]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_3784,plain,
% 43.41/6.01      ( k1_relat_1(k8_relat_1(X0,k6_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = k1_relat_1(k8_relat_1(X0,k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))))) ),
% 43.41/6.01      inference(superposition,[status(thm)],[c_2914,c_2118]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_1894,plain,
% 43.41/6.01      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))) ),
% 43.41/6.01      inference(demodulation,[status(thm)],[c_1885,c_1112]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_3785,plain,
% 43.41/6.01      ( k1_relat_1(k8_relat_1(X0,k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0)))))) = k1_relat_1(k8_relat_1(X0,k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))))) ),
% 43.41/6.01      inference(light_normalisation,[status(thm)],[c_3784,c_1894]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_10140,plain,
% 43.41/6.01      ( k1_relat_1(k8_relat_1(X0,k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0)))))) = k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))) ),
% 43.41/6.01      inference(demodulation,[status(thm)],[c_9230,c_3785]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_10846,plain,
% 43.41/6.01      ( k1_relat_1(k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))))) = k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))) ),
% 43.41/6.01      inference(light_normalisation,[status(thm)],[c_10839,c_10140]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_10905,plain,
% 43.41/6.01      ( k6_relat_1(k1_relat_1(k8_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))),k6_relat_1(X0)))) = k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0)))) ),
% 43.41/6.01      inference(demodulation,[status(thm)],[c_10771,c_5604,c_10846]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_10906,plain,
% 43.41/6.01      ( k6_relat_1(k1_relat_1(k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))))) = k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0)))) ),
% 43.41/6.01      inference(light_normalisation,[status(thm)],[c_10905,c_5603]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_10907,plain,
% 43.41/6.01      ( k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))) = k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0)))) ),
% 43.41/6.01      inference(demodulation,[status(thm)],[c_10906,c_12]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_9,plain,
% 43.41/6.01      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 43.41/6.01      | ~ v1_relat_1(X0)
% 43.41/6.01      | k8_relat_1(X1,X0) = X0 ),
% 43.41/6.01      inference(cnf_transformation,[],[f49]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_536,plain,
% 43.41/6.01      ( k8_relat_1(X0,X1) = X1
% 43.41/6.01      | r1_tarski(k2_relat_1(X1),X0) != iProver_top
% 43.41/6.01      | v1_relat_1(X1) != iProver_top ),
% 43.41/6.01      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_2247,plain,
% 43.41/6.01      ( k8_relat_1(X0,k6_relat_1(X1)) = k6_relat_1(X1)
% 43.41/6.01      | r1_tarski(X1,X0) != iProver_top
% 43.41/6.01      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 43.41/6.01      inference(superposition,[status(thm)],[c_11,c_536]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_2366,plain,
% 43.41/6.01      ( k8_relat_1(X0,k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))))) = k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))))
% 43.41/6.01      | v1_relat_1(k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))))) != iProver_top ),
% 43.41/6.01      inference(superposition,[status(thm)],[c_1890,c_2247]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_15102,plain,
% 43.41/6.01      ( k8_relat_1(X0,k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))))) = k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0)))) ),
% 43.41/6.01      inference(superposition,[status(thm)],[c_539,c_2366]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_17374,plain,
% 43.41/6.01      ( k8_relat_1(X0,k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))))) = k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0)))) ),
% 43.41/6.01      inference(superposition,[status(thm)],[c_10907,c_15102]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_140846,plain,
% 43.41/6.01      ( k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))) = k8_relat_1(X1,k6_relat_1(X0)) ),
% 43.41/6.01      inference(demodulation,[status(thm)],[c_140842,c_17374]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_9151,plain,
% 43.41/6.01      ( k8_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))),k6_relat_1(X1)) = k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0)))) ),
% 43.41/6.01      inference(superposition,[status(thm)],[c_1896,c_5603]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_2246,plain,
% 43.41/6.01      ( k8_relat_1(k2_relat_1(X0),X0) = X0 | v1_relat_1(X0) != iProver_top ),
% 43.41/6.01      inference(superposition,[status(thm)],[c_541,c_536]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_5880,plain,
% 43.41/6.01      ( k8_relat_1(k2_relat_1(k8_relat_1(X0,k6_relat_1(X1))),k8_relat_1(X0,k6_relat_1(X1))) = k8_relat_1(X0,k6_relat_1(X1)) ),
% 43.41/6.01      inference(superposition,[status(thm)],[c_5864,c_2246]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_14539,plain,
% 43.41/6.01      ( k8_relat_1(k2_relat_1(k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))))),k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))))) = k8_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))),k6_relat_1(X0)) ),
% 43.41/6.01      inference(superposition,[status(thm)],[c_9151,c_5880]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_14652,plain,
% 43.41/6.01      ( k8_relat_1(k2_relat_1(k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))))),k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))))) = k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))) ),
% 43.41/6.01      inference(demodulation,[status(thm)],[c_14539,c_9151]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_11323,plain,
% 43.41/6.01      ( k2_relat_1(k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))))) = k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))) ),
% 43.41/6.01      inference(superposition,[status(thm)],[c_10907,c_11]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_14653,plain,
% 43.41/6.01      ( k8_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))),k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))))) = k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0)))) ),
% 43.41/6.01      inference(light_normalisation,[status(thm)],[c_14652,c_11323]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_5601,plain,
% 43.41/6.01      ( k8_relat_1(k5_relat_1(k6_relat_1(X0),X1),k6_relat_1(X1)) = k6_relat_1(k5_relat_1(k6_relat_1(X0),X1))
% 43.41/6.01      | v1_relat_1(X1) != iProver_top ),
% 43.41/6.01      inference(superposition,[status(thm)],[c_534,c_5597]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_7768,plain,
% 43.41/6.01      ( k8_relat_1(k5_relat_1(k6_relat_1(X0),k8_relat_1(X1,k6_relat_1(X2))),k6_relat_1(k8_relat_1(X1,k6_relat_1(X2)))) = k6_relat_1(k5_relat_1(k6_relat_1(X0),k8_relat_1(X1,k6_relat_1(X2)))) ),
% 43.41/6.01      inference(superposition,[status(thm)],[c_5864,c_5601]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_7778,plain,
% 43.41/6.01      ( k8_relat_1(k7_relat_1(k8_relat_1(X0,k6_relat_1(X1)),X2),k6_relat_1(k8_relat_1(X0,k6_relat_1(X1)))) = k6_relat_1(k7_relat_1(k8_relat_1(X0,k6_relat_1(X1)),X2)) ),
% 43.41/6.01      inference(light_normalisation,[status(thm)],[c_7768,c_5885]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_109898,plain,
% 43.41/6.01      ( k8_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))),X2),k6_relat_1(k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))))) = k6_relat_1(k7_relat_1(k8_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))),k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))))),X2)) ),
% 43.41/6.01      inference(superposition,[status(thm)],[c_14653,c_7778]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_11317,plain,
% 43.41/6.01      ( k7_relat_1(k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))),X2) = k8_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))),k6_relat_1(X2)) ),
% 43.41/6.01      inference(superposition,[status(thm)],[c_10907,c_1885]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_110818,plain,
% 43.41/6.01      ( k8_relat_1(k8_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))),k6_relat_1(X2)),k6_relat_1(k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0)))))) = k6_relat_1(k7_relat_1(k8_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))),k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))))),X2)) ),
% 43.41/6.01      inference(light_normalisation,[status(thm)],[c_109898,c_11317]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_29302,plain,
% 43.41/6.01      ( k8_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))),k6_relat_1(X2)) = k8_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))),k6_relat_1(X2)) ),
% 43.41/6.01      inference(superposition,[status(thm)],[c_11317,c_1885]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_41628,plain,
% 43.41/6.01      ( k8_relat_1(k8_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))),k6_relat_1(X2)),k6_relat_1(k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0)))))) = k6_relat_1(k8_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))),k6_relat_1(X2))) ),
% 43.41/6.01      inference(superposition,[status(thm)],[c_29302,c_5606]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_110819,plain,
% 43.41/6.01      ( k6_relat_1(k8_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))),k6_relat_1(X2))) = k6_relat_1(k8_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))),k6_relat_1(X2))) ),
% 43.41/6.01      inference(demodulation,[status(thm)],[c_110818,c_11317,c_14653,c_41628]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_116820,plain,
% 43.41/6.01      ( k1_relat_1(k6_relat_1(k8_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))),k6_relat_1(X2)))) = k8_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))),k6_relat_1(X2)) ),
% 43.41/6.01      inference(superposition,[status(thm)],[c_110819,c_12]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_142487,plain,
% 43.41/6.01      ( k1_relat_1(k6_relat_1(k8_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))),k8_relat_1(X2,k6_relat_1(X3))))) = k8_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))),k6_relat_1(k1_relat_1(k8_relat_1(X3,k6_relat_1(X2))))) ),
% 43.41/6.01      inference(superposition,[status(thm)],[c_140846,c_116820]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_142279,plain,
% 43.41/6.01      ( k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))) = k2_relat_1(k8_relat_1(X1,k6_relat_1(X0))) ),
% 43.41/6.01      inference(superposition,[status(thm)],[c_140846,c_11]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_142692,plain,
% 43.41/6.01      ( k1_relat_1(k6_relat_1(k8_relat_1(k2_relat_1(k8_relat_1(X0,k6_relat_1(X1))),k8_relat_1(X2,k6_relat_1(X3))))) = k8_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))),k6_relat_1(k1_relat_1(k8_relat_1(X3,k6_relat_1(X2))))) ),
% 43.41/6.01      inference(light_normalisation,[status(thm)],[c_142487,c_142279]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_10758,plain,
% 43.41/6.01      ( k8_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))),k6_relat_1(X0)) = k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0)))) ),
% 43.41/6.01      inference(superposition,[status(thm)],[c_1896,c_5604]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_141319,plain,
% 43.41/6.01      ( k8_relat_1(X0,k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))))) = k8_relat_1(X0,k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))))) ),
% 43.41/6.01      inference(superposition,[status(thm)],[c_10758,c_140839]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_2365,plain,
% 43.41/6.01      ( k8_relat_1(X0,k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))))) = k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))))
% 43.41/6.01      | v1_relat_1(k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))))) != iProver_top ),
% 43.41/6.01      inference(superposition,[status(thm)],[c_1889,c_2247]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_13375,plain,
% 43.41/6.01      ( k8_relat_1(X0,k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))))) = k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))) ),
% 43.41/6.01      inference(superposition,[status(thm)],[c_539,c_2365]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_15348,plain,
% 43.41/6.01      ( k8_relat_1(X0,k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))))) = k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))) ),
% 43.41/6.01      inference(superposition,[status(thm)],[c_10907,c_13375]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_141392,plain,
% 43.41/6.01      ( k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))) = k8_relat_1(X0,k6_relat_1(X1)) ),
% 43.41/6.01      inference(light_normalisation,
% 43.41/6.01                [status(thm)],
% 43.41/6.01                [c_141319,c_15348,c_17374,c_140846]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_142693,plain,
% 43.41/6.01      ( k8_relat_1(k2_relat_1(k8_relat_1(X0,k6_relat_1(X1))),k8_relat_1(X2,k6_relat_1(X3))) = k8_relat_1(k2_relat_1(k8_relat_1(X1,k6_relat_1(X0))),k8_relat_1(X3,k6_relat_1(X2))) ),
% 43.41/6.01      inference(demodulation,[status(thm)],[c_142692,c_12,c_141392,c_142279]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_142505,plain,
% 43.41/6.01      ( k8_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))),k6_relat_1(k1_relat_1(k8_relat_1(X2,k6_relat_1(X3))))) = k8_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))),k8_relat_1(X3,k6_relat_1(X2))) ),
% 43.41/6.01      inference(superposition,[status(thm)],[c_140846,c_29302]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_142658,plain,
% 43.41/6.01      ( k8_relat_1(k2_relat_1(k8_relat_1(X0,k6_relat_1(X1))),k6_relat_1(k1_relat_1(k8_relat_1(X2,k6_relat_1(X3))))) = k8_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))),k8_relat_1(X3,k6_relat_1(X2))) ),
% 43.41/6.01      inference(light_normalisation,[status(thm)],[c_142505,c_142279]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_141753,plain,
% 43.41/6.01      ( k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))) = k2_relat_1(k8_relat_1(X0,k6_relat_1(X1))) ),
% 43.41/6.01      inference(demodulation,[status(thm)],[c_140846,c_11323]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_11390,plain,
% 43.41/6.01      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(k1_relat_1(k8_relat_1(X1,k6_relat_1(X2))))) = k8_relat_1(k1_relat_1(k8_relat_1(X2,k6_relat_1(X1))),k6_relat_1(X0)) ),
% 43.41/6.01      inference(superposition,[status(thm)],[c_10907,c_1786]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_141804,plain,
% 43.41/6.01      ( k8_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))),k6_relat_1(X2)) = k5_relat_1(k6_relat_1(X2),k8_relat_1(X0,k6_relat_1(X1))) ),
% 43.41/6.01      inference(demodulation,[status(thm)],[c_140846,c_11390]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_140641,plain,
% 43.41/6.01      ( k5_relat_1(k6_relat_1(X0),k8_relat_1(X1,k6_relat_1(X2))) = k8_relat_1(X1,k8_relat_1(X2,k6_relat_1(X0))) ),
% 43.41/6.01      inference(demodulation,[status(thm)],[c_139123,c_5885]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_141805,plain,
% 43.41/6.01      ( k8_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))),k6_relat_1(X2)) = k8_relat_1(X0,k8_relat_1(X1,k6_relat_1(X2))) ),
% 43.41/6.01      inference(demodulation,[status(thm)],[c_141804,c_140641]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_141832,plain,
% 43.41/6.01      ( k8_relat_1(k2_relat_1(k8_relat_1(X0,k6_relat_1(X1))),k6_relat_1(X2)) = k8_relat_1(X0,k8_relat_1(X1,k6_relat_1(X2))) ),
% 43.41/6.01      inference(demodulation,[status(thm)],[c_141753,c_141805]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_142659,plain,
% 43.41/6.01      ( k8_relat_1(k2_relat_1(k8_relat_1(X0,k6_relat_1(X1))),k8_relat_1(X2,k6_relat_1(X3))) = k8_relat_1(X1,k8_relat_1(X0,k8_relat_1(X3,k6_relat_1(X2)))) ),
% 43.41/6.01      inference(demodulation,
% 43.41/6.01                [status(thm)],
% 43.41/6.01                [c_142658,c_141392,c_141832,c_142279]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_144583,plain,
% 43.41/6.01      ( k8_relat_1(k2_relat_1(k8_relat_1(X0,k6_relat_1(X1))),k8_relat_1(X2,k6_relat_1(X3))) = k8_relat_1(X0,k8_relat_1(X1,k8_relat_1(X2,k6_relat_1(X3)))) ),
% 43.41/6.01      inference(light_normalisation,[status(thm)],[c_142693,c_142659]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_144587,plain,
% 43.41/6.01      ( k8_relat_1(X0,k8_relat_1(X0,k8_relat_1(X1,k6_relat_1(X2)))) = k8_relat_1(k2_relat_1(k6_relat_1(X0)),k8_relat_1(X1,k6_relat_1(X2))) ),
% 43.41/6.01      inference(superposition,[status(thm)],[c_2071,c_144583]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_144700,plain,
% 43.41/6.01      ( k8_relat_1(X0,k8_relat_1(X0,k8_relat_1(X1,k6_relat_1(X2)))) = k8_relat_1(X0,k8_relat_1(X1,k6_relat_1(X2))) ),
% 43.41/6.01      inference(light_normalisation,[status(thm)],[c_144587,c_11]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_144865,plain,
% 43.41/6.01      ( k8_relat_1(X0,k8_relat_1(X0,k6_relat_1(X1))) = k8_relat_1(X0,k8_relat_1(X1,k6_relat_1(X0))) ),
% 43.41/6.01      inference(superposition,[status(thm)],[c_140839,c_144700]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_140775,plain,
% 43.41/6.01      ( k8_relat_1(X0,k8_relat_1(X0,k6_relat_1(X1))) = k7_relat_1(k6_relat_1(X0),X1) ),
% 43.41/6.01      inference(superposition,[status(thm)],[c_2071,c_139123]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_140897,plain,
% 43.41/6.01      ( k8_relat_1(X0,k8_relat_1(X0,k6_relat_1(X1))) = k8_relat_1(X0,k6_relat_1(X1)) ),
% 43.41/6.01      inference(light_normalisation,[status(thm)],[c_140775,c_1885]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_141747,plain,
% 43.41/6.01      ( k8_relat_1(X0,k8_relat_1(X1,k6_relat_1(X0))) = k8_relat_1(X1,k6_relat_1(X0)) ),
% 43.41/6.01      inference(demodulation,[status(thm)],[c_140846,c_13375]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_144914,plain,
% 43.41/6.01      ( k8_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X1,k6_relat_1(X0)) ),
% 43.41/6.01      inference(light_normalisation,[status(thm)],[c_144865,c_140897,c_141747]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_19,negated_conjecture,
% 43.41/6.01      ( k6_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) != k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) ),
% 43.41/6.01      inference(cnf_transformation,[],[f66]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_1115,plain,
% 43.41/6.01      ( k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(sK0),sK1))) != k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) ),
% 43.41/6.01      inference(demodulation,[status(thm)],[c_1006,c_19]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_1887,plain,
% 43.41/6.01      ( k6_relat_1(k1_relat_1(k8_relat_1(sK0,k6_relat_1(sK1)))) != k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) ),
% 43.41/6.01      inference(demodulation,[status(thm)],[c_1885,c_1115]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_1897,plain,
% 43.41/6.01      ( k6_relat_1(k1_relat_1(k8_relat_1(sK0,k6_relat_1(sK1)))) != k8_relat_1(sK0,k6_relat_1(sK1)) ),
% 43.41/6.01      inference(demodulation,[status(thm)],[c_1887,c_1786]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_141668,plain,
% 43.41/6.01      ( k8_relat_1(sK1,k6_relat_1(sK0)) != k8_relat_1(sK0,k6_relat_1(sK1)) ),
% 43.41/6.01      inference(demodulation,[status(thm)],[c_140846,c_1897]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_145116,plain,
% 43.41/6.01      ( k8_relat_1(sK0,k6_relat_1(sK1)) != k8_relat_1(sK0,k6_relat_1(sK1)) ),
% 43.41/6.01      inference(demodulation,[status(thm)],[c_144914,c_141668]) ).
% 43.41/6.01  
% 43.41/6.01  cnf(c_145122,plain,
% 43.41/6.01      ( $false ),
% 43.41/6.01      inference(equality_resolution_simp,[status(thm)],[c_145116]) ).
% 43.41/6.01  
% 43.41/6.01  
% 43.41/6.01  % SZS output end CNFRefutation for theBenchmark.p
% 43.41/6.01  
% 43.41/6.01  ------                               Statistics
% 43.41/6.01  
% 43.41/6.01  ------ General
% 43.41/6.01  
% 43.41/6.01  abstr_ref_over_cycles:                  0
% 43.41/6.01  abstr_ref_under_cycles:                 0
% 43.41/6.01  gc_basic_clause_elim:                   0
% 43.41/6.01  forced_gc_time:                         0
% 43.41/6.01  parsing_time:                           0.011
% 43.41/6.01  unif_index_cands_time:                  0.
% 43.41/6.01  unif_index_add_time:                    0.
% 43.41/6.01  orderings_time:                         0.
% 43.41/6.01  out_proof_time:                         0.015
% 43.41/6.01  total_time:                             5.401
% 43.41/6.01  num_of_symbols:                         44
% 43.41/6.01  num_of_terms:                           210636
% 43.41/6.01  
% 43.41/6.01  ------ Preprocessing
% 43.41/6.01  
% 43.41/6.01  num_of_splits:                          0
% 43.41/6.01  num_of_split_atoms:                     0
% 43.41/6.01  num_of_reused_defs:                     0
% 43.41/6.01  num_eq_ax_congr_red:                    27
% 43.41/6.01  num_of_sem_filtered_clauses:            1
% 43.41/6.01  num_of_subtypes:                        0
% 43.41/6.01  monotx_restored_types:                  0
% 43.41/6.01  sat_num_of_epr_types:                   0
% 43.41/6.01  sat_num_of_non_cyclic_types:            0
% 43.41/6.01  sat_guarded_non_collapsed_types:        0
% 43.41/6.01  num_pure_diseq_elim:                    0
% 43.41/6.01  simp_replaced_by:                       0
% 43.41/6.01  res_preprocessed:                       97
% 43.41/6.01  prep_upred:                             0
% 43.41/6.01  prep_unflattend:                        0
% 43.41/6.01  smt_new_axioms:                         0
% 43.41/6.01  pred_elim_cands:                        2
% 43.41/6.01  pred_elim:                              0
% 43.41/6.01  pred_elim_cl:                           0
% 43.41/6.01  pred_elim_cycles:                       2
% 43.41/6.01  merged_defs:                            0
% 43.41/6.01  merged_defs_ncl:                        0
% 43.41/6.01  bin_hyper_res:                          0
% 43.41/6.01  prep_cycles:                            4
% 43.41/6.01  pred_elim_time:                         0.
% 43.41/6.01  splitting_time:                         0.
% 43.41/6.01  sem_filter_time:                        0.
% 43.41/6.01  monotx_time:                            0.001
% 43.41/6.01  subtype_inf_time:                       0.
% 43.41/6.01  
% 43.41/6.01  ------ Problem properties
% 43.41/6.01  
% 43.41/6.01  clauses:                                19
% 43.41/6.01  conjectures:                            1
% 43.41/6.01  epr:                                    2
% 43.41/6.01  horn:                                   19
% 43.41/6.01  ground:                                 1
% 43.41/6.01  unary:                                  8
% 43.41/6.01  binary:                                 7
% 43.41/6.01  lits:                                   35
% 43.41/6.01  lits_eq:                                13
% 43.41/6.01  fd_pure:                                0
% 43.41/6.01  fd_pseudo:                              0
% 43.41/6.01  fd_cond:                                0
% 43.41/6.01  fd_pseudo_cond:                         1
% 43.41/6.01  ac_symbols:                             0
% 43.41/6.01  
% 43.41/6.01  ------ Propositional Solver
% 43.41/6.01  
% 43.41/6.01  prop_solver_calls:                      44
% 43.41/6.01  prop_fast_solver_calls:                 1110
% 43.41/6.01  smt_solver_calls:                       0
% 43.41/6.01  smt_fast_solver_calls:                  0
% 43.41/6.01  prop_num_of_clauses:                    43732
% 43.41/6.01  prop_preprocess_simplified:             39628
% 43.41/6.01  prop_fo_subsumed:                       7
% 43.41/6.01  prop_solver_time:                       0.
% 43.41/6.01  smt_solver_time:                        0.
% 43.41/6.01  smt_fast_solver_time:                   0.
% 43.41/6.01  prop_fast_solver_time:                  0.
% 43.41/6.01  prop_unsat_core_time:                   0.
% 43.41/6.01  
% 43.41/6.01  ------ QBF
% 43.41/6.01  
% 43.41/6.01  qbf_q_res:                              0
% 43.41/6.01  qbf_num_tautologies:                    0
% 43.41/6.01  qbf_prep_cycles:                        0
% 43.41/6.01  
% 43.41/6.01  ------ BMC1
% 43.41/6.01  
% 43.41/6.01  bmc1_current_bound:                     -1
% 43.41/6.01  bmc1_last_solved_bound:                 -1
% 43.41/6.01  bmc1_unsat_core_size:                   -1
% 43.41/6.01  bmc1_unsat_core_parents_size:           -1
% 43.41/6.01  bmc1_merge_next_fun:                    0
% 43.41/6.01  bmc1_unsat_core_clauses_time:           0.
% 43.41/6.01  
% 43.41/6.01  ------ Instantiation
% 43.41/6.01  
% 43.41/6.01  inst_num_of_clauses:                    7858
% 43.41/6.01  inst_num_in_passive:                    4268
% 43.41/6.01  inst_num_in_active:                     2665
% 43.41/6.01  inst_num_in_unprocessed:                925
% 43.41/6.01  inst_num_of_loops:                      2810
% 43.41/6.01  inst_num_of_learning_restarts:          0
% 43.41/6.01  inst_num_moves_active_passive:          143
% 43.41/6.01  inst_lit_activity:                      0
% 43.41/6.01  inst_lit_activity_moves:                0
% 43.41/6.01  inst_num_tautologies:                   0
% 43.41/6.01  inst_num_prop_implied:                  0
% 43.41/6.01  inst_num_existing_simplified:           0
% 43.41/6.01  inst_num_eq_res_simplified:             0
% 43.41/6.01  inst_num_child_elim:                    0
% 43.41/6.01  inst_num_of_dismatching_blockings:      3561
% 43.41/6.01  inst_num_of_non_proper_insts:           8818
% 43.41/6.01  inst_num_of_duplicates:                 0
% 43.41/6.01  inst_inst_num_from_inst_to_res:         0
% 43.41/6.01  inst_dismatching_checking_time:         0.
% 43.41/6.01  
% 43.41/6.01  ------ Resolution
% 43.41/6.01  
% 43.41/6.01  res_num_of_clauses:                     0
% 43.41/6.01  res_num_in_passive:                     0
% 43.41/6.01  res_num_in_active:                      0
% 43.41/6.01  res_num_of_loops:                       101
% 43.41/6.01  res_forward_subset_subsumed:            999
% 43.41/6.01  res_backward_subset_subsumed:           0
% 43.41/6.01  res_forward_subsumed:                   0
% 43.41/6.01  res_backward_subsumed:                  0
% 43.41/6.01  res_forward_subsumption_resolution:     0
% 43.41/6.01  res_backward_subsumption_resolution:    0
% 43.41/6.01  res_clause_to_clause_subsumption:       61377
% 43.41/6.01  res_orphan_elimination:                 0
% 43.41/6.01  res_tautology_del:                      1423
% 43.41/6.01  res_num_eq_res_simplified:              0
% 43.41/6.01  res_num_sel_changes:                    0
% 43.41/6.01  res_moves_from_active_to_pass:          0
% 43.41/6.01  
% 43.41/6.01  ------ Superposition
% 43.41/6.01  
% 43.41/6.01  sup_time_total:                         0.
% 43.41/6.01  sup_time_generating:                    0.
% 43.41/6.01  sup_time_sim_full:                      0.
% 43.41/6.01  sup_time_sim_immed:                     0.
% 43.41/6.01  
% 43.41/6.01  sup_num_of_clauses:                     10808
% 43.41/6.01  sup_num_in_active:                      243
% 43.41/6.01  sup_num_in_passive:                     10565
% 43.41/6.01  sup_num_of_loops:                       561
% 43.41/6.01  sup_fw_superposition:                   31843
% 43.41/6.01  sup_bw_superposition:                   32601
% 43.41/6.01  sup_immediate_simplified:               23564
% 43.41/6.01  sup_given_eliminated:                   4
% 43.41/6.01  comparisons_done:                       0
% 43.41/6.01  comparisons_avoided:                    0
% 43.41/6.01  
% 43.41/6.01  ------ Simplifications
% 43.41/6.01  
% 43.41/6.01  
% 43.41/6.01  sim_fw_subset_subsumed:                 183
% 43.41/6.01  sim_bw_subset_subsumed:                 144
% 43.41/6.01  sim_fw_subsumed:                        7189
% 43.41/6.01  sim_bw_subsumed:                        16
% 43.41/6.01  sim_fw_subsumption_res:                 0
% 43.41/6.01  sim_bw_subsumption_res:                 0
% 43.41/6.01  sim_tautology_del:                      95
% 43.41/6.01  sim_eq_tautology_del:                   5038
% 43.41/6.01  sim_eq_res_simp:                        0
% 43.41/6.01  sim_fw_demodulated:                     17102
% 43.41/6.01  sim_bw_demodulated:                     469
% 43.41/6.01  sim_light_normalised:                   10488
% 43.41/6.01  sim_joinable_taut:                      0
% 43.41/6.01  sim_joinable_simp:                      0
% 43.41/6.01  sim_ac_normalised:                      0
% 43.41/6.01  sim_smt_subsumption:                    0
% 43.41/6.01  
%------------------------------------------------------------------------------
