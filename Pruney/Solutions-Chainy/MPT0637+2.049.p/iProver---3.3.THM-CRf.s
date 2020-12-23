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
% DateTime   : Thu Dec  3 11:50:03 EST 2020

% Result     : Theorem 19.58s
% Output     : CNFRefutation 19.58s
% Verified   : 
% Statistics : Number of formulae       :  166 (5417 expanded)
%              Number of clauses        :  107 (2394 expanded)
%              Number of leaves         :   17 ( 995 expanded)
%              Depth                    :   33
%              Number of atoms          :  282 (9173 expanded)
%              Number of equality atoms :  185 (4318 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :   10 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f56,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f21,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f1,axiom,(
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
    inference(nnf_transformation,[],[f1])).

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
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f63,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f38])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k5_relat_1(k6_relat_1(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f58,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f41,f42])).

fof(f59,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f43,f58])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X0)) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f54,f59])).

fof(f9,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f60,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f40,f59])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k5_relat_1(k7_relat_1(X1,X0),X2) = k7_relat_1(k5_relat_1(X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k5_relat_1(k7_relat_1(X1,X0),X2) = k7_relat_1(k5_relat_1(X1,X2),X0)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k7_relat_1(X1,X0),X2) = k7_relat_1(k5_relat_1(X1,X2),X0)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f39,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f48,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f53,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f17,conjecture,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f17])).

fof(f32,plain,(
    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f18])).

fof(f35,plain,
    ( ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))
   => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f32,f35])).

fof(f57,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f36])).

fof(f62,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) ),
    inference(definition_unfolding,[],[f57,f59])).

cnf(c_16,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_537,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_15,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_538,plain,
    ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1209,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(superposition,[status(thm)],[c_537,c_538])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | v1_relat_1(k5_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_547,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k5_relat_1(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2137,plain,
    ( v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1209,c_547])).

cnf(c_18,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_4124,plain,
    ( v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2137,c_18])).

cnf(c_4130,plain,
    ( v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4124,c_537])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_549,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_11,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k6_relat_1(X1),X0) = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_542,plain,
    ( k5_relat_1(k6_relat_1(X0),X1) = X1
    | r1_tarski(k1_relat_1(X1),X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2172,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_549,c_542])).

cnf(c_4140,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),k7_relat_1(k6_relat_1(X0),X1)) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(superposition,[status(thm)],[c_4130,c_2172])).

cnf(c_14,plain,
    ( ~ v1_relat_1(X0)
    | k1_setfam_1(k2_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_539,plain,
    ( k1_setfam_1(k2_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_980,plain,
    ( k1_setfam_1(k2_enumset1(k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(superposition,[status(thm)],[c_537,c_539])).

cnf(c_8,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_981,plain,
    ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(light_normalisation,[status(thm)],[c_980,c_8])).

cnf(c_3,plain,
    ( r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_548,plain,
    ( r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_984,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_981,c_548])).

cnf(c_2173,plain,
    ( k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X0),X1)) = k7_relat_1(k6_relat_1(X0),X1)
    | v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_984,c_542])).

cnf(c_4956,plain,
    ( k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X0),X1)) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2173,c_4130])).

cnf(c_4136,plain,
    ( k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X1),X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X0) ),
    inference(superposition,[status(thm)],[c_4130,c_538])).

cnf(c_4968,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(superposition,[status(thm)],[c_4956,c_4136])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k7_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(k7_relat_1(X0,X2),X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_546,plain,
    ( k7_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(k7_relat_1(X0,X2),X1)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2369,plain,
    ( k7_relat_1(k5_relat_1(k6_relat_1(X0),X1),X2) = k5_relat_1(k7_relat_1(k6_relat_1(X0),X2),X1)
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_537,c_546])).

cnf(c_3474,plain,
    ( k7_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),X2) = k5_relat_1(k7_relat_1(k6_relat_1(X0),X2),k6_relat_1(X1)) ),
    inference(superposition,[status(thm)],[c_537,c_2369])).

cnf(c_3476,plain,
    ( k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X0),X1) ),
    inference(light_normalisation,[status(thm)],[c_3474,c_1209])).

cnf(c_10,plain,
    ( r1_tarski(k5_relat_1(X0,k6_relat_1(X1)),X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_543,plain,
    ( r1_tarski(k5_relat_1(X0,k6_relat_1(X1)),X0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3731,plain,
    ( r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2),k7_relat_1(k6_relat_1(X1),X2)) = iProver_top
    | v1_relat_1(k7_relat_1(k6_relat_1(X1),X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3476,c_543])).

cnf(c_7679,plain,
    ( r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2),k7_relat_1(k6_relat_1(X1),X2)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3731,c_4130])).

cnf(c_7684,plain,
    ( r1_tarski(k7_relat_1(k6_relat_1(X0),X1),k7_relat_1(k6_relat_1(X1),X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4968,c_7679])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_550,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_7966,plain,
    ( k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X1),X0)
    | r1_tarski(k7_relat_1(k6_relat_1(X0),X1),k7_relat_1(k6_relat_1(X1),X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7684,c_550])).

cnf(c_7969,plain,
    ( k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_7966,c_7684])).

cnf(c_8165,plain,
    ( k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X1),X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X1),X0) ),
    inference(superposition,[status(thm)],[c_7969,c_4136])).

cnf(c_45907,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),k1_relat_1(k7_relat_1(k6_relat_1(X1),X0))) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(superposition,[status(thm)],[c_4140,c_8165])).

cnf(c_8155,plain,
    ( k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X1),X0) ),
    inference(superposition,[status(thm)],[c_7969,c_3476])).

cnf(c_13695,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X2),X1) ),
    inference(superposition,[status(thm)],[c_8155,c_3476])).

cnf(c_7,plain,
    ( k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_12,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_relat_1(X1)) = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_541,plain,
    ( k5_relat_1(X0,k6_relat_1(X1)) = X0
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2091,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k6_relat_1(X0)
    | r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_541])).

cnf(c_2095,plain,
    ( k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X1)
    | r1_tarski(X1,X0) != iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2091,c_1209])).

cnf(c_3898,plain,
    ( k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X1)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2095,c_537])).

cnf(c_3902,plain,
    ( k7_relat_1(k6_relat_1(X0),k5_relat_1(X0,k6_relat_1(X1))) = k6_relat_1(k5_relat_1(X0,k6_relat_1(X1)))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_543,c_3898])).

cnf(c_4137,plain,
    ( k7_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X0),X1)),k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X2))) = k6_relat_1(k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X2))) ),
    inference(superposition,[status(thm)],[c_4130,c_3902])).

cnf(c_4163,plain,
    ( k7_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X0),X1)),k7_relat_1(k7_relat_1(k6_relat_1(X2),X0),X1)) = k6_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X2),X0),X1)) ),
    inference(light_normalisation,[status(thm)],[c_4137,c_3476])).

cnf(c_53686,plain,
    ( k7_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X0),X1)),k7_relat_1(k7_relat_1(k6_relat_1(X2),X1),X0)) = k6_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X2),X0),X1)) ),
    inference(superposition,[status(thm)],[c_13695,c_4163])).

cnf(c_3903,plain,
    ( k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
    inference(superposition,[status(thm)],[c_984,c_3898])).

cnf(c_9,plain,
    ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_544,plain,
    ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1642,plain,
    ( r1_tarski(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X0)) = iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1209,c_544])).

cnf(c_1931,plain,
    ( r1_tarski(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1642,c_18])).

cnf(c_2174,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k6_relat_1(X1)
    | r1_tarski(X1,X0) != iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8,c_542])).

cnf(c_2178,plain,
    ( k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X0)
    | r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2174,c_1209])).

cnf(c_5130,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2178,c_18])).

cnf(c_5131,plain,
    ( k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X0)
    | r1_tarski(X0,X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_5130])).

cnf(c_5141,plain,
    ( k7_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X0),X1)),k6_relat_1(X0)) = k6_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(superposition,[status(thm)],[c_1931,c_5131])).

cnf(c_8139,plain,
    ( k7_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X0),X1)),k6_relat_1(X1)) = k6_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
    inference(superposition,[status(thm)],[c_7969,c_5141])).

cnf(c_1471,plain,
    ( r1_tarski(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X1)) = iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1209,c_543])).

cnf(c_1925,plain,
    ( r1_tarski(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X1)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1471,c_537])).

cnf(c_5140,plain,
    ( k7_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X0),X1)),k6_relat_1(X1)) = k6_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(superposition,[status(thm)],[c_1925,c_5131])).

cnf(c_10006,plain,
    ( k6_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k6_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
    inference(superposition,[status(thm)],[c_8139,c_5140])).

cnf(c_10302,plain,
    ( k1_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(superposition,[status(thm)],[c_10006,c_8])).

cnf(c_10703,plain,
    ( k1_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X2))) = k7_relat_1(k6_relat_1(X2),k7_relat_1(k6_relat_1(X1),X0)) ),
    inference(superposition,[status(thm)],[c_10006,c_10302])).

cnf(c_11210,plain,
    ( k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X2))),k7_relat_1(k6_relat_1(X1),X0)) = k1_relat_1(k6_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X2))))) ),
    inference(superposition,[status(thm)],[c_3903,c_10703])).

cnf(c_11263,plain,
    ( k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X2))),k7_relat_1(k6_relat_1(X1),X0)) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X2))) ),
    inference(demodulation,[status(thm)],[c_11210,c_8])).

cnf(c_5139,plain,
    ( k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X0) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
    inference(superposition,[status(thm)],[c_984,c_5131])).

cnf(c_18081,plain,
    ( k7_relat_1(k6_relat_1(k1_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X2))))),k1_relat_1(k7_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X2))) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X2))),k7_relat_1(k6_relat_1(X1),X0)))) ),
    inference(superposition,[status(thm)],[c_11263,c_5139])).

cnf(c_18084,plain,
    ( k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X2))),k7_relat_1(k6_relat_1(X1),X0)) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X1),X0)),X2))) ),
    inference(superposition,[status(thm)],[c_10006,c_5139])).

cnf(c_18295,plain,
    ( k7_relat_1(k6_relat_1(k1_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X2))))),k1_relat_1(k7_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X2))) = k6_relat_1(k1_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X1),X0)),X2))))) ),
    inference(light_normalisation,[status(thm)],[c_18081,c_18084])).

cnf(c_13,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_540,plain,
    ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_793,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(k2_relat_1(k6_relat_1(X0)))) = k6_relat_1(X0) ),
    inference(superposition,[status(thm)],[c_537,c_540])).

cnf(c_794,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X0)) = k6_relat_1(X0) ),
    inference(light_normalisation,[status(thm)],[c_793,c_7])).

cnf(c_1472,plain,
    ( k7_relat_1(k6_relat_1(X0),X0) = k6_relat_1(X0) ),
    inference(superposition,[status(thm)],[c_1209,c_794])).

cnf(c_18297,plain,
    ( k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X2))) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X1),X0)),X2))) ),
    inference(demodulation,[status(thm)],[c_18295,c_8,c_1472])).

cnf(c_20577,plain,
    ( k1_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X2)))) = k1_relat_1(k7_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X1),X0)),X2)) ),
    inference(superposition,[status(thm)],[c_18297,c_8])).

cnf(c_53979,plain,
    ( k1_relat_1(k7_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X0),X1)),k7_relat_1(k7_relat_1(k6_relat_1(X2),X1),X0))) = k1_relat_1(k6_relat_1(k1_relat_1(k6_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X2),X1),X0))))) ),
    inference(superposition,[status(thm)],[c_4163,c_20577])).

cnf(c_54017,plain,
    ( k1_relat_1(k7_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X0),X1)),k7_relat_1(k7_relat_1(k6_relat_1(X2),X1),X0))) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X1),X0) ),
    inference(demodulation,[status(thm)],[c_53979,c_8])).

cnf(c_54555,plain,
    ( k1_relat_1(k6_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2))) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X2),X1) ),
    inference(demodulation,[status(thm)],[c_53686,c_54017])).

cnf(c_89014,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(k6_relat_1(X1),X0))),X1) = k1_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X1),X0))) ),
    inference(superposition,[status(thm)],[c_45907,c_54555])).

cnf(c_8161,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_7969,c_984])).

cnf(c_8277,plain,
    ( k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(k6_relat_1(X1),X0))) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X1),X0))) ),
    inference(superposition,[status(thm)],[c_8161,c_3898])).

cnf(c_89158,plain,
    ( k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X0) = k1_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
    inference(light_normalisation,[status(thm)],[c_89014,c_8277])).

cnf(c_8147,plain,
    ( k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(k6_relat_1(X1),X0))) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
    inference(superposition,[status(thm)],[c_7969,c_3903])).

cnf(c_21369,plain,
    ( k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X1),X0))) ),
    inference(superposition,[status(thm)],[c_8277,c_8147])).

cnf(c_22006,plain,
    ( k1_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)))) = k1_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
    inference(superposition,[status(thm)],[c_21369,c_8])).

cnf(c_22593,plain,
    ( k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
    inference(superposition,[status(thm)],[c_22006,c_8])).

cnf(c_8278,plain,
    ( k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X1) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
    inference(superposition,[status(thm)],[c_8161,c_5131])).

cnf(c_23115,plain,
    ( k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X0) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X1),X0))) ),
    inference(superposition,[status(thm)],[c_22593,c_8278])).

cnf(c_89159,plain,
    ( k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(demodulation,[status(thm)],[c_89158,c_10302,c_23115])).

cnf(c_17,negated_conjecture,
    ( k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_986,plain,
    ( k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(sK0),sK1))) != k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) ),
    inference(demodulation,[status(thm)],[c_981,c_17])).

cnf(c_1469,plain,
    ( k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(sK0),sK1))) != k7_relat_1(k6_relat_1(sK0),sK1) ),
    inference(demodulation,[status(thm)],[c_1209,c_986])).

cnf(c_8087,plain,
    ( k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(sK1),sK0))) != k7_relat_1(k6_relat_1(sK1),sK0) ),
    inference(demodulation,[status(thm)],[c_7969,c_1469])).

cnf(c_93843,plain,
    ( k7_relat_1(k6_relat_1(sK1),sK0) != k7_relat_1(k6_relat_1(sK1),sK0) ),
    inference(demodulation,[status(thm)],[c_89159,c_8087])).

cnf(c_93869,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_93843])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:20:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 19.58/3.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.58/3.01  
% 19.58/3.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 19.58/3.01  
% 19.58/3.01  ------  iProver source info
% 19.58/3.01  
% 19.58/3.01  git: date: 2020-06-30 10:37:57 +0100
% 19.58/3.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 19.58/3.01  git: non_committed_changes: false
% 19.58/3.01  git: last_make_outside_of_git: false
% 19.58/3.01  
% 19.58/3.01  ------ 
% 19.58/3.01  
% 19.58/3.01  ------ Input Options
% 19.58/3.01  
% 19.58/3.01  --out_options                           all
% 19.58/3.01  --tptp_safe_out                         true
% 19.58/3.01  --problem_path                          ""
% 19.58/3.01  --include_path                          ""
% 19.58/3.01  --clausifier                            res/vclausify_rel
% 19.58/3.01  --clausifier_options                    --mode clausify
% 19.58/3.01  --stdin                                 false
% 19.58/3.01  --stats_out                             all
% 19.58/3.01  
% 19.58/3.01  ------ General Options
% 19.58/3.01  
% 19.58/3.01  --fof                                   false
% 19.58/3.01  --time_out_real                         305.
% 19.58/3.01  --time_out_virtual                      -1.
% 19.58/3.01  --symbol_type_check                     false
% 19.58/3.01  --clausify_out                          false
% 19.58/3.01  --sig_cnt_out                           false
% 19.58/3.01  --trig_cnt_out                          false
% 19.58/3.01  --trig_cnt_out_tolerance                1.
% 19.58/3.01  --trig_cnt_out_sk_spl                   false
% 19.58/3.01  --abstr_cl_out                          false
% 19.58/3.01  
% 19.58/3.01  ------ Global Options
% 19.58/3.01  
% 19.58/3.01  --schedule                              default
% 19.58/3.01  --add_important_lit                     false
% 19.58/3.01  --prop_solver_per_cl                    1000
% 19.58/3.01  --min_unsat_core                        false
% 19.58/3.01  --soft_assumptions                      false
% 19.58/3.01  --soft_lemma_size                       3
% 19.58/3.01  --prop_impl_unit_size                   0
% 19.58/3.01  --prop_impl_unit                        []
% 19.58/3.01  --share_sel_clauses                     true
% 19.58/3.01  --reset_solvers                         false
% 19.58/3.01  --bc_imp_inh                            [conj_cone]
% 19.58/3.01  --conj_cone_tolerance                   3.
% 19.58/3.01  --extra_neg_conj                        none
% 19.58/3.01  --large_theory_mode                     true
% 19.58/3.01  --prolific_symb_bound                   200
% 19.58/3.01  --lt_threshold                          2000
% 19.58/3.01  --clause_weak_htbl                      true
% 19.58/3.01  --gc_record_bc_elim                     false
% 19.58/3.01  
% 19.58/3.01  ------ Preprocessing Options
% 19.58/3.01  
% 19.58/3.01  --preprocessing_flag                    true
% 19.58/3.01  --time_out_prep_mult                    0.1
% 19.58/3.01  --splitting_mode                        input
% 19.58/3.01  --splitting_grd                         true
% 19.58/3.01  --splitting_cvd                         false
% 19.58/3.01  --splitting_cvd_svl                     false
% 19.58/3.01  --splitting_nvd                         32
% 19.58/3.01  --sub_typing                            true
% 19.58/3.01  --prep_gs_sim                           true
% 19.58/3.01  --prep_unflatten                        true
% 19.58/3.01  --prep_res_sim                          true
% 19.58/3.01  --prep_upred                            true
% 19.58/3.01  --prep_sem_filter                       exhaustive
% 19.58/3.01  --prep_sem_filter_out                   false
% 19.58/3.01  --pred_elim                             true
% 19.58/3.01  --res_sim_input                         true
% 19.58/3.01  --eq_ax_congr_red                       true
% 19.58/3.01  --pure_diseq_elim                       true
% 19.58/3.01  --brand_transform                       false
% 19.58/3.01  --non_eq_to_eq                          false
% 19.58/3.01  --prep_def_merge                        true
% 19.58/3.01  --prep_def_merge_prop_impl              false
% 19.58/3.01  --prep_def_merge_mbd                    true
% 19.58/3.01  --prep_def_merge_tr_red                 false
% 19.58/3.01  --prep_def_merge_tr_cl                  false
% 19.58/3.01  --smt_preprocessing                     true
% 19.58/3.01  --smt_ac_axioms                         fast
% 19.58/3.01  --preprocessed_out                      false
% 19.58/3.01  --preprocessed_stats                    false
% 19.58/3.01  
% 19.58/3.01  ------ Abstraction refinement Options
% 19.58/3.01  
% 19.58/3.01  --abstr_ref                             []
% 19.58/3.01  --abstr_ref_prep                        false
% 19.58/3.01  --abstr_ref_until_sat                   false
% 19.58/3.01  --abstr_ref_sig_restrict                funpre
% 19.58/3.01  --abstr_ref_af_restrict_to_split_sk     false
% 19.58/3.01  --abstr_ref_under                       []
% 19.58/3.01  
% 19.58/3.01  ------ SAT Options
% 19.58/3.01  
% 19.58/3.01  --sat_mode                              false
% 19.58/3.01  --sat_fm_restart_options                ""
% 19.58/3.01  --sat_gr_def                            false
% 19.58/3.01  --sat_epr_types                         true
% 19.58/3.01  --sat_non_cyclic_types                  false
% 19.58/3.01  --sat_finite_models                     false
% 19.58/3.01  --sat_fm_lemmas                         false
% 19.58/3.01  --sat_fm_prep                           false
% 19.58/3.01  --sat_fm_uc_incr                        true
% 19.58/3.01  --sat_out_model                         small
% 19.58/3.01  --sat_out_clauses                       false
% 19.58/3.01  
% 19.58/3.01  ------ QBF Options
% 19.58/3.01  
% 19.58/3.01  --qbf_mode                              false
% 19.58/3.01  --qbf_elim_univ                         false
% 19.58/3.01  --qbf_dom_inst                          none
% 19.58/3.01  --qbf_dom_pre_inst                      false
% 19.58/3.01  --qbf_sk_in                             false
% 19.58/3.01  --qbf_pred_elim                         true
% 19.58/3.01  --qbf_split                             512
% 19.58/3.01  
% 19.58/3.01  ------ BMC1 Options
% 19.58/3.01  
% 19.58/3.01  --bmc1_incremental                      false
% 19.58/3.01  --bmc1_axioms                           reachable_all
% 19.58/3.01  --bmc1_min_bound                        0
% 19.58/3.01  --bmc1_max_bound                        -1
% 19.58/3.01  --bmc1_max_bound_default                -1
% 19.58/3.01  --bmc1_symbol_reachability              true
% 19.58/3.01  --bmc1_property_lemmas                  false
% 19.58/3.01  --bmc1_k_induction                      false
% 19.58/3.01  --bmc1_non_equiv_states                 false
% 19.58/3.01  --bmc1_deadlock                         false
% 19.58/3.01  --bmc1_ucm                              false
% 19.58/3.01  --bmc1_add_unsat_core                   none
% 19.58/3.01  --bmc1_unsat_core_children              false
% 19.58/3.01  --bmc1_unsat_core_extrapolate_axioms    false
% 19.58/3.01  --bmc1_out_stat                         full
% 19.58/3.01  --bmc1_ground_init                      false
% 19.58/3.01  --bmc1_pre_inst_next_state              false
% 19.58/3.01  --bmc1_pre_inst_state                   false
% 19.58/3.01  --bmc1_pre_inst_reach_state             false
% 19.58/3.01  --bmc1_out_unsat_core                   false
% 19.58/3.01  --bmc1_aig_witness_out                  false
% 19.58/3.01  --bmc1_verbose                          false
% 19.58/3.01  --bmc1_dump_clauses_tptp                false
% 19.58/3.01  --bmc1_dump_unsat_core_tptp             false
% 19.58/3.01  --bmc1_dump_file                        -
% 19.58/3.01  --bmc1_ucm_expand_uc_limit              128
% 19.58/3.01  --bmc1_ucm_n_expand_iterations          6
% 19.58/3.01  --bmc1_ucm_extend_mode                  1
% 19.58/3.01  --bmc1_ucm_init_mode                    2
% 19.58/3.01  --bmc1_ucm_cone_mode                    none
% 19.58/3.01  --bmc1_ucm_reduced_relation_type        0
% 19.58/3.01  --bmc1_ucm_relax_model                  4
% 19.58/3.01  --bmc1_ucm_full_tr_after_sat            true
% 19.58/3.01  --bmc1_ucm_expand_neg_assumptions       false
% 19.58/3.01  --bmc1_ucm_layered_model                none
% 19.58/3.01  --bmc1_ucm_max_lemma_size               10
% 19.58/3.01  
% 19.58/3.01  ------ AIG Options
% 19.58/3.01  
% 19.58/3.01  --aig_mode                              false
% 19.58/3.01  
% 19.58/3.01  ------ Instantiation Options
% 19.58/3.01  
% 19.58/3.01  --instantiation_flag                    true
% 19.58/3.01  --inst_sos_flag                         false
% 19.58/3.01  --inst_sos_phase                        true
% 19.58/3.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.58/3.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.58/3.01  --inst_lit_sel_side                     num_symb
% 19.58/3.01  --inst_solver_per_active                1400
% 19.58/3.01  --inst_solver_calls_frac                1.
% 19.58/3.01  --inst_passive_queue_type               priority_queues
% 19.58/3.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.58/3.01  --inst_passive_queues_freq              [25;2]
% 19.58/3.01  --inst_dismatching                      true
% 19.58/3.01  --inst_eager_unprocessed_to_passive     true
% 19.58/3.01  --inst_prop_sim_given                   true
% 19.58/3.01  --inst_prop_sim_new                     false
% 19.58/3.01  --inst_subs_new                         false
% 19.58/3.01  --inst_eq_res_simp                      false
% 19.58/3.01  --inst_subs_given                       false
% 19.58/3.01  --inst_orphan_elimination               true
% 19.58/3.01  --inst_learning_loop_flag               true
% 19.58/3.01  --inst_learning_start                   3000
% 19.58/3.01  --inst_learning_factor                  2
% 19.58/3.01  --inst_start_prop_sim_after_learn       3
% 19.58/3.01  --inst_sel_renew                        solver
% 19.58/3.01  --inst_lit_activity_flag                true
% 19.58/3.01  --inst_restr_to_given                   false
% 19.58/3.01  --inst_activity_threshold               500
% 19.58/3.01  --inst_out_proof                        true
% 19.58/3.01  
% 19.58/3.01  ------ Resolution Options
% 19.58/3.01  
% 19.58/3.01  --resolution_flag                       true
% 19.58/3.01  --res_lit_sel                           adaptive
% 19.58/3.01  --res_lit_sel_side                      none
% 19.58/3.01  --res_ordering                          kbo
% 19.58/3.01  --res_to_prop_solver                    active
% 19.58/3.01  --res_prop_simpl_new                    false
% 19.58/3.01  --res_prop_simpl_given                  true
% 19.58/3.01  --res_passive_queue_type                priority_queues
% 19.58/3.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.58/3.01  --res_passive_queues_freq               [15;5]
% 19.58/3.01  --res_forward_subs                      full
% 19.58/3.01  --res_backward_subs                     full
% 19.58/3.01  --res_forward_subs_resolution           true
% 19.58/3.01  --res_backward_subs_resolution          true
% 19.58/3.01  --res_orphan_elimination                true
% 19.58/3.01  --res_time_limit                        2.
% 19.58/3.01  --res_out_proof                         true
% 19.58/3.01  
% 19.58/3.01  ------ Superposition Options
% 19.58/3.01  
% 19.58/3.01  --superposition_flag                    true
% 19.58/3.01  --sup_passive_queue_type                priority_queues
% 19.58/3.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.58/3.01  --sup_passive_queues_freq               [8;1;4]
% 19.58/3.01  --demod_completeness_check              fast
% 19.58/3.01  --demod_use_ground                      true
% 19.58/3.01  --sup_to_prop_solver                    passive
% 19.58/3.01  --sup_prop_simpl_new                    true
% 19.58/3.01  --sup_prop_simpl_given                  true
% 19.58/3.01  --sup_fun_splitting                     false
% 19.58/3.01  --sup_smt_interval                      50000
% 19.58/3.01  
% 19.58/3.01  ------ Superposition Simplification Setup
% 19.58/3.01  
% 19.58/3.01  --sup_indices_passive                   []
% 19.58/3.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.58/3.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.58/3.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.58/3.01  --sup_full_triv                         [TrivRules;PropSubs]
% 19.58/3.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.58/3.01  --sup_full_bw                           [BwDemod]
% 19.58/3.01  --sup_immed_triv                        [TrivRules]
% 19.58/3.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.58/3.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.58/3.01  --sup_immed_bw_main                     []
% 19.58/3.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 19.58/3.01  --sup_input_triv                        [Unflattening;TrivRules]
% 19.58/3.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.58/3.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 19.58/3.01  
% 19.58/3.01  ------ Combination Options
% 19.58/3.01  
% 19.58/3.01  --comb_res_mult                         3
% 19.58/3.01  --comb_sup_mult                         2
% 19.58/3.01  --comb_inst_mult                        10
% 19.58/3.01  
% 19.58/3.01  ------ Debug Options
% 19.58/3.01  
% 19.58/3.01  --dbg_backtrace                         false
% 19.58/3.01  --dbg_dump_prop_clauses                 false
% 19.58/3.01  --dbg_dump_prop_clauses_file            -
% 19.58/3.01  --dbg_out_stat                          false
% 19.58/3.01  ------ Parsing...
% 19.58/3.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 19.58/3.01  
% 19.58/3.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 19.58/3.01  
% 19.58/3.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 19.58/3.01  
% 19.58/3.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.58/3.01  ------ Proving...
% 19.58/3.01  ------ Problem Properties 
% 19.58/3.01  
% 19.58/3.01  
% 19.58/3.01  clauses                                 17
% 19.58/3.01  conjectures                             1
% 19.58/3.01  EPR                                     2
% 19.58/3.01  Horn                                    17
% 19.58/3.01  unary                                   6
% 19.58/3.01  binary                                  5
% 19.58/3.01  lits                                    35
% 19.58/3.01  lits eq                                 11
% 19.58/3.01  fd_pure                                 0
% 19.58/3.01  fd_pseudo                               0
% 19.58/3.01  fd_cond                                 0
% 19.58/3.01  fd_pseudo_cond                          1
% 19.58/3.01  AC symbols                              0
% 19.58/3.01  
% 19.58/3.01  ------ Schedule dynamic 5 is on 
% 19.58/3.01  
% 19.58/3.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 19.58/3.01  
% 19.58/3.01  
% 19.58/3.01  ------ 
% 19.58/3.01  Current options:
% 19.58/3.01  ------ 
% 19.58/3.01  
% 19.58/3.01  ------ Input Options
% 19.58/3.01  
% 19.58/3.01  --out_options                           all
% 19.58/3.01  --tptp_safe_out                         true
% 19.58/3.01  --problem_path                          ""
% 19.58/3.01  --include_path                          ""
% 19.58/3.01  --clausifier                            res/vclausify_rel
% 19.58/3.01  --clausifier_options                    --mode clausify
% 19.58/3.01  --stdin                                 false
% 19.58/3.01  --stats_out                             all
% 19.58/3.01  
% 19.58/3.01  ------ General Options
% 19.58/3.01  
% 19.58/3.01  --fof                                   false
% 19.58/3.01  --time_out_real                         305.
% 19.58/3.01  --time_out_virtual                      -1.
% 19.58/3.01  --symbol_type_check                     false
% 19.58/3.01  --clausify_out                          false
% 19.58/3.01  --sig_cnt_out                           false
% 19.58/3.01  --trig_cnt_out                          false
% 19.58/3.01  --trig_cnt_out_tolerance                1.
% 19.58/3.01  --trig_cnt_out_sk_spl                   false
% 19.58/3.01  --abstr_cl_out                          false
% 19.58/3.01  
% 19.58/3.01  ------ Global Options
% 19.58/3.01  
% 19.58/3.01  --schedule                              default
% 19.58/3.01  --add_important_lit                     false
% 19.58/3.01  --prop_solver_per_cl                    1000
% 19.58/3.01  --min_unsat_core                        false
% 19.58/3.01  --soft_assumptions                      false
% 19.58/3.01  --soft_lemma_size                       3
% 19.58/3.01  --prop_impl_unit_size                   0
% 19.58/3.01  --prop_impl_unit                        []
% 19.58/3.01  --share_sel_clauses                     true
% 19.58/3.01  --reset_solvers                         false
% 19.58/3.01  --bc_imp_inh                            [conj_cone]
% 19.58/3.01  --conj_cone_tolerance                   3.
% 19.58/3.01  --extra_neg_conj                        none
% 19.58/3.01  --large_theory_mode                     true
% 19.58/3.01  --prolific_symb_bound                   200
% 19.58/3.01  --lt_threshold                          2000
% 19.58/3.01  --clause_weak_htbl                      true
% 19.58/3.01  --gc_record_bc_elim                     false
% 19.58/3.01  
% 19.58/3.01  ------ Preprocessing Options
% 19.58/3.01  
% 19.58/3.01  --preprocessing_flag                    true
% 19.58/3.01  --time_out_prep_mult                    0.1
% 19.58/3.01  --splitting_mode                        input
% 19.58/3.01  --splitting_grd                         true
% 19.58/3.01  --splitting_cvd                         false
% 19.58/3.01  --splitting_cvd_svl                     false
% 19.58/3.01  --splitting_nvd                         32
% 19.58/3.01  --sub_typing                            true
% 19.58/3.01  --prep_gs_sim                           true
% 19.58/3.01  --prep_unflatten                        true
% 19.58/3.01  --prep_res_sim                          true
% 19.58/3.01  --prep_upred                            true
% 19.58/3.01  --prep_sem_filter                       exhaustive
% 19.58/3.01  --prep_sem_filter_out                   false
% 19.58/3.01  --pred_elim                             true
% 19.58/3.01  --res_sim_input                         true
% 19.58/3.01  --eq_ax_congr_red                       true
% 19.58/3.01  --pure_diseq_elim                       true
% 19.58/3.01  --brand_transform                       false
% 19.58/3.01  --non_eq_to_eq                          false
% 19.58/3.01  --prep_def_merge                        true
% 19.58/3.01  --prep_def_merge_prop_impl              false
% 19.58/3.01  --prep_def_merge_mbd                    true
% 19.58/3.01  --prep_def_merge_tr_red                 false
% 19.58/3.01  --prep_def_merge_tr_cl                  false
% 19.58/3.01  --smt_preprocessing                     true
% 19.58/3.01  --smt_ac_axioms                         fast
% 19.58/3.01  --preprocessed_out                      false
% 19.58/3.01  --preprocessed_stats                    false
% 19.58/3.01  
% 19.58/3.01  ------ Abstraction refinement Options
% 19.58/3.01  
% 19.58/3.01  --abstr_ref                             []
% 19.58/3.01  --abstr_ref_prep                        false
% 19.58/3.01  --abstr_ref_until_sat                   false
% 19.58/3.01  --abstr_ref_sig_restrict                funpre
% 19.58/3.01  --abstr_ref_af_restrict_to_split_sk     false
% 19.58/3.01  --abstr_ref_under                       []
% 19.58/3.01  
% 19.58/3.01  ------ SAT Options
% 19.58/3.01  
% 19.58/3.01  --sat_mode                              false
% 19.58/3.01  --sat_fm_restart_options                ""
% 19.58/3.01  --sat_gr_def                            false
% 19.58/3.01  --sat_epr_types                         true
% 19.58/3.01  --sat_non_cyclic_types                  false
% 19.58/3.01  --sat_finite_models                     false
% 19.58/3.01  --sat_fm_lemmas                         false
% 19.58/3.01  --sat_fm_prep                           false
% 19.58/3.01  --sat_fm_uc_incr                        true
% 19.58/3.01  --sat_out_model                         small
% 19.58/3.01  --sat_out_clauses                       false
% 19.58/3.01  
% 19.58/3.01  ------ QBF Options
% 19.58/3.01  
% 19.58/3.01  --qbf_mode                              false
% 19.58/3.01  --qbf_elim_univ                         false
% 19.58/3.01  --qbf_dom_inst                          none
% 19.58/3.01  --qbf_dom_pre_inst                      false
% 19.58/3.01  --qbf_sk_in                             false
% 19.58/3.01  --qbf_pred_elim                         true
% 19.58/3.01  --qbf_split                             512
% 19.58/3.01  
% 19.58/3.01  ------ BMC1 Options
% 19.58/3.01  
% 19.58/3.01  --bmc1_incremental                      false
% 19.58/3.01  --bmc1_axioms                           reachable_all
% 19.58/3.01  --bmc1_min_bound                        0
% 19.58/3.01  --bmc1_max_bound                        -1
% 19.58/3.01  --bmc1_max_bound_default                -1
% 19.58/3.01  --bmc1_symbol_reachability              true
% 19.58/3.01  --bmc1_property_lemmas                  false
% 19.58/3.01  --bmc1_k_induction                      false
% 19.58/3.01  --bmc1_non_equiv_states                 false
% 19.58/3.01  --bmc1_deadlock                         false
% 19.58/3.01  --bmc1_ucm                              false
% 19.58/3.01  --bmc1_add_unsat_core                   none
% 19.58/3.01  --bmc1_unsat_core_children              false
% 19.58/3.01  --bmc1_unsat_core_extrapolate_axioms    false
% 19.58/3.01  --bmc1_out_stat                         full
% 19.58/3.01  --bmc1_ground_init                      false
% 19.58/3.01  --bmc1_pre_inst_next_state              false
% 19.58/3.01  --bmc1_pre_inst_state                   false
% 19.58/3.01  --bmc1_pre_inst_reach_state             false
% 19.58/3.01  --bmc1_out_unsat_core                   false
% 19.58/3.01  --bmc1_aig_witness_out                  false
% 19.58/3.01  --bmc1_verbose                          false
% 19.58/3.01  --bmc1_dump_clauses_tptp                false
% 19.58/3.01  --bmc1_dump_unsat_core_tptp             false
% 19.58/3.01  --bmc1_dump_file                        -
% 19.58/3.01  --bmc1_ucm_expand_uc_limit              128
% 19.58/3.01  --bmc1_ucm_n_expand_iterations          6
% 19.58/3.01  --bmc1_ucm_extend_mode                  1
% 19.58/3.01  --bmc1_ucm_init_mode                    2
% 19.58/3.01  --bmc1_ucm_cone_mode                    none
% 19.58/3.01  --bmc1_ucm_reduced_relation_type        0
% 19.58/3.01  --bmc1_ucm_relax_model                  4
% 19.58/3.01  --bmc1_ucm_full_tr_after_sat            true
% 19.58/3.01  --bmc1_ucm_expand_neg_assumptions       false
% 19.58/3.01  --bmc1_ucm_layered_model                none
% 19.58/3.01  --bmc1_ucm_max_lemma_size               10
% 19.58/3.01  
% 19.58/3.01  ------ AIG Options
% 19.58/3.01  
% 19.58/3.01  --aig_mode                              false
% 19.58/3.01  
% 19.58/3.01  ------ Instantiation Options
% 19.58/3.01  
% 19.58/3.01  --instantiation_flag                    true
% 19.58/3.01  --inst_sos_flag                         false
% 19.58/3.01  --inst_sos_phase                        true
% 19.58/3.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.58/3.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.58/3.01  --inst_lit_sel_side                     none
% 19.58/3.01  --inst_solver_per_active                1400
% 19.58/3.01  --inst_solver_calls_frac                1.
% 19.58/3.01  --inst_passive_queue_type               priority_queues
% 19.58/3.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.58/3.01  --inst_passive_queues_freq              [25;2]
% 19.58/3.01  --inst_dismatching                      true
% 19.58/3.01  --inst_eager_unprocessed_to_passive     true
% 19.58/3.01  --inst_prop_sim_given                   true
% 19.58/3.01  --inst_prop_sim_new                     false
% 19.58/3.01  --inst_subs_new                         false
% 19.58/3.01  --inst_eq_res_simp                      false
% 19.58/3.01  --inst_subs_given                       false
% 19.58/3.01  --inst_orphan_elimination               true
% 19.58/3.01  --inst_learning_loop_flag               true
% 19.58/3.01  --inst_learning_start                   3000
% 19.58/3.01  --inst_learning_factor                  2
% 19.58/3.01  --inst_start_prop_sim_after_learn       3
% 19.58/3.01  --inst_sel_renew                        solver
% 19.58/3.01  --inst_lit_activity_flag                true
% 19.58/3.01  --inst_restr_to_given                   false
% 19.58/3.01  --inst_activity_threshold               500
% 19.58/3.01  --inst_out_proof                        true
% 19.58/3.01  
% 19.58/3.01  ------ Resolution Options
% 19.58/3.01  
% 19.58/3.01  --resolution_flag                       false
% 19.58/3.01  --res_lit_sel                           adaptive
% 19.58/3.01  --res_lit_sel_side                      none
% 19.58/3.01  --res_ordering                          kbo
% 19.58/3.01  --res_to_prop_solver                    active
% 19.58/3.01  --res_prop_simpl_new                    false
% 19.58/3.01  --res_prop_simpl_given                  true
% 19.58/3.01  --res_passive_queue_type                priority_queues
% 19.58/3.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.58/3.01  --res_passive_queues_freq               [15;5]
% 19.58/3.01  --res_forward_subs                      full
% 19.58/3.01  --res_backward_subs                     full
% 19.58/3.01  --res_forward_subs_resolution           true
% 19.58/3.01  --res_backward_subs_resolution          true
% 19.58/3.01  --res_orphan_elimination                true
% 19.58/3.01  --res_time_limit                        2.
% 19.58/3.01  --res_out_proof                         true
% 19.58/3.01  
% 19.58/3.01  ------ Superposition Options
% 19.58/3.01  
% 19.58/3.01  --superposition_flag                    true
% 19.58/3.01  --sup_passive_queue_type                priority_queues
% 19.58/3.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.58/3.01  --sup_passive_queues_freq               [8;1;4]
% 19.58/3.01  --demod_completeness_check              fast
% 19.58/3.01  --demod_use_ground                      true
% 19.58/3.01  --sup_to_prop_solver                    passive
% 19.58/3.01  --sup_prop_simpl_new                    true
% 19.58/3.01  --sup_prop_simpl_given                  true
% 19.58/3.01  --sup_fun_splitting                     false
% 19.58/3.01  --sup_smt_interval                      50000
% 19.58/3.01  
% 19.58/3.01  ------ Superposition Simplification Setup
% 19.58/3.01  
% 19.58/3.01  --sup_indices_passive                   []
% 19.58/3.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.58/3.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.58/3.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.58/3.01  --sup_full_triv                         [TrivRules;PropSubs]
% 19.58/3.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.58/3.01  --sup_full_bw                           [BwDemod]
% 19.58/3.01  --sup_immed_triv                        [TrivRules]
% 19.58/3.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.58/3.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.58/3.01  --sup_immed_bw_main                     []
% 19.58/3.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 19.58/3.01  --sup_input_triv                        [Unflattening;TrivRules]
% 19.58/3.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.58/3.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 19.58/3.01  
% 19.58/3.01  ------ Combination Options
% 19.58/3.01  
% 19.58/3.01  --comb_res_mult                         3
% 19.58/3.01  --comb_sup_mult                         2
% 19.58/3.01  --comb_inst_mult                        10
% 19.58/3.01  
% 19.58/3.01  ------ Debug Options
% 19.58/3.01  
% 19.58/3.01  --dbg_backtrace                         false
% 19.58/3.01  --dbg_dump_prop_clauses                 false
% 19.58/3.01  --dbg_dump_prop_clauses_file            -
% 19.58/3.01  --dbg_out_stat                          false
% 19.58/3.01  
% 19.58/3.01  
% 19.58/3.01  
% 19.58/3.01  
% 19.58/3.01  ------ Proving...
% 19.58/3.01  
% 19.58/3.01  
% 19.58/3.01  % SZS status Theorem for theBenchmark.p
% 19.58/3.01  
% 19.58/3.01   Resolution empty clause
% 19.58/3.01  
% 19.58/3.01  % SZS output start CNFRefutation for theBenchmark.p
% 19.58/3.01  
% 19.58/3.01  fof(f16,axiom,(
% 19.58/3.01    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 19.58/3.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.58/3.01  
% 19.58/3.01  fof(f19,plain,(
% 19.58/3.01    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 19.58/3.01    inference(pure_predicate_removal,[],[f16])).
% 19.58/3.01  
% 19.58/3.01  fof(f56,plain,(
% 19.58/3.01    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 19.58/3.01    inference(cnf_transformation,[],[f19])).
% 19.58/3.01  
% 19.58/3.01  fof(f15,axiom,(
% 19.58/3.01    ! [X0,X1] : (v1_relat_1(X1) => k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0))),
% 19.58/3.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.58/3.01  
% 19.58/3.01  fof(f31,plain,(
% 19.58/3.01    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 19.58/3.01    inference(ennf_transformation,[],[f15])).
% 19.58/3.01  
% 19.58/3.01  fof(f55,plain,(
% 19.58/3.01    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 19.58/3.01    inference(cnf_transformation,[],[f31])).
% 19.58/3.01  
% 19.58/3.01  fof(f6,axiom,(
% 19.58/3.01    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 19.58/3.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.58/3.01  
% 19.58/3.01  fof(f20,plain,(
% 19.58/3.01    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 19.58/3.01    inference(ennf_transformation,[],[f6])).
% 19.58/3.01  
% 19.58/3.01  fof(f21,plain,(
% 19.58/3.01    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 19.58/3.01    inference(flattening,[],[f20])).
% 19.58/3.01  
% 19.58/3.01  fof(f44,plain,(
% 19.58/3.01    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 19.58/3.01    inference(cnf_transformation,[],[f21])).
% 19.58/3.01  
% 19.58/3.01  fof(f1,axiom,(
% 19.58/3.01    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 19.58/3.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.58/3.01  
% 19.58/3.01  fof(f33,plain,(
% 19.58/3.01    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 19.58/3.01    inference(nnf_transformation,[],[f1])).
% 19.58/3.01  
% 19.58/3.01  fof(f34,plain,(
% 19.58/3.01    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 19.58/3.01    inference(flattening,[],[f33])).
% 19.58/3.01  
% 19.58/3.01  fof(f38,plain,(
% 19.58/3.01    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 19.58/3.01    inference(cnf_transformation,[],[f34])).
% 19.58/3.01  
% 19.58/3.01  fof(f63,plain,(
% 19.58/3.01    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 19.58/3.01    inference(equality_resolution,[],[f38])).
% 19.58/3.01  
% 19.58/3.01  fof(f11,axiom,(
% 19.58/3.01    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k5_relat_1(k6_relat_1(X0),X1) = X1))),
% 19.58/3.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.58/3.01  
% 19.58/3.01  fof(f25,plain,(
% 19.58/3.01    ! [X0,X1] : ((k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 19.58/3.01    inference(ennf_transformation,[],[f11])).
% 19.58/3.01  
% 19.58/3.01  fof(f26,plain,(
% 19.58/3.01    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 19.58/3.01    inference(flattening,[],[f25])).
% 19.58/3.01  
% 19.58/3.01  fof(f51,plain,(
% 19.58/3.01    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 19.58/3.01    inference(cnf_transformation,[],[f26])).
% 19.58/3.01  
% 19.58/3.01  fof(f14,axiom,(
% 19.58/3.01    ! [X0,X1] : (v1_relat_1(X1) => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)))),
% 19.58/3.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.58/3.01  
% 19.58/3.01  fof(f30,plain,(
% 19.58/3.01    ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 19.58/3.01    inference(ennf_transformation,[],[f14])).
% 19.58/3.01  
% 19.58/3.01  fof(f54,plain,(
% 19.58/3.01    ( ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 19.58/3.01    inference(cnf_transformation,[],[f30])).
% 19.58/3.01  
% 19.58/3.01  fof(f5,axiom,(
% 19.58/3.01    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 19.58/3.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.58/3.01  
% 19.58/3.01  fof(f43,plain,(
% 19.58/3.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 19.58/3.01    inference(cnf_transformation,[],[f5])).
% 19.58/3.01  
% 19.58/3.01  fof(f3,axiom,(
% 19.58/3.01    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 19.58/3.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.58/3.01  
% 19.58/3.01  fof(f41,plain,(
% 19.58/3.01    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 19.58/3.01    inference(cnf_transformation,[],[f3])).
% 19.58/3.01  
% 19.58/3.01  fof(f4,axiom,(
% 19.58/3.01    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 19.58/3.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.58/3.01  
% 19.58/3.01  fof(f42,plain,(
% 19.58/3.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 19.58/3.01    inference(cnf_transformation,[],[f4])).
% 19.58/3.01  
% 19.58/3.01  fof(f58,plain,(
% 19.58/3.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 19.58/3.01    inference(definition_unfolding,[],[f41,f42])).
% 19.58/3.01  
% 19.58/3.01  fof(f59,plain,(
% 19.58/3.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 19.58/3.01    inference(definition_unfolding,[],[f43,f58])).
% 19.58/3.01  
% 19.58/3.01  fof(f61,plain,(
% 19.58/3.01    ( ! [X0,X1] : (k1_setfam_1(k2_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X0)) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 19.58/3.01    inference(definition_unfolding,[],[f54,f59])).
% 19.58/3.01  
% 19.58/3.01  fof(f9,axiom,(
% 19.58/3.01    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 19.58/3.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.58/3.01  
% 19.58/3.01  fof(f47,plain,(
% 19.58/3.01    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 19.58/3.01    inference(cnf_transformation,[],[f9])).
% 19.58/3.01  
% 19.58/3.01  fof(f2,axiom,(
% 19.58/3.01    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 19.58/3.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.58/3.01  
% 19.58/3.01  fof(f40,plain,(
% 19.58/3.01    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 19.58/3.01    inference(cnf_transformation,[],[f2])).
% 19.58/3.01  
% 19.58/3.01  fof(f60,plain,(
% 19.58/3.01    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0)) )),
% 19.58/3.01    inference(definition_unfolding,[],[f40,f59])).
% 19.58/3.01  
% 19.58/3.01  fof(f7,axiom,(
% 19.58/3.01    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k7_relat_1(X1,X0),X2) = k7_relat_1(k5_relat_1(X1,X2),X0)))),
% 19.58/3.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.58/3.01  
% 19.58/3.01  fof(f22,plain,(
% 19.58/3.01    ! [X0,X1] : (! [X2] : (k5_relat_1(k7_relat_1(X1,X0),X2) = k7_relat_1(k5_relat_1(X1,X2),X0) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 19.58/3.01    inference(ennf_transformation,[],[f7])).
% 19.58/3.01  
% 19.58/3.01  fof(f45,plain,(
% 19.58/3.01    ( ! [X2,X0,X1] : (k5_relat_1(k7_relat_1(X1,X0),X2) = k7_relat_1(k5_relat_1(X1,X2),X0) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 19.58/3.01    inference(cnf_transformation,[],[f22])).
% 19.58/3.01  
% 19.58/3.01  fof(f10,axiom,(
% 19.58/3.01    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)))),
% 19.58/3.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.58/3.01  
% 19.58/3.01  fof(f24,plain,(
% 19.58/3.01    ! [X0,X1] : ((r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)) | ~v1_relat_1(X1))),
% 19.58/3.01    inference(ennf_transformation,[],[f10])).
% 19.58/3.01  
% 19.58/3.01  fof(f49,plain,(
% 19.58/3.01    ( ! [X0,X1] : (r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) | ~v1_relat_1(X1)) )),
% 19.58/3.01    inference(cnf_transformation,[],[f24])).
% 19.58/3.01  
% 19.58/3.01  fof(f39,plain,(
% 19.58/3.01    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 19.58/3.01    inference(cnf_transformation,[],[f34])).
% 19.58/3.01  
% 19.58/3.01  fof(f48,plain,(
% 19.58/3.01    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 19.58/3.01    inference(cnf_transformation,[],[f9])).
% 19.58/3.01  
% 19.58/3.01  fof(f12,axiom,(
% 19.58/3.01    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 19.58/3.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.58/3.01  
% 19.58/3.01  fof(f27,plain,(
% 19.58/3.01    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 19.58/3.01    inference(ennf_transformation,[],[f12])).
% 19.58/3.01  
% 19.58/3.01  fof(f28,plain,(
% 19.58/3.01    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 19.58/3.01    inference(flattening,[],[f27])).
% 19.58/3.01  
% 19.58/3.01  fof(f52,plain,(
% 19.58/3.01    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 19.58/3.01    inference(cnf_transformation,[],[f28])).
% 19.58/3.01  
% 19.58/3.01  fof(f50,plain,(
% 19.58/3.01    ( ! [X0,X1] : (r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) | ~v1_relat_1(X1)) )),
% 19.58/3.01    inference(cnf_transformation,[],[f24])).
% 19.58/3.01  
% 19.58/3.01  fof(f13,axiom,(
% 19.58/3.01    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 19.58/3.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.58/3.01  
% 19.58/3.01  fof(f29,plain,(
% 19.58/3.01    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 19.58/3.01    inference(ennf_transformation,[],[f13])).
% 19.58/3.01  
% 19.58/3.01  fof(f53,plain,(
% 19.58/3.01    ( ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 19.58/3.01    inference(cnf_transformation,[],[f29])).
% 19.58/3.01  
% 19.58/3.01  fof(f17,conjecture,(
% 19.58/3.01    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 19.58/3.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.58/3.01  
% 19.58/3.01  fof(f18,negated_conjecture,(
% 19.58/3.01    ~! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 19.58/3.01    inference(negated_conjecture,[],[f17])).
% 19.58/3.01  
% 19.58/3.01  fof(f32,plain,(
% 19.58/3.01    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))),
% 19.58/3.01    inference(ennf_transformation,[],[f18])).
% 19.58/3.01  
% 19.58/3.01  fof(f35,plain,(
% 19.58/3.01    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 19.58/3.01    introduced(choice_axiom,[])).
% 19.58/3.01  
% 19.58/3.01  fof(f36,plain,(
% 19.58/3.01    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 19.58/3.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f32,f35])).
% 19.58/3.01  
% 19.58/3.01  fof(f57,plain,(
% 19.58/3.01    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 19.58/3.01    inference(cnf_transformation,[],[f36])).
% 19.58/3.01  
% 19.58/3.01  fof(f62,plain,(
% 19.58/3.01    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)))),
% 19.58/3.01    inference(definition_unfolding,[],[f57,f59])).
% 19.58/3.01  
% 19.58/3.01  cnf(c_16,plain,
% 19.58/3.01      ( v1_relat_1(k6_relat_1(X0)) ),
% 19.58/3.01      inference(cnf_transformation,[],[f56]) ).
% 19.58/3.01  
% 19.58/3.01  cnf(c_537,plain,
% 19.58/3.01      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 19.58/3.01      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 19.58/3.01  
% 19.58/3.01  cnf(c_15,plain,
% 19.58/3.01      ( ~ v1_relat_1(X0) | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
% 19.58/3.01      inference(cnf_transformation,[],[f55]) ).
% 19.58/3.01  
% 19.58/3.01  cnf(c_538,plain,
% 19.58/3.01      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
% 19.58/3.01      | v1_relat_1(X1) != iProver_top ),
% 19.58/3.01      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 19.58/3.01  
% 19.58/3.01  cnf(c_1209,plain,
% 19.58/3.01      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
% 19.58/3.01      inference(superposition,[status(thm)],[c_537,c_538]) ).
% 19.58/3.01  
% 19.58/3.01  cnf(c_4,plain,
% 19.58/3.01      ( ~ v1_relat_1(X0) | ~ v1_relat_1(X1) | v1_relat_1(k5_relat_1(X1,X0)) ),
% 19.58/3.01      inference(cnf_transformation,[],[f44]) ).
% 19.58/3.01  
% 19.58/3.01  cnf(c_547,plain,
% 19.58/3.01      ( v1_relat_1(X0) != iProver_top
% 19.58/3.01      | v1_relat_1(X1) != iProver_top
% 19.58/3.01      | v1_relat_1(k5_relat_1(X1,X0)) = iProver_top ),
% 19.58/3.01      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 19.58/3.01  
% 19.58/3.01  cnf(c_2137,plain,
% 19.58/3.01      ( v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = iProver_top
% 19.58/3.01      | v1_relat_1(k6_relat_1(X0)) != iProver_top
% 19.58/3.01      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 19.58/3.01      inference(superposition,[status(thm)],[c_1209,c_547]) ).
% 19.58/3.01  
% 19.58/3.01  cnf(c_18,plain,
% 19.58/3.01      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 19.58/3.01      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 19.58/3.01  
% 19.58/3.01  cnf(c_4124,plain,
% 19.58/3.01      ( v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = iProver_top
% 19.58/3.01      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 19.58/3.01      inference(global_propositional_subsumption,[status(thm)],[c_2137,c_18]) ).
% 19.58/3.01  
% 19.58/3.01  cnf(c_4130,plain,
% 19.58/3.01      ( v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = iProver_top ),
% 19.58/3.01      inference(forward_subsumption_resolution,[status(thm)],[c_4124,c_537]) ).
% 19.58/3.01  
% 19.58/3.01  cnf(c_1,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f63]) ).
% 19.58/3.01  
% 19.58/3.01  cnf(c_549,plain,
% 19.58/3.01      ( r1_tarski(X0,X0) = iProver_top ),
% 19.58/3.01      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 19.58/3.01  
% 19.58/3.01  cnf(c_11,plain,
% 19.58/3.01      ( ~ r1_tarski(k1_relat_1(X0),X1)
% 19.58/3.01      | ~ v1_relat_1(X0)
% 19.58/3.01      | k5_relat_1(k6_relat_1(X1),X0) = X0 ),
% 19.58/3.01      inference(cnf_transformation,[],[f51]) ).
% 19.58/3.01  
% 19.58/3.01  cnf(c_542,plain,
% 19.58/3.01      ( k5_relat_1(k6_relat_1(X0),X1) = X1
% 19.58/3.01      | r1_tarski(k1_relat_1(X1),X0) != iProver_top
% 19.58/3.01      | v1_relat_1(X1) != iProver_top ),
% 19.58/3.01      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 19.58/3.01  
% 19.58/3.01  cnf(c_2172,plain,
% 19.58/3.01      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
% 19.58/3.01      | v1_relat_1(X0) != iProver_top ),
% 19.58/3.01      inference(superposition,[status(thm)],[c_549,c_542]) ).
% 19.58/3.01  
% 19.58/3.01  cnf(c_4140,plain,
% 19.58/3.01      ( k5_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),k7_relat_1(k6_relat_1(X0),X1)) = k7_relat_1(k6_relat_1(X0),X1) ),
% 19.58/3.01      inference(superposition,[status(thm)],[c_4130,c_2172]) ).
% 19.58/3.01  
% 19.58/3.01  cnf(c_14,plain,
% 19.58/3.01      ( ~ v1_relat_1(X0)
% 19.58/3.01      | k1_setfam_1(k2_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1)) ),
% 19.58/3.01      inference(cnf_transformation,[],[f61]) ).
% 19.58/3.01  
% 19.58/3.01  cnf(c_539,plain,
% 19.58/3.01      ( k1_setfam_1(k2_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1))
% 19.58/3.01      | v1_relat_1(X0) != iProver_top ),
% 19.58/3.01      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 19.58/3.01  
% 19.58/3.01  cnf(c_980,plain,
% 19.58/3.01      ( k1_setfam_1(k2_enumset1(k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
% 19.58/3.01      inference(superposition,[status(thm)],[c_537,c_539]) ).
% 19.58/3.01  
% 19.58/3.01  cnf(c_8,plain,
% 19.58/3.01      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 19.58/3.01      inference(cnf_transformation,[],[f47]) ).
% 19.58/3.01  
% 19.58/3.01  cnf(c_981,plain,
% 19.58/3.01      ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
% 19.58/3.01      inference(light_normalisation,[status(thm)],[c_980,c_8]) ).
% 19.58/3.01  
% 19.58/3.01  cnf(c_3,plain,
% 19.58/3.01      ( r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0) ),
% 19.58/3.01      inference(cnf_transformation,[],[f60]) ).
% 19.58/3.01  
% 19.58/3.01  cnf(c_548,plain,
% 19.58/3.01      ( r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0) = iProver_top ),
% 19.58/3.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 19.58/3.01  
% 19.58/3.01  cnf(c_984,plain,
% 19.58/3.01      ( r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X0) = iProver_top ),
% 19.58/3.01      inference(demodulation,[status(thm)],[c_981,c_548]) ).
% 19.58/3.01  
% 19.58/3.01  cnf(c_2173,plain,
% 19.58/3.01      ( k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X0),X1)) = k7_relat_1(k6_relat_1(X0),X1)
% 19.58/3.01      | v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) != iProver_top ),
% 19.58/3.01      inference(superposition,[status(thm)],[c_984,c_542]) ).
% 19.58/3.01  
% 19.58/3.01  cnf(c_4956,plain,
% 19.58/3.01      ( k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X0),X1)) = k7_relat_1(k6_relat_1(X0),X1) ),
% 19.58/3.01      inference(global_propositional_subsumption,[status(thm)],[c_2173,c_4130]) ).
% 19.58/3.01  
% 19.58/3.01  cnf(c_4136,plain,
% 19.58/3.01      ( k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X1),X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X0) ),
% 19.58/3.01      inference(superposition,[status(thm)],[c_4130,c_538]) ).
% 19.58/3.01  
% 19.58/3.01  cnf(c_4968,plain,
% 19.58/3.01      ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0) = k7_relat_1(k6_relat_1(X0),X1) ),
% 19.58/3.01      inference(superposition,[status(thm)],[c_4956,c_4136]) ).
% 19.58/3.01  
% 19.58/3.01  cnf(c_5,plain,
% 19.58/3.01      ( ~ v1_relat_1(X0)
% 19.58/3.01      | ~ v1_relat_1(X1)
% 19.58/3.01      | k7_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(k7_relat_1(X0,X2),X1) ),
% 19.58/3.01      inference(cnf_transformation,[],[f45]) ).
% 19.58/3.01  
% 19.58/3.01  cnf(c_546,plain,
% 19.58/3.01      ( k7_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(k7_relat_1(X0,X2),X1)
% 19.58/3.01      | v1_relat_1(X0) != iProver_top
% 19.58/3.01      | v1_relat_1(X1) != iProver_top ),
% 19.58/3.01      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 19.58/3.01  
% 19.58/3.01  cnf(c_2369,plain,
% 19.58/3.01      ( k7_relat_1(k5_relat_1(k6_relat_1(X0),X1),X2) = k5_relat_1(k7_relat_1(k6_relat_1(X0),X2),X1)
% 19.58/3.01      | v1_relat_1(X1) != iProver_top ),
% 19.58/3.01      inference(superposition,[status(thm)],[c_537,c_546]) ).
% 19.58/3.01  
% 19.58/3.01  cnf(c_3474,plain,
% 19.58/3.01      ( k7_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),X2) = k5_relat_1(k7_relat_1(k6_relat_1(X0),X2),k6_relat_1(X1)) ),
% 19.58/3.01      inference(superposition,[status(thm)],[c_537,c_2369]) ).
% 19.58/3.01  
% 19.58/3.01  cnf(c_3476,plain,
% 19.58/3.01      ( k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X0),X1) ),
% 19.58/3.01      inference(light_normalisation,[status(thm)],[c_3474,c_1209]) ).
% 19.58/3.01  
% 19.58/3.01  cnf(c_10,plain,
% 19.58/3.01      ( r1_tarski(k5_relat_1(X0,k6_relat_1(X1)),X0) | ~ v1_relat_1(X0) ),
% 19.58/3.01      inference(cnf_transformation,[],[f49]) ).
% 19.58/3.01  
% 19.58/3.01  cnf(c_543,plain,
% 19.58/3.01      ( r1_tarski(k5_relat_1(X0,k6_relat_1(X1)),X0) = iProver_top
% 19.58/3.01      | v1_relat_1(X0) != iProver_top ),
% 19.58/3.01      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 19.58/3.01  
% 19.58/3.01  cnf(c_3731,plain,
% 19.58/3.01      ( r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2),k7_relat_1(k6_relat_1(X1),X2)) = iProver_top
% 19.58/3.01      | v1_relat_1(k7_relat_1(k6_relat_1(X1),X2)) != iProver_top ),
% 19.58/3.01      inference(superposition,[status(thm)],[c_3476,c_543]) ).
% 19.58/3.01  
% 19.58/3.01  cnf(c_7679,plain,
% 19.58/3.01      ( r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2),k7_relat_1(k6_relat_1(X1),X2)) = iProver_top ),
% 19.58/3.01      inference(forward_subsumption_resolution,[status(thm)],[c_3731,c_4130]) ).
% 19.58/3.01  
% 19.58/3.01  cnf(c_7684,plain,
% 19.58/3.01      ( r1_tarski(k7_relat_1(k6_relat_1(X0),X1),k7_relat_1(k6_relat_1(X1),X0)) = iProver_top ),
% 19.58/3.01      inference(superposition,[status(thm)],[c_4968,c_7679]) ).
% 19.58/3.01  
% 19.58/3.01  cnf(c_0,plain,
% 19.58/3.01      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 19.58/3.01      inference(cnf_transformation,[],[f39]) ).
% 19.58/3.01  
% 19.58/3.01  cnf(c_550,plain,
% 19.58/3.01      ( X0 = X1
% 19.58/3.01      | r1_tarski(X0,X1) != iProver_top
% 19.58/3.01      | r1_tarski(X1,X0) != iProver_top ),
% 19.58/3.01      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 19.58/3.01  
% 19.58/3.01  cnf(c_7966,plain,
% 19.58/3.01      ( k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X1),X0)
% 19.58/3.01      | r1_tarski(k7_relat_1(k6_relat_1(X0),X1),k7_relat_1(k6_relat_1(X1),X0)) != iProver_top ),
% 19.58/3.01      inference(superposition,[status(thm)],[c_7684,c_550]) ).
% 19.58/3.01  
% 19.58/3.01  cnf(c_7969,plain,
% 19.58/3.01      ( k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X1),X0) ),
% 19.58/3.01      inference(forward_subsumption_resolution,[status(thm)],[c_7966,c_7684]) ).
% 19.58/3.01  
% 19.58/3.01  cnf(c_8165,plain,
% 19.58/3.01      ( k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X1),X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X1),X0) ),
% 19.58/3.01      inference(superposition,[status(thm)],[c_7969,c_4136]) ).
% 19.58/3.01  
% 19.58/3.01  cnf(c_45907,plain,
% 19.58/3.01      ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),k1_relat_1(k7_relat_1(k6_relat_1(X1),X0))) = k7_relat_1(k6_relat_1(X1),X0) ),
% 19.58/3.01      inference(superposition,[status(thm)],[c_4140,c_8165]) ).
% 19.58/3.01  
% 19.58/3.01  cnf(c_8155,plain,
% 19.58/3.01      ( k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X1),X0) ),
% 19.58/3.01      inference(superposition,[status(thm)],[c_7969,c_3476]) ).
% 19.58/3.01  
% 19.58/3.01  cnf(c_13695,plain,
% 19.58/3.01      ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X2),X1) ),
% 19.58/3.01      inference(superposition,[status(thm)],[c_8155,c_3476]) ).
% 19.58/3.01  
% 19.58/3.01  cnf(c_7,plain,
% 19.58/3.01      ( k2_relat_1(k6_relat_1(X0)) = X0 ),
% 19.58/3.01      inference(cnf_transformation,[],[f48]) ).
% 19.58/3.01  
% 19.58/3.01  cnf(c_12,plain,
% 19.58/3.01      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 19.58/3.01      | ~ v1_relat_1(X0)
% 19.58/3.01      | k5_relat_1(X0,k6_relat_1(X1)) = X0 ),
% 19.58/3.01      inference(cnf_transformation,[],[f52]) ).
% 19.58/3.01  
% 19.58/3.01  cnf(c_541,plain,
% 19.58/3.01      ( k5_relat_1(X0,k6_relat_1(X1)) = X0
% 19.58/3.01      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 19.58/3.01      | v1_relat_1(X0) != iProver_top ),
% 19.58/3.01      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 19.58/3.01  
% 19.58/3.01  cnf(c_2091,plain,
% 19.58/3.01      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k6_relat_1(X0)
% 19.58/3.01      | r1_tarski(X0,X1) != iProver_top
% 19.58/3.01      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 19.58/3.01      inference(superposition,[status(thm)],[c_7,c_541]) ).
% 19.58/3.01  
% 19.58/3.01  cnf(c_2095,plain,
% 19.58/3.01      ( k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X1)
% 19.58/3.01      | r1_tarski(X1,X0) != iProver_top
% 19.58/3.01      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 19.58/3.01      inference(demodulation,[status(thm)],[c_2091,c_1209]) ).
% 19.58/3.01  
% 19.58/3.01  cnf(c_3898,plain,
% 19.58/3.01      ( k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X1)
% 19.58/3.01      | r1_tarski(X1,X0) != iProver_top ),
% 19.58/3.01      inference(forward_subsumption_resolution,[status(thm)],[c_2095,c_537]) ).
% 19.58/3.01  
% 19.58/3.01  cnf(c_3902,plain,
% 19.58/3.01      ( k7_relat_1(k6_relat_1(X0),k5_relat_1(X0,k6_relat_1(X1))) = k6_relat_1(k5_relat_1(X0,k6_relat_1(X1)))
% 19.58/3.01      | v1_relat_1(X0) != iProver_top ),
% 19.58/3.01      inference(superposition,[status(thm)],[c_543,c_3898]) ).
% 19.58/3.01  
% 19.58/3.01  cnf(c_4137,plain,
% 19.58/3.01      ( k7_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X0),X1)),k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X2))) = k6_relat_1(k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X2))) ),
% 19.58/3.01      inference(superposition,[status(thm)],[c_4130,c_3902]) ).
% 19.58/3.01  
% 19.58/3.01  cnf(c_4163,plain,
% 19.58/3.01      ( k7_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X0),X1)),k7_relat_1(k7_relat_1(k6_relat_1(X2),X0),X1)) = k6_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X2),X0),X1)) ),
% 19.58/3.01      inference(light_normalisation,[status(thm)],[c_4137,c_3476]) ).
% 19.58/3.01  
% 19.58/3.01  cnf(c_53686,plain,
% 19.58/3.01      ( k7_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X0),X1)),k7_relat_1(k7_relat_1(k6_relat_1(X2),X1),X0)) = k6_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X2),X0),X1)) ),
% 19.58/3.01      inference(superposition,[status(thm)],[c_13695,c_4163]) ).
% 19.58/3.01  
% 19.58/3.01  cnf(c_3903,plain,
% 19.58/3.01      ( k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
% 19.58/3.01      inference(superposition,[status(thm)],[c_984,c_3898]) ).
% 19.58/3.01  
% 19.58/3.01  cnf(c_9,plain,
% 19.58/3.01      ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) | ~ v1_relat_1(X1) ),
% 19.58/3.01      inference(cnf_transformation,[],[f50]) ).
% 19.58/3.01  
% 19.58/3.01  cnf(c_544,plain,
% 19.58/3.01      ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) = iProver_top
% 19.58/3.01      | v1_relat_1(X1) != iProver_top ),
% 19.58/3.01      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 19.58/3.01  
% 19.58/3.01  cnf(c_1642,plain,
% 19.58/3.01      ( r1_tarski(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X0)) = iProver_top
% 19.58/3.01      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 19.58/3.01      inference(superposition,[status(thm)],[c_1209,c_544]) ).
% 19.58/3.01  
% 19.58/3.01  cnf(c_1931,plain,
% 19.58/3.01      ( r1_tarski(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X0)) = iProver_top ),
% 19.58/3.01      inference(global_propositional_subsumption,[status(thm)],[c_1642,c_18]) ).
% 19.58/3.01  
% 19.58/3.01  cnf(c_2174,plain,
% 19.58/3.01      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k6_relat_1(X1)
% 19.58/3.01      | r1_tarski(X1,X0) != iProver_top
% 19.58/3.01      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 19.58/3.01      inference(superposition,[status(thm)],[c_8,c_542]) ).
% 19.58/3.01  
% 19.58/3.01  cnf(c_2178,plain,
% 19.58/3.01      ( k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X0)
% 19.58/3.01      | r1_tarski(X0,X1) != iProver_top
% 19.58/3.01      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 19.58/3.01      inference(demodulation,[status(thm)],[c_2174,c_1209]) ).
% 19.58/3.01  
% 19.58/3.01  cnf(c_5130,plain,
% 19.58/3.01      ( r1_tarski(X0,X1) != iProver_top
% 19.58/3.01      | k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X0) ),
% 19.58/3.01      inference(global_propositional_subsumption,[status(thm)],[c_2178,c_18]) ).
% 19.58/3.01  
% 19.58/3.01  cnf(c_5131,plain,
% 19.58/3.01      ( k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X0)
% 19.58/3.01      | r1_tarski(X0,X1) != iProver_top ),
% 19.58/3.01      inference(renaming,[status(thm)],[c_5130]) ).
% 19.58/3.01  
% 19.58/3.01  cnf(c_5141,plain,
% 19.58/3.01      ( k7_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X0),X1)),k6_relat_1(X0)) = k6_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
% 19.58/3.01      inference(superposition,[status(thm)],[c_1931,c_5131]) ).
% 19.58/3.01  
% 19.58/3.01  cnf(c_8139,plain,
% 19.58/3.01      ( k7_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X0),X1)),k6_relat_1(X1)) = k6_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
% 19.58/3.01      inference(superposition,[status(thm)],[c_7969,c_5141]) ).
% 19.58/3.01  
% 19.58/3.01  cnf(c_1471,plain,
% 19.58/3.01      ( r1_tarski(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X1)) = iProver_top
% 19.58/3.01      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 19.58/3.01      inference(superposition,[status(thm)],[c_1209,c_543]) ).
% 19.58/3.01  
% 19.58/3.01  cnf(c_1925,plain,
% 19.58/3.01      ( r1_tarski(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X1)) = iProver_top ),
% 19.58/3.01      inference(forward_subsumption_resolution,[status(thm)],[c_1471,c_537]) ).
% 19.58/3.01  
% 19.58/3.01  cnf(c_5140,plain,
% 19.58/3.01      ( k7_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X0),X1)),k6_relat_1(X1)) = k6_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
% 19.58/3.01      inference(superposition,[status(thm)],[c_1925,c_5131]) ).
% 19.58/3.01  
% 19.58/3.01  cnf(c_10006,plain,
% 19.58/3.01      ( k6_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k6_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
% 19.58/3.01      inference(superposition,[status(thm)],[c_8139,c_5140]) ).
% 19.58/3.01  
% 19.58/3.01  cnf(c_10302,plain,
% 19.58/3.01      ( k1_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k7_relat_1(k6_relat_1(X1),X0) ),
% 19.58/3.01      inference(superposition,[status(thm)],[c_10006,c_8]) ).
% 19.58/3.01  
% 19.58/3.01  cnf(c_10703,plain,
% 19.58/3.01      ( k1_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X2))) = k7_relat_1(k6_relat_1(X2),k7_relat_1(k6_relat_1(X1),X0)) ),
% 19.58/3.01      inference(superposition,[status(thm)],[c_10006,c_10302]) ).
% 19.58/3.01  
% 19.58/3.01  cnf(c_11210,plain,
% 19.58/3.01      ( k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X2))),k7_relat_1(k6_relat_1(X1),X0)) = k1_relat_1(k6_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X2))))) ),
% 19.58/3.01      inference(superposition,[status(thm)],[c_3903,c_10703]) ).
% 19.58/3.01  
% 19.58/3.01  cnf(c_11263,plain,
% 19.58/3.01      ( k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X2))),k7_relat_1(k6_relat_1(X1),X0)) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X2))) ),
% 19.58/3.01      inference(demodulation,[status(thm)],[c_11210,c_8]) ).
% 19.58/3.01  
% 19.58/3.01  cnf(c_5139,plain,
% 19.58/3.01      ( k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X0) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
% 19.58/3.01      inference(superposition,[status(thm)],[c_984,c_5131]) ).
% 19.58/3.01  
% 19.58/3.01  cnf(c_18081,plain,
% 19.58/3.01      ( k7_relat_1(k6_relat_1(k1_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X2))))),k1_relat_1(k7_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X2))) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X2))),k7_relat_1(k6_relat_1(X1),X0)))) ),
% 19.58/3.01      inference(superposition,[status(thm)],[c_11263,c_5139]) ).
% 19.58/3.01  
% 19.58/3.01  cnf(c_18084,plain,
% 19.58/3.01      ( k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X2))),k7_relat_1(k6_relat_1(X1),X0)) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X1),X0)),X2))) ),
% 19.58/3.01      inference(superposition,[status(thm)],[c_10006,c_5139]) ).
% 19.58/3.01  
% 19.58/3.01  cnf(c_18295,plain,
% 19.58/3.01      ( k7_relat_1(k6_relat_1(k1_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X2))))),k1_relat_1(k7_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X2))) = k6_relat_1(k1_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X1),X0)),X2))))) ),
% 19.58/3.01      inference(light_normalisation,[status(thm)],[c_18081,c_18084]) ).
% 19.58/3.01  
% 19.58/3.01  cnf(c_13,plain,
% 19.58/3.01      ( ~ v1_relat_1(X0) | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ),
% 19.58/3.01      inference(cnf_transformation,[],[f53]) ).
% 19.58/3.01  
% 19.58/3.01  cnf(c_540,plain,
% 19.58/3.01      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
% 19.58/3.01      | v1_relat_1(X0) != iProver_top ),
% 19.58/3.01      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 19.58/3.01  
% 19.58/3.01  cnf(c_793,plain,
% 19.58/3.01      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(k2_relat_1(k6_relat_1(X0)))) = k6_relat_1(X0) ),
% 19.58/3.01      inference(superposition,[status(thm)],[c_537,c_540]) ).
% 19.58/3.01  
% 19.58/3.01  cnf(c_794,plain,
% 19.58/3.01      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X0)) = k6_relat_1(X0) ),
% 19.58/3.01      inference(light_normalisation,[status(thm)],[c_793,c_7]) ).
% 19.58/3.01  
% 19.58/3.01  cnf(c_1472,plain,
% 19.58/3.01      ( k7_relat_1(k6_relat_1(X0),X0) = k6_relat_1(X0) ),
% 19.58/3.01      inference(superposition,[status(thm)],[c_1209,c_794]) ).
% 19.58/3.01  
% 19.58/3.01  cnf(c_18297,plain,
% 19.58/3.01      ( k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X2))) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X1),X0)),X2))) ),
% 19.58/3.01      inference(demodulation,[status(thm)],[c_18295,c_8,c_1472]) ).
% 19.58/3.01  
% 19.58/3.01  cnf(c_20577,plain,
% 19.58/3.01      ( k1_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X2)))) = k1_relat_1(k7_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X1),X0)),X2)) ),
% 19.58/3.01      inference(superposition,[status(thm)],[c_18297,c_8]) ).
% 19.58/3.01  
% 19.58/3.01  cnf(c_53979,plain,
% 19.58/3.01      ( k1_relat_1(k7_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X0),X1)),k7_relat_1(k7_relat_1(k6_relat_1(X2),X1),X0))) = k1_relat_1(k6_relat_1(k1_relat_1(k6_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X2),X1),X0))))) ),
% 19.58/3.01      inference(superposition,[status(thm)],[c_4163,c_20577]) ).
% 19.58/3.01  
% 19.58/3.01  cnf(c_54017,plain,
% 19.58/3.01      ( k1_relat_1(k7_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X0),X1)),k7_relat_1(k7_relat_1(k6_relat_1(X2),X1),X0))) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X1),X0) ),
% 19.58/3.01      inference(demodulation,[status(thm)],[c_53979,c_8]) ).
% 19.58/3.01  
% 19.58/3.01  cnf(c_54555,plain,
% 19.58/3.01      ( k1_relat_1(k6_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2))) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X2),X1) ),
% 19.58/3.01      inference(demodulation,[status(thm)],[c_53686,c_54017]) ).
% 19.58/3.01  
% 19.58/3.01  cnf(c_89014,plain,
% 19.58/3.01      ( k7_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(k6_relat_1(X1),X0))),X1) = k1_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X1),X0))) ),
% 19.58/3.01      inference(superposition,[status(thm)],[c_45907,c_54555]) ).
% 19.58/3.01  
% 19.58/3.01  cnf(c_8161,plain,
% 19.58/3.01      ( r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X1) = iProver_top ),
% 19.58/3.01      inference(superposition,[status(thm)],[c_7969,c_984]) ).
% 19.58/3.01  
% 19.58/3.01  cnf(c_8277,plain,
% 19.58/3.01      ( k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(k6_relat_1(X1),X0))) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X1),X0))) ),
% 19.58/3.01      inference(superposition,[status(thm)],[c_8161,c_3898]) ).
% 19.58/3.01  
% 19.58/3.01  cnf(c_89158,plain,
% 19.58/3.01      ( k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X0) = k1_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
% 19.58/3.01      inference(light_normalisation,[status(thm)],[c_89014,c_8277]) ).
% 19.58/3.01  
% 19.58/3.01  cnf(c_8147,plain,
% 19.58/3.01      ( k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(k6_relat_1(X1),X0))) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
% 19.58/3.01      inference(superposition,[status(thm)],[c_7969,c_3903]) ).
% 19.58/3.01  
% 19.58/3.01  cnf(c_21369,plain,
% 19.58/3.01      ( k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X1),X0))) ),
% 19.58/3.01      inference(superposition,[status(thm)],[c_8277,c_8147]) ).
% 19.58/3.01  
% 19.58/3.01  cnf(c_22006,plain,
% 19.58/3.01      ( k1_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)))) = k1_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
% 19.58/3.01      inference(superposition,[status(thm)],[c_21369,c_8]) ).
% 19.58/3.01  
% 19.58/3.01  cnf(c_22593,plain,
% 19.58/3.01      ( k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
% 19.58/3.01      inference(superposition,[status(thm)],[c_22006,c_8]) ).
% 19.58/3.01  
% 19.58/3.01  cnf(c_8278,plain,
% 19.58/3.01      ( k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X1) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
% 19.58/3.01      inference(superposition,[status(thm)],[c_8161,c_5131]) ).
% 19.58/3.01  
% 19.58/3.01  cnf(c_23115,plain,
% 19.58/3.01      ( k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X0) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X1),X0))) ),
% 19.58/3.01      inference(superposition,[status(thm)],[c_22593,c_8278]) ).
% 19.58/3.01  
% 19.58/3.01  cnf(c_89159,plain,
% 19.58/3.01      ( k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k7_relat_1(k6_relat_1(X0),X1) ),
% 19.58/3.01      inference(demodulation,[status(thm)],[c_89158,c_10302,c_23115]) ).
% 19.58/3.01  
% 19.58/3.01  cnf(c_17,negated_conjecture,
% 19.58/3.01      ( k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) ),
% 19.58/3.01      inference(cnf_transformation,[],[f62]) ).
% 19.58/3.01  
% 19.58/3.01  cnf(c_986,plain,
% 19.58/3.01      ( k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(sK0),sK1))) != k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) ),
% 19.58/3.01      inference(demodulation,[status(thm)],[c_981,c_17]) ).
% 19.58/3.01  
% 19.58/3.01  cnf(c_1469,plain,
% 19.58/3.01      ( k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(sK0),sK1))) != k7_relat_1(k6_relat_1(sK0),sK1) ),
% 19.58/3.01      inference(demodulation,[status(thm)],[c_1209,c_986]) ).
% 19.58/3.01  
% 19.58/3.01  cnf(c_8087,plain,
% 19.58/3.01      ( k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(sK1),sK0))) != k7_relat_1(k6_relat_1(sK1),sK0) ),
% 19.58/3.01      inference(demodulation,[status(thm)],[c_7969,c_1469]) ).
% 19.58/3.01  
% 19.58/3.01  cnf(c_93843,plain,
% 19.58/3.01      ( k7_relat_1(k6_relat_1(sK1),sK0) != k7_relat_1(k6_relat_1(sK1),sK0) ),
% 19.58/3.01      inference(demodulation,[status(thm)],[c_89159,c_8087]) ).
% 19.58/3.01  
% 19.58/3.01  cnf(c_93869,plain,
% 19.58/3.01      ( $false ),
% 19.58/3.01      inference(equality_resolution_simp,[status(thm)],[c_93843]) ).
% 19.58/3.01  
% 19.58/3.01  
% 19.58/3.01  % SZS output end CNFRefutation for theBenchmark.p
% 19.58/3.01  
% 19.58/3.01  ------                               Statistics
% 19.58/3.01  
% 19.58/3.01  ------ General
% 19.58/3.01  
% 19.58/3.01  abstr_ref_over_cycles:                  0
% 19.58/3.01  abstr_ref_under_cycles:                 0
% 19.58/3.01  gc_basic_clause_elim:                   0
% 19.58/3.01  forced_gc_time:                         0
% 19.58/3.01  parsing_time:                           0.011
% 19.58/3.01  unif_index_cands_time:                  0.
% 19.58/3.01  unif_index_add_time:                    0.
% 19.58/3.01  orderings_time:                         0.
% 19.58/3.01  out_proof_time:                         0.013
% 19.58/3.01  total_time:                             2.374
% 19.58/3.01  num_of_symbols:                         42
% 19.58/3.01  num_of_terms:                           109765
% 19.58/3.01  
% 19.58/3.01  ------ Preprocessing
% 19.58/3.01  
% 19.58/3.01  num_of_splits:                          0
% 19.58/3.01  num_of_split_atoms:                     0
% 19.58/3.01  num_of_reused_defs:                     0
% 19.58/3.01  num_eq_ax_congr_red:                    6
% 19.58/3.01  num_of_sem_filtered_clauses:            1
% 19.58/3.01  num_of_subtypes:                        0
% 19.58/3.01  monotx_restored_types:                  0
% 19.58/3.01  sat_num_of_epr_types:                   0
% 19.58/3.01  sat_num_of_non_cyclic_types:            0
% 19.58/3.01  sat_guarded_non_collapsed_types:        0
% 19.58/3.01  num_pure_diseq_elim:                    0
% 19.58/3.01  simp_replaced_by:                       0
% 19.58/3.01  res_preprocessed:                       91
% 19.58/3.01  prep_upred:                             0
% 19.58/3.01  prep_unflattend:                        0
% 19.58/3.01  smt_new_axioms:                         0
% 19.58/3.01  pred_elim_cands:                        2
% 19.58/3.01  pred_elim:                              0
% 19.58/3.01  pred_elim_cl:                           0
% 19.58/3.01  pred_elim_cycles:                       2
% 19.58/3.01  merged_defs:                            0
% 19.58/3.01  merged_defs_ncl:                        0
% 19.58/3.01  bin_hyper_res:                          0
% 19.58/3.01  prep_cycles:                            4
% 19.58/3.01  pred_elim_time:                         0.
% 19.58/3.01  splitting_time:                         0.
% 19.58/3.01  sem_filter_time:                        0.
% 19.58/3.01  monotx_time:                            0.001
% 19.58/3.01  subtype_inf_time:                       0.
% 19.58/3.01  
% 19.58/3.01  ------ Problem properties
% 19.58/3.01  
% 19.58/3.01  clauses:                                17
% 19.58/3.01  conjectures:                            1
% 19.58/3.01  epr:                                    2
% 19.58/3.01  horn:                                   17
% 19.58/3.01  ground:                                 1
% 19.58/3.01  unary:                                  6
% 19.58/3.01  binary:                                 5
% 19.58/3.01  lits:                                   35
% 19.58/3.01  lits_eq:                                11
% 19.58/3.01  fd_pure:                                0
% 19.58/3.01  fd_pseudo:                              0
% 19.58/3.01  fd_cond:                                0
% 19.58/3.01  fd_pseudo_cond:                         1
% 19.58/3.01  ac_symbols:                             0
% 19.58/3.01  
% 19.58/3.01  ------ Propositional Solver
% 19.58/3.01  
% 19.58/3.01  prop_solver_calls:                      32
% 19.58/3.01  prop_fast_solver_calls:                 815
% 19.58/3.01  smt_solver_calls:                       0
% 19.58/3.01  smt_fast_solver_calls:                  0
% 19.58/3.01  prop_num_of_clauses:                    27022
% 19.58/3.01  prop_preprocess_simplified:             29670
% 19.58/3.01  prop_fo_subsumed:                       6
% 19.58/3.01  prop_solver_time:                       0.
% 19.58/3.01  smt_solver_time:                        0.
% 19.58/3.01  smt_fast_solver_time:                   0.
% 19.58/3.01  prop_fast_solver_time:                  0.
% 19.58/3.01  prop_unsat_core_time:                   0.
% 19.58/3.01  
% 19.58/3.01  ------ QBF
% 19.58/3.01  
% 19.58/3.01  qbf_q_res:                              0
% 19.58/3.01  qbf_num_tautologies:                    0
% 19.58/3.01  qbf_prep_cycles:                        0
% 19.58/3.01  
% 19.58/3.01  ------ BMC1
% 19.58/3.01  
% 19.58/3.01  bmc1_current_bound:                     -1
% 19.58/3.01  bmc1_last_solved_bound:                 -1
% 19.58/3.01  bmc1_unsat_core_size:                   -1
% 19.58/3.01  bmc1_unsat_core_parents_size:           -1
% 19.58/3.01  bmc1_merge_next_fun:                    0
% 19.58/3.01  bmc1_unsat_core_clauses_time:           0.
% 19.58/3.01  
% 19.58/3.01  ------ Instantiation
% 19.58/3.01  
% 19.58/3.01  inst_num_of_clauses:                    4284
% 19.58/3.01  inst_num_in_passive:                    2899
% 19.58/3.01  inst_num_in_active:                     1386
% 19.58/3.01  inst_num_in_unprocessed:                0
% 19.58/3.01  inst_num_of_loops:                      1560
% 19.58/3.01  inst_num_of_learning_restarts:          0
% 19.58/3.01  inst_num_moves_active_passive:          171
% 19.58/3.01  inst_lit_activity:                      0
% 19.58/3.01  inst_lit_activity_moves:                2
% 19.58/3.01  inst_num_tautologies:                   0
% 19.58/3.01  inst_num_prop_implied:                  0
% 19.58/3.01  inst_num_existing_simplified:           0
% 19.58/3.01  inst_num_eq_res_simplified:             0
% 19.58/3.01  inst_num_child_elim:                    0
% 19.58/3.01  inst_num_of_dismatching_blockings:      2455
% 19.58/3.01  inst_num_of_non_proper_insts:           3989
% 19.58/3.01  inst_num_of_duplicates:                 0
% 19.58/3.01  inst_inst_num_from_inst_to_res:         0
% 19.58/3.01  inst_dismatching_checking_time:         0.
% 19.58/3.01  
% 19.58/3.01  ------ Resolution
% 19.58/3.01  
% 19.58/3.01  res_num_of_clauses:                     0
% 19.58/3.01  res_num_in_passive:                     0
% 19.58/3.01  res_num_in_active:                      0
% 19.58/3.01  res_num_of_loops:                       95
% 19.58/3.01  res_forward_subset_subsumed:            694
% 19.58/3.01  res_backward_subset_subsumed:           10
% 19.58/3.01  res_forward_subsumed:                   0
% 19.58/3.01  res_backward_subsumed:                  0
% 19.58/3.01  res_forward_subsumption_resolution:     0
% 19.58/3.01  res_backward_subsumption_resolution:    0
% 19.58/3.01  res_clause_to_clause_subsumption:       57315
% 19.58/3.01  res_orphan_elimination:                 0
% 19.58/3.01  res_tautology_del:                      336
% 19.58/3.01  res_num_eq_res_simplified:              0
% 19.58/3.01  res_num_sel_changes:                    0
% 19.58/3.01  res_moves_from_active_to_pass:          0
% 19.58/3.01  
% 19.58/3.01  ------ Superposition
% 19.58/3.01  
% 19.58/3.01  sup_time_total:                         0.
% 19.58/3.01  sup_time_generating:                    0.
% 19.58/3.01  sup_time_sim_full:                      0.
% 19.58/3.01  sup_time_sim_immed:                     0.
% 19.58/3.01  
% 19.58/3.01  sup_num_of_clauses:                     6589
% 19.58/3.01  sup_num_in_active:                      248
% 19.58/3.01  sup_num_in_passive:                     6341
% 19.58/3.01  sup_num_of_loops:                       310
% 19.58/3.01  sup_fw_superposition:                   20898
% 19.58/3.01  sup_bw_superposition:                   11555
% 19.58/3.01  sup_immediate_simplified:               7911
% 19.58/3.01  sup_given_eliminated:                   2
% 19.58/3.01  comparisons_done:                       0
% 19.58/3.01  comparisons_avoided:                    0
% 19.58/3.01  
% 19.58/3.01  ------ Simplifications
% 19.58/3.01  
% 19.58/3.01  
% 19.58/3.01  sim_fw_subset_subsumed:                 62
% 19.58/3.01  sim_bw_subset_subsumed:                 13
% 19.58/3.01  sim_fw_subsumed:                        2583
% 19.58/3.01  sim_bw_subsumed:                        26
% 19.58/3.01  sim_fw_subsumption_res:                 6
% 19.58/3.01  sim_bw_subsumption_res:                 0
% 19.58/3.01  sim_tautology_del:                      7
% 19.58/3.01  sim_eq_tautology_del:                   648
% 19.58/3.01  sim_eq_res_simp:                        0
% 19.58/3.01  sim_fw_demodulated:                     3184
% 19.58/3.01  sim_bw_demodulated:                     212
% 19.58/3.01  sim_light_normalised:                   3395
% 19.58/3.01  sim_joinable_taut:                      0
% 19.58/3.01  sim_joinable_simp:                      0
% 19.58/3.01  sim_ac_normalised:                      0
% 19.58/3.01  sim_smt_subsumption:                    0
% 19.58/3.01  
%------------------------------------------------------------------------------
