%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:49:58 EST 2020

% Result     : Theorem 7.91s
% Output     : CNFRefutation 7.91s
% Verified   : 
% Statistics : Number of formulae       :  165 (13208 expanded)
%              Number of clauses        :  118 (6079 expanded)
%              Number of leaves         :   15 (2772 expanded)
%              Depth                    :   29
%              Number of atoms          :  248 (20536 expanded)
%              Number of equality atoms :  186 (11901 expanded)
%              Maximal formula depth    :    8 (   2 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    8 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f43,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f31,f30])).

fof(f44,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f28,f43])).

fof(f8,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f17,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f45,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(definition_unfolding,[],[f29,f30,f30])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),X0)) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f40,f43])).

fof(f35,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f37,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f39,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f14,conjecture,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f14])).

fof(f25,plain,(
    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f15])).

fof(f26,plain,
    ( ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))
   => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f26])).

fof(f42,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f27])).

fof(f47,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))) ),
    inference(definition_unfolding,[],[f42,f43])).

cnf(c_3,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_314,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_0,plain,
    ( r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_316,plain,
    ( r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_5,plain,
    ( k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_8,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_relat_1(X1)) = X0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_311,plain,
    ( k5_relat_1(X0,k6_relat_1(X1)) = X0
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_858,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k6_relat_1(X0)
    | r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5,c_311])).

cnf(c_11,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_308,plain,
    ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_823,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(superposition,[status(thm)],[c_314,c_308])).

cnf(c_859,plain,
    ( k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X1)
    | r1_tarski(X1,X0) != iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_858,c_823])).

cnf(c_1146,plain,
    ( k7_relat_1(k6_relat_1(X0),k1_setfam_1(k1_enumset1(X0,X0,X1))) = k6_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1)))
    | v1_relat_1(k6_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_316,c_859])).

cnf(c_4568,plain,
    ( k7_relat_1(k6_relat_1(X0),k1_setfam_1(k1_enumset1(X0,X0,X1))) = k6_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1))) ),
    inference(superposition,[status(thm)],[c_314,c_1146])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | k5_relat_1(k5_relat_1(X1,X0),X2) = k5_relat_1(X1,k5_relat_1(X0,X2)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_313,plain,
    ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_924,plain,
    ( k5_relat_1(k5_relat_1(k6_relat_1(X0),X1),X2) = k5_relat_1(k6_relat_1(X0),k5_relat_1(X1,X2))
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_314,c_313])).

cnf(c_3922,plain,
    ( k5_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),X2) = k5_relat_1(k6_relat_1(X0),k5_relat_1(k6_relat_1(X1),X2))
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_314,c_924])).

cnf(c_3925,plain,
    ( k5_relat_1(k6_relat_1(X0),k5_relat_1(k6_relat_1(X1),X2)) = k5_relat_1(k7_relat_1(k6_relat_1(X1),X0),X2)
    | v1_relat_1(X2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3922,c_823])).

cnf(c_4185,plain,
    ( k5_relat_1(k6_relat_1(X0),k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) = k5_relat_1(k7_relat_1(k6_relat_1(X1),X0),k6_relat_1(X2)) ),
    inference(superposition,[status(thm)],[c_314,c_3925])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | v1_relat_1(k5_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_315,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k5_relat_1(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_905,plain,
    ( v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_823,c_315])).

cnf(c_33,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1160,plain,
    ( v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_905,c_33])).

cnf(c_1165,plain,
    ( k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X1),X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X0)
    | v1_relat_1(k6_relat_1(X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1160,c_308])).

cnf(c_1227,plain,
    ( k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X1),X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X0) ),
    inference(superposition,[status(thm)],[c_314,c_1165])).

cnf(c_4189,plain,
    ( k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X0),X1) ),
    inference(demodulation,[status(thm)],[c_4185,c_823,c_1227])).

cnf(c_4677,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),k1_setfam_1(k1_enumset1(X1,X1,X2))) = k5_relat_1(k6_relat_1(k1_setfam_1(k1_enumset1(X1,X1,X2))),k6_relat_1(X0)) ),
    inference(superposition,[status(thm)],[c_4568,c_4189])).

cnf(c_4805,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),k1_setfam_1(k1_enumset1(X1,X1,X2))) = k7_relat_1(k6_relat_1(X0),k1_setfam_1(k1_enumset1(X1,X1,X2))) ),
    inference(demodulation,[status(thm)],[c_4677,c_823])).

cnf(c_1,plain,
    ( k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_10,plain,
    ( ~ v1_relat_1(X0)
    | k1_setfam_1(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_309,plain,
    ( k1_setfam_1(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_543,plain,
    ( k1_setfam_1(k1_enumset1(k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(superposition,[status(thm)],[c_314,c_309])).

cnf(c_6,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_544,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(light_normalisation,[status(thm)],[c_543,c_6])).

cnf(c_550,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
    inference(superposition,[status(thm)],[c_1,c_544])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_312,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1168,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),k7_relat_1(k6_relat_1(X0),X1)) = k7_relat_1(k6_relat_1(X0),X1)
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1160,c_312])).

cnf(c_1306,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k7_relat_1(k6_relat_1(X0),X1)
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1168,c_1227])).

cnf(c_1310,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(superposition,[status(thm)],[c_314,c_1306])).

cnf(c_1316,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),k1_setfam_1(k1_enumset1(X1,X1,X0))) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(superposition,[status(thm)],[c_550,c_1310])).

cnf(c_36050,plain,
    ( k7_relat_1(k6_relat_1(X0),k1_setfam_1(k1_enumset1(X1,X1,X0))) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(superposition,[status(thm)],[c_4805,c_1316])).

cnf(c_4666,plain,
    ( k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k6_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1))) ),
    inference(superposition,[status(thm)],[c_544,c_4568])).

cnf(c_36255,plain,
    ( k6_relat_1(k1_setfam_1(k1_enumset1(X0,X0,k1_setfam_1(k1_enumset1(X1,X1,X0))))) = k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
    inference(superposition,[status(thm)],[c_36050,c_4666])).

cnf(c_614,plain,
    ( k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
    inference(superposition,[status(thm)],[c_550,c_544])).

cnf(c_4665,plain,
    ( k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(k6_relat_1(X1),X0))) = k6_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1))) ),
    inference(superposition,[status(thm)],[c_550,c_4568])).

cnf(c_4982,plain,
    ( k6_relat_1(k1_setfam_1(k1_enumset1(k1_setfam_1(k1_enumset1(X0,X0,X1)),k1_setfam_1(k1_enumset1(X0,X0,X1)),X0))) = k7_relat_1(k6_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1))),k1_relat_1(k6_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1))))) ),
    inference(superposition,[status(thm)],[c_4568,c_4665])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_310,plain,
    ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_621,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(k2_relat_1(k6_relat_1(X0)))) = k6_relat_1(X0) ),
    inference(superposition,[status(thm)],[c_314,c_310])).

cnf(c_622,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X0)) = k6_relat_1(X0) ),
    inference(light_normalisation,[status(thm)],[c_621,c_5])).

cnf(c_826,plain,
    ( k7_relat_1(k6_relat_1(X0),X0) = k6_relat_1(X0) ),
    inference(superposition,[status(thm)],[c_622,c_823])).

cnf(c_546,plain,
    ( k1_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(X0)),X1)) = k1_relat_1(k7_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_544,c_309])).

cnf(c_1166,plain,
    ( k1_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X2)) = k1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2))
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1160,c_546])).

cnf(c_1603,plain,
    ( k1_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X2)) = k1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)) ),
    inference(superposition,[status(thm)],[c_314,c_1166])).

cnf(c_1647,plain,
    ( k1_relat_1(k7_relat_1(k6_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1))),X2)) = k1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)) ),
    inference(superposition,[status(thm)],[c_544,c_1603])).

cnf(c_2150,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),k1_setfam_1(k1_enumset1(X0,X0,X1)))) = k1_relat_1(k6_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1)))) ),
    inference(superposition,[status(thm)],[c_826,c_1647])).

cnf(c_1314,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),k1_setfam_1(k1_enumset1(X0,X0,X1))) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(superposition,[status(thm)],[c_544,c_1310])).

cnf(c_2177,plain,
    ( k1_relat_1(k6_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1)))) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(light_normalisation,[status(thm)],[c_2150,c_1314])).

cnf(c_2286,plain,
    ( k1_relat_1(k6_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1)))) = k1_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
    inference(superposition,[status(thm)],[c_1,c_2177])).

cnf(c_908,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1(k5_relat_1(X0,X1))),k5_relat_1(X0,X1)) = k5_relat_1(X0,X1)
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_315,c_312])).

cnf(c_1855,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(X0),X1))),k5_relat_1(k6_relat_1(X0),X1)) = k5_relat_1(k6_relat_1(X0),X1)
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_314,c_908])).

cnf(c_3820,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)))),k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) ),
    inference(superposition,[status(thm)],[c_314,c_1855])).

cnf(c_3823,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),k7_relat_1(k6_relat_1(X0),X1)) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(light_normalisation,[status(thm)],[c_3820,c_823])).

cnf(c_4035,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),k7_relat_1(k6_relat_1(X1),X0)) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(superposition,[status(thm)],[c_614,c_3823])).

cnf(c_4710,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1))),X0))),k6_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1)))) = k7_relat_1(k6_relat_1(X0),k1_setfam_1(k1_enumset1(X0,X0,X1))) ),
    inference(superposition,[status(thm)],[c_4568,c_4035])).

cnf(c_4753,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1))),X0))),k6_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1)))) = k6_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1))) ),
    inference(demodulation,[status(thm)],[c_4710,c_4568])).

cnf(c_1649,plain,
    ( k1_relat_1(k7_relat_1(k6_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1))),X2)) = k1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X1),X0),X2)) ),
    inference(superposition,[status(thm)],[c_550,c_1603])).

cnf(c_4754,plain,
    ( k7_relat_1(k6_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1))),k1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X1),X0),X0))) = k6_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1))) ),
    inference(demodulation,[status(thm)],[c_4753,c_823,c_1649])).

cnf(c_4201,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X1) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
    inference(superposition,[status(thm)],[c_826,c_4189])).

cnf(c_4204,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X1) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(demodulation,[status(thm)],[c_4201,c_823])).

cnf(c_4755,plain,
    ( k7_relat_1(k6_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1))),k1_relat_1(k7_relat_1(k6_relat_1(X1),X0))) = k6_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1))) ),
    inference(demodulation,[status(thm)],[c_4754,c_4204])).

cnf(c_5116,plain,
    ( k6_relat_1(k1_setfam_1(k1_enumset1(k1_setfam_1(k1_enumset1(X0,X0,X1)),k1_setfam_1(k1_enumset1(X0,X0,X1)),X0))) = k6_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1))) ),
    inference(light_normalisation,[status(thm)],[c_4982,c_2286,c_4755])).

cnf(c_2792,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,k1_setfam_1(k1_enumset1(X1,X1,X2)))) = k1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X2),X1),X0)) ),
    inference(superposition,[status(thm)],[c_1649,c_550])).

cnf(c_617,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = k1_setfam_1(k1_enumset1(X1,X1,X0)) ),
    inference(superposition,[status(thm)],[c_550,c_544])).

cnf(c_3544,plain,
    ( k1_setfam_1(k1_enumset1(k1_setfam_1(k1_enumset1(X0,X0,X1)),k1_setfam_1(k1_enumset1(X0,X0,X1)),X2)) = k1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X1),X0),X2)) ),
    inference(superposition,[status(thm)],[c_2792,c_617])).

cnf(c_5117,plain,
    ( k6_relat_1(k1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X1))) = k6_relat_1(k1_setfam_1(k1_enumset1(X1,X1,X0))) ),
    inference(demodulation,[status(thm)],[c_5116,c_3544])).

cnf(c_5118,plain,
    ( k6_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1))) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X1),X0))) ),
    inference(light_normalisation,[status(thm)],[c_5117,c_4204])).

cnf(c_5149,plain,
    ( k6_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1))) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
    inference(superposition,[status(thm)],[c_614,c_5118])).

cnf(c_6148,plain,
    ( k2_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)))) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(superposition,[status(thm)],[c_5149,c_5])).

cnf(c_36256,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,k1_setfam_1(k1_enumset1(X1,X1,X0)))) = k2_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)))) ),
    inference(superposition,[status(thm)],[c_36050,c_6148])).

cnf(c_36295,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,k1_setfam_1(k1_enumset1(X1,X1,X0)))) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(superposition,[status(thm)],[c_36050,c_544])).

cnf(c_36487,plain,
    ( k2_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)))) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(demodulation,[status(thm)],[c_36256,c_36295])).

cnf(c_5138,plain,
    ( k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X1),X0))) ),
    inference(superposition,[status(thm)],[c_544,c_5118])).

cnf(c_5696,plain,
    ( k2_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)))) = k1_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
    inference(superposition,[status(thm)],[c_5138,c_5])).

cnf(c_4708,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,k1_setfam_1(k1_enumset1(X0,X0,X1)))) = k1_relat_1(k6_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1)))) ),
    inference(superposition,[status(thm)],[c_4568,c_544])).

cnf(c_4759,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,k1_setfam_1(k1_enumset1(X0,X0,X1)))) = k1_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
    inference(light_normalisation,[status(thm)],[c_4708,c_2286])).

cnf(c_8017,plain,
    ( k6_relat_1(k1_setfam_1(k1_enumset1(X0,X0,k1_setfam_1(k1_enumset1(X0,X0,X1))))) = k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(k6_relat_1(X1),X0))) ),
    inference(superposition,[status(thm)],[c_4759,c_4568])).

cnf(c_8072,plain,
    ( k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(k6_relat_1(X1),X0))) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X1),X0))) ),
    inference(demodulation,[status(thm)],[c_8017,c_4759])).

cnf(c_8977,plain,
    ( k7_relat_1(k6_relat_1(X0),k1_setfam_1(k1_enumset1(X1,X1,X0))) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X1),X0))) ),
    inference(superposition,[status(thm)],[c_544,c_8072])).

cnf(c_36148,plain,
    ( k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(demodulation,[status(thm)],[c_36050,c_8977])).

cnf(c_36488,plain,
    ( k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k2_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
    inference(light_normalisation,[status(thm)],[c_36487,c_5696,c_36148])).

cnf(c_36489,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,k1_setfam_1(k1_enumset1(X1,X1,X0)))) = k2_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
    inference(demodulation,[status(thm)],[c_36488,c_36295])).

cnf(c_5199,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),k6_relat_1(X2)) = k7_relat_1(k6_relat_1(X2),k1_setfam_1(k1_enumset1(X1,X1,X0))) ),
    inference(superposition,[status(thm)],[c_5118,c_823])).

cnf(c_20945,plain,
    ( k7_relat_1(k6_relat_1(X0),k1_setfam_1(k1_enumset1(X1,X1,X2))) = k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(k6_relat_1(X2),X1))) ),
    inference(superposition,[status(thm)],[c_5199,c_823])).

cnf(c_36346,plain,
    ( k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(superposition,[status(thm)],[c_36050,c_20945])).

cnf(c_36490,plain,
    ( k7_relat_1(k6_relat_1(X0),k2_relat_1(k7_relat_1(k6_relat_1(X1),X0))) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(demodulation,[status(thm)],[c_36488,c_36346])).

cnf(c_36493,plain,
    ( k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(demodulation,[status(thm)],[c_36255,c_36488,c_36489,c_36490])).

cnf(c_1169,plain,
    ( k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)))) = k7_relat_1(k6_relat_1(X0),X1)
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1160,c_310])).

cnf(c_1554,plain,
    ( k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)))) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(superposition,[status(thm)],[c_314,c_1169])).

cnf(c_4203,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X0),X1) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(superposition,[status(thm)],[c_4189,c_1554])).

cnf(c_36260,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X0),k1_setfam_1(k1_enumset1(X1,X1,X0))) = k7_relat_1(k6_relat_1(X0),k1_setfam_1(k1_enumset1(X1,X1,X0))) ),
    inference(superposition,[status(thm)],[c_36050,c_4203])).

cnf(c_36264,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),k1_setfam_1(k1_enumset1(X2,X2,X1))) = k5_relat_1(k7_relat_1(k6_relat_1(X1),X2),k6_relat_1(X0)) ),
    inference(superposition,[status(thm)],[c_36050,c_4189])).

cnf(c_36031,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),k1_setfam_1(k1_enumset1(X2,X2,X1))) = k7_relat_1(k6_relat_1(X0),k1_setfam_1(k1_enumset1(X1,X1,X2))) ),
    inference(superposition,[status(thm)],[c_1,c_4805])).

cnf(c_36479,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),k1_setfam_1(k1_enumset1(X2,X2,X1))) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) ),
    inference(demodulation,[status(thm)],[c_36264,c_4189,c_36031])).

cnf(c_36484,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X0),k1_setfam_1(k1_enumset1(X1,X1,X0))) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(demodulation,[status(thm)],[c_36260,c_36050,c_36479])).

cnf(c_36494,plain,
    ( k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X1),k1_setfam_1(k1_enumset1(X0,X0,X1))) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(demodulation,[status(thm)],[c_36493,c_36484])).

cnf(c_36495,plain,
    ( k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(light_normalisation,[status(thm)],[c_36494,c_1314,c_4204])).

cnf(c_12,negated_conjecture,
    ( k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_443,plain,
    ( k6_relat_1(k1_setfam_1(k1_enumset1(sK1,sK1,sK0))) != k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) ),
    inference(demodulation,[status(thm)],[c_1,c_12])).

cnf(c_825,plain,
    ( k6_relat_1(k1_setfam_1(k1_enumset1(sK1,sK1,sK0))) != k7_relat_1(k6_relat_1(sK0),sK1) ),
    inference(demodulation,[status(thm)],[c_823,c_443])).

cnf(c_36720,plain,
    ( k6_relat_1(k1_setfam_1(k1_enumset1(sK1,sK1,sK0))) != k7_relat_1(k6_relat_1(sK1),sK0) ),
    inference(demodulation,[status(thm)],[c_36495,c_825])).

cnf(c_4673,plain,
    ( k7_relat_1(k6_relat_1(X0),k1_setfam_1(k1_enumset1(X1,X1,X0))) = k6_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1))) ),
    inference(superposition,[status(thm)],[c_1,c_4568])).

cnf(c_36149,plain,
    ( k6_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1))) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(demodulation,[status(thm)],[c_36050,c_4673])).

cnf(c_36727,plain,
    ( k7_relat_1(k6_relat_1(sK1),sK0) != k7_relat_1(k6_relat_1(sK1),sK0) ),
    inference(demodulation,[status(thm)],[c_36720,c_36149])).

cnf(c_36728,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_36727])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 14:49:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.91/1.48  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.91/1.48  
% 7.91/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.91/1.48  
% 7.91/1.48  ------  iProver source info
% 7.91/1.48  
% 7.91/1.48  git: date: 2020-06-30 10:37:57 +0100
% 7.91/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.91/1.48  git: non_committed_changes: false
% 7.91/1.48  git: last_make_outside_of_git: false
% 7.91/1.48  
% 7.91/1.48  ------ 
% 7.91/1.48  
% 7.91/1.48  ------ Input Options
% 7.91/1.48  
% 7.91/1.48  --out_options                           all
% 7.91/1.48  --tptp_safe_out                         true
% 7.91/1.48  --problem_path                          ""
% 7.91/1.48  --include_path                          ""
% 7.91/1.48  --clausifier                            res/vclausify_rel
% 7.91/1.48  --clausifier_options                    ""
% 7.91/1.48  --stdin                                 false
% 7.91/1.48  --stats_out                             all
% 7.91/1.48  
% 7.91/1.48  ------ General Options
% 7.91/1.48  
% 7.91/1.48  --fof                                   false
% 7.91/1.48  --time_out_real                         305.
% 7.91/1.48  --time_out_virtual                      -1.
% 7.91/1.48  --symbol_type_check                     false
% 7.91/1.48  --clausify_out                          false
% 7.91/1.48  --sig_cnt_out                           false
% 7.91/1.48  --trig_cnt_out                          false
% 7.91/1.48  --trig_cnt_out_tolerance                1.
% 7.91/1.48  --trig_cnt_out_sk_spl                   false
% 7.91/1.48  --abstr_cl_out                          false
% 7.91/1.48  
% 7.91/1.48  ------ Global Options
% 7.91/1.48  
% 7.91/1.48  --schedule                              default
% 7.91/1.48  --add_important_lit                     false
% 7.91/1.48  --prop_solver_per_cl                    1000
% 7.91/1.48  --min_unsat_core                        false
% 7.91/1.48  --soft_assumptions                      false
% 7.91/1.48  --soft_lemma_size                       3
% 7.91/1.48  --prop_impl_unit_size                   0
% 7.91/1.48  --prop_impl_unit                        []
% 7.91/1.48  --share_sel_clauses                     true
% 7.91/1.48  --reset_solvers                         false
% 7.91/1.48  --bc_imp_inh                            [conj_cone]
% 7.91/1.48  --conj_cone_tolerance                   3.
% 7.91/1.48  --extra_neg_conj                        none
% 7.91/1.48  --large_theory_mode                     true
% 7.91/1.48  --prolific_symb_bound                   200
% 7.91/1.48  --lt_threshold                          2000
% 7.91/1.48  --clause_weak_htbl                      true
% 7.91/1.48  --gc_record_bc_elim                     false
% 7.91/1.48  
% 7.91/1.48  ------ Preprocessing Options
% 7.91/1.48  
% 7.91/1.48  --preprocessing_flag                    true
% 7.91/1.48  --time_out_prep_mult                    0.1
% 7.91/1.48  --splitting_mode                        input
% 7.91/1.48  --splitting_grd                         true
% 7.91/1.48  --splitting_cvd                         false
% 7.91/1.48  --splitting_cvd_svl                     false
% 7.91/1.48  --splitting_nvd                         32
% 7.91/1.48  --sub_typing                            true
% 7.91/1.48  --prep_gs_sim                           true
% 7.91/1.48  --prep_unflatten                        true
% 7.91/1.48  --prep_res_sim                          true
% 7.91/1.48  --prep_upred                            true
% 7.91/1.48  --prep_sem_filter                       exhaustive
% 7.91/1.48  --prep_sem_filter_out                   false
% 7.91/1.48  --pred_elim                             true
% 7.91/1.48  --res_sim_input                         true
% 7.91/1.48  --eq_ax_congr_red                       true
% 7.91/1.48  --pure_diseq_elim                       true
% 7.91/1.48  --brand_transform                       false
% 7.91/1.48  --non_eq_to_eq                          false
% 7.91/1.48  --prep_def_merge                        true
% 7.91/1.48  --prep_def_merge_prop_impl              false
% 7.91/1.48  --prep_def_merge_mbd                    true
% 7.91/1.48  --prep_def_merge_tr_red                 false
% 7.91/1.48  --prep_def_merge_tr_cl                  false
% 7.91/1.48  --smt_preprocessing                     true
% 7.91/1.48  --smt_ac_axioms                         fast
% 7.91/1.48  --preprocessed_out                      false
% 7.91/1.48  --preprocessed_stats                    false
% 7.91/1.48  
% 7.91/1.48  ------ Abstraction refinement Options
% 7.91/1.48  
% 7.91/1.48  --abstr_ref                             []
% 7.91/1.48  --abstr_ref_prep                        false
% 7.91/1.48  --abstr_ref_until_sat                   false
% 7.91/1.48  --abstr_ref_sig_restrict                funpre
% 7.91/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.91/1.48  --abstr_ref_under                       []
% 7.91/1.48  
% 7.91/1.48  ------ SAT Options
% 7.91/1.48  
% 7.91/1.48  --sat_mode                              false
% 7.91/1.48  --sat_fm_restart_options                ""
% 7.91/1.48  --sat_gr_def                            false
% 7.91/1.48  --sat_epr_types                         true
% 7.91/1.48  --sat_non_cyclic_types                  false
% 7.91/1.48  --sat_finite_models                     false
% 7.91/1.48  --sat_fm_lemmas                         false
% 7.91/1.48  --sat_fm_prep                           false
% 7.91/1.48  --sat_fm_uc_incr                        true
% 7.91/1.48  --sat_out_model                         small
% 7.91/1.48  --sat_out_clauses                       false
% 7.91/1.48  
% 7.91/1.48  ------ QBF Options
% 7.91/1.48  
% 7.91/1.48  --qbf_mode                              false
% 7.91/1.48  --qbf_elim_univ                         false
% 7.91/1.48  --qbf_dom_inst                          none
% 7.91/1.48  --qbf_dom_pre_inst                      false
% 7.91/1.48  --qbf_sk_in                             false
% 7.91/1.48  --qbf_pred_elim                         true
% 7.91/1.48  --qbf_split                             512
% 7.91/1.48  
% 7.91/1.48  ------ BMC1 Options
% 7.91/1.48  
% 7.91/1.48  --bmc1_incremental                      false
% 7.91/1.48  --bmc1_axioms                           reachable_all
% 7.91/1.48  --bmc1_min_bound                        0
% 7.91/1.48  --bmc1_max_bound                        -1
% 7.91/1.48  --bmc1_max_bound_default                -1
% 7.91/1.48  --bmc1_symbol_reachability              true
% 7.91/1.48  --bmc1_property_lemmas                  false
% 7.91/1.48  --bmc1_k_induction                      false
% 7.91/1.48  --bmc1_non_equiv_states                 false
% 7.91/1.48  --bmc1_deadlock                         false
% 7.91/1.48  --bmc1_ucm                              false
% 7.91/1.48  --bmc1_add_unsat_core                   none
% 7.91/1.48  --bmc1_unsat_core_children              false
% 7.91/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.91/1.48  --bmc1_out_stat                         full
% 7.91/1.48  --bmc1_ground_init                      false
% 7.91/1.48  --bmc1_pre_inst_next_state              false
% 7.91/1.48  --bmc1_pre_inst_state                   false
% 7.91/1.48  --bmc1_pre_inst_reach_state             false
% 7.91/1.48  --bmc1_out_unsat_core                   false
% 7.91/1.48  --bmc1_aig_witness_out                  false
% 7.91/1.48  --bmc1_verbose                          false
% 7.91/1.48  --bmc1_dump_clauses_tptp                false
% 7.91/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.91/1.48  --bmc1_dump_file                        -
% 7.91/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.91/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.91/1.48  --bmc1_ucm_extend_mode                  1
% 7.91/1.48  --bmc1_ucm_init_mode                    2
% 7.91/1.48  --bmc1_ucm_cone_mode                    none
% 7.91/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.91/1.48  --bmc1_ucm_relax_model                  4
% 7.91/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.91/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.91/1.48  --bmc1_ucm_layered_model                none
% 7.91/1.48  --bmc1_ucm_max_lemma_size               10
% 7.91/1.48  
% 7.91/1.48  ------ AIG Options
% 7.91/1.48  
% 7.91/1.48  --aig_mode                              false
% 7.91/1.48  
% 7.91/1.48  ------ Instantiation Options
% 7.91/1.48  
% 7.91/1.48  --instantiation_flag                    true
% 7.91/1.48  --inst_sos_flag                         true
% 7.91/1.48  --inst_sos_phase                        true
% 7.91/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.91/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.91/1.48  --inst_lit_sel_side                     num_symb
% 7.91/1.48  --inst_solver_per_active                1400
% 7.91/1.48  --inst_solver_calls_frac                1.
% 7.91/1.48  --inst_passive_queue_type               priority_queues
% 7.91/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.91/1.48  --inst_passive_queues_freq              [25;2]
% 7.91/1.48  --inst_dismatching                      true
% 7.91/1.48  --inst_eager_unprocessed_to_passive     true
% 7.91/1.48  --inst_prop_sim_given                   true
% 7.91/1.48  --inst_prop_sim_new                     false
% 7.91/1.48  --inst_subs_new                         false
% 7.91/1.48  --inst_eq_res_simp                      false
% 7.91/1.48  --inst_subs_given                       false
% 7.91/1.48  --inst_orphan_elimination               true
% 7.91/1.48  --inst_learning_loop_flag               true
% 7.91/1.48  --inst_learning_start                   3000
% 7.91/1.48  --inst_learning_factor                  2
% 7.91/1.48  --inst_start_prop_sim_after_learn       3
% 7.91/1.48  --inst_sel_renew                        solver
% 7.91/1.48  --inst_lit_activity_flag                true
% 7.91/1.48  --inst_restr_to_given                   false
% 7.91/1.48  --inst_activity_threshold               500
% 7.91/1.48  --inst_out_proof                        true
% 7.91/1.48  
% 7.91/1.48  ------ Resolution Options
% 7.91/1.48  
% 7.91/1.48  --resolution_flag                       true
% 7.91/1.48  --res_lit_sel                           adaptive
% 7.91/1.48  --res_lit_sel_side                      none
% 7.91/1.48  --res_ordering                          kbo
% 7.91/1.48  --res_to_prop_solver                    active
% 7.91/1.48  --res_prop_simpl_new                    false
% 7.91/1.48  --res_prop_simpl_given                  true
% 7.91/1.48  --res_passive_queue_type                priority_queues
% 7.91/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.91/1.48  --res_passive_queues_freq               [15;5]
% 7.91/1.48  --res_forward_subs                      full
% 7.91/1.48  --res_backward_subs                     full
% 7.91/1.48  --res_forward_subs_resolution           true
% 7.91/1.48  --res_backward_subs_resolution          true
% 7.91/1.48  --res_orphan_elimination                true
% 7.91/1.48  --res_time_limit                        2.
% 7.91/1.48  --res_out_proof                         true
% 7.91/1.48  
% 7.91/1.48  ------ Superposition Options
% 7.91/1.48  
% 7.91/1.48  --superposition_flag                    true
% 7.91/1.48  --sup_passive_queue_type                priority_queues
% 7.91/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.91/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.91/1.48  --demod_completeness_check              fast
% 7.91/1.48  --demod_use_ground                      true
% 7.91/1.48  --sup_to_prop_solver                    passive
% 7.91/1.48  --sup_prop_simpl_new                    true
% 7.91/1.48  --sup_prop_simpl_given                  true
% 7.91/1.48  --sup_fun_splitting                     true
% 7.91/1.48  --sup_smt_interval                      50000
% 7.91/1.48  
% 7.91/1.48  ------ Superposition Simplification Setup
% 7.91/1.48  
% 7.91/1.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.91/1.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.91/1.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.91/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.91/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.91/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.91/1.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.91/1.48  --sup_immed_triv                        [TrivRules]
% 7.91/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.91/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.91/1.48  --sup_immed_bw_main                     []
% 7.91/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.91/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.91/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.91/1.48  --sup_input_bw                          []
% 7.91/1.48  
% 7.91/1.48  ------ Combination Options
% 7.91/1.48  
% 7.91/1.48  --comb_res_mult                         3
% 7.91/1.48  --comb_sup_mult                         2
% 7.91/1.48  --comb_inst_mult                        10
% 7.91/1.48  
% 7.91/1.48  ------ Debug Options
% 7.91/1.48  
% 7.91/1.48  --dbg_backtrace                         false
% 7.91/1.48  --dbg_dump_prop_clauses                 false
% 7.91/1.48  --dbg_dump_prop_clauses_file            -
% 7.91/1.48  --dbg_out_stat                          false
% 7.91/1.48  ------ Parsing...
% 7.91/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.91/1.48  
% 7.91/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.91/1.48  
% 7.91/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.91/1.48  
% 7.91/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.91/1.48  ------ Proving...
% 7.91/1.48  ------ Problem Properties 
% 7.91/1.48  
% 7.91/1.48  
% 7.91/1.48  clauses                                 13
% 7.91/1.48  conjectures                             1
% 7.91/1.48  EPR                                     0
% 7.91/1.48  Horn                                    13
% 7.91/1.48  unary                                   6
% 7.91/1.48  binary                                  4
% 7.91/1.48  lits                                    24
% 7.91/1.48  lits eq                                 10
% 7.91/1.48  fd_pure                                 0
% 7.91/1.48  fd_pseudo                               0
% 7.91/1.48  fd_cond                                 0
% 7.91/1.48  fd_pseudo_cond                          0
% 7.91/1.48  AC symbols                              0
% 7.91/1.48  
% 7.91/1.48  ------ Schedule dynamic 5 is on 
% 7.91/1.48  
% 7.91/1.48  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.91/1.48  
% 7.91/1.48  
% 7.91/1.48  ------ 
% 7.91/1.48  Current options:
% 7.91/1.48  ------ 
% 7.91/1.48  
% 7.91/1.48  ------ Input Options
% 7.91/1.48  
% 7.91/1.48  --out_options                           all
% 7.91/1.48  --tptp_safe_out                         true
% 7.91/1.48  --problem_path                          ""
% 7.91/1.48  --include_path                          ""
% 7.91/1.48  --clausifier                            res/vclausify_rel
% 7.91/1.48  --clausifier_options                    ""
% 7.91/1.48  --stdin                                 false
% 7.91/1.48  --stats_out                             all
% 7.91/1.48  
% 7.91/1.48  ------ General Options
% 7.91/1.48  
% 7.91/1.48  --fof                                   false
% 7.91/1.48  --time_out_real                         305.
% 7.91/1.48  --time_out_virtual                      -1.
% 7.91/1.48  --symbol_type_check                     false
% 7.91/1.48  --clausify_out                          false
% 7.91/1.48  --sig_cnt_out                           false
% 7.91/1.48  --trig_cnt_out                          false
% 7.91/1.48  --trig_cnt_out_tolerance                1.
% 7.91/1.48  --trig_cnt_out_sk_spl                   false
% 7.91/1.48  --abstr_cl_out                          false
% 7.91/1.48  
% 7.91/1.48  ------ Global Options
% 7.91/1.48  
% 7.91/1.48  --schedule                              default
% 7.91/1.48  --add_important_lit                     false
% 7.91/1.48  --prop_solver_per_cl                    1000
% 7.91/1.48  --min_unsat_core                        false
% 7.91/1.48  --soft_assumptions                      false
% 7.91/1.48  --soft_lemma_size                       3
% 7.91/1.48  --prop_impl_unit_size                   0
% 7.91/1.48  --prop_impl_unit                        []
% 7.91/1.48  --share_sel_clauses                     true
% 7.91/1.48  --reset_solvers                         false
% 7.91/1.48  --bc_imp_inh                            [conj_cone]
% 7.91/1.48  --conj_cone_tolerance                   3.
% 7.91/1.48  --extra_neg_conj                        none
% 7.91/1.48  --large_theory_mode                     true
% 7.91/1.48  --prolific_symb_bound                   200
% 7.91/1.48  --lt_threshold                          2000
% 7.91/1.48  --clause_weak_htbl                      true
% 7.91/1.48  --gc_record_bc_elim                     false
% 7.91/1.48  
% 7.91/1.48  ------ Preprocessing Options
% 7.91/1.48  
% 7.91/1.48  --preprocessing_flag                    true
% 7.91/1.48  --time_out_prep_mult                    0.1
% 7.91/1.48  --splitting_mode                        input
% 7.91/1.48  --splitting_grd                         true
% 7.91/1.48  --splitting_cvd                         false
% 7.91/1.48  --splitting_cvd_svl                     false
% 7.91/1.48  --splitting_nvd                         32
% 7.91/1.48  --sub_typing                            true
% 7.91/1.48  --prep_gs_sim                           true
% 7.91/1.48  --prep_unflatten                        true
% 7.91/1.48  --prep_res_sim                          true
% 7.91/1.48  --prep_upred                            true
% 7.91/1.48  --prep_sem_filter                       exhaustive
% 7.91/1.48  --prep_sem_filter_out                   false
% 7.91/1.48  --pred_elim                             true
% 7.91/1.48  --res_sim_input                         true
% 7.91/1.48  --eq_ax_congr_red                       true
% 7.91/1.48  --pure_diseq_elim                       true
% 7.91/1.48  --brand_transform                       false
% 7.91/1.48  --non_eq_to_eq                          false
% 7.91/1.48  --prep_def_merge                        true
% 7.91/1.48  --prep_def_merge_prop_impl              false
% 7.91/1.48  --prep_def_merge_mbd                    true
% 7.91/1.48  --prep_def_merge_tr_red                 false
% 7.91/1.48  --prep_def_merge_tr_cl                  false
% 7.91/1.48  --smt_preprocessing                     true
% 7.91/1.48  --smt_ac_axioms                         fast
% 7.91/1.48  --preprocessed_out                      false
% 7.91/1.48  --preprocessed_stats                    false
% 7.91/1.48  
% 7.91/1.48  ------ Abstraction refinement Options
% 7.91/1.48  
% 7.91/1.48  --abstr_ref                             []
% 7.91/1.48  --abstr_ref_prep                        false
% 7.91/1.48  --abstr_ref_until_sat                   false
% 7.91/1.48  --abstr_ref_sig_restrict                funpre
% 7.91/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.91/1.48  --abstr_ref_under                       []
% 7.91/1.48  
% 7.91/1.48  ------ SAT Options
% 7.91/1.48  
% 7.91/1.48  --sat_mode                              false
% 7.91/1.48  --sat_fm_restart_options                ""
% 7.91/1.48  --sat_gr_def                            false
% 7.91/1.48  --sat_epr_types                         true
% 7.91/1.48  --sat_non_cyclic_types                  false
% 7.91/1.48  --sat_finite_models                     false
% 7.91/1.48  --sat_fm_lemmas                         false
% 7.91/1.48  --sat_fm_prep                           false
% 7.91/1.48  --sat_fm_uc_incr                        true
% 7.91/1.48  --sat_out_model                         small
% 7.91/1.48  --sat_out_clauses                       false
% 7.91/1.48  
% 7.91/1.48  ------ QBF Options
% 7.91/1.48  
% 7.91/1.48  --qbf_mode                              false
% 7.91/1.48  --qbf_elim_univ                         false
% 7.91/1.48  --qbf_dom_inst                          none
% 7.91/1.48  --qbf_dom_pre_inst                      false
% 7.91/1.48  --qbf_sk_in                             false
% 7.91/1.48  --qbf_pred_elim                         true
% 7.91/1.48  --qbf_split                             512
% 7.91/1.48  
% 7.91/1.48  ------ BMC1 Options
% 7.91/1.48  
% 7.91/1.48  --bmc1_incremental                      false
% 7.91/1.48  --bmc1_axioms                           reachable_all
% 7.91/1.48  --bmc1_min_bound                        0
% 7.91/1.48  --bmc1_max_bound                        -1
% 7.91/1.48  --bmc1_max_bound_default                -1
% 7.91/1.48  --bmc1_symbol_reachability              true
% 7.91/1.48  --bmc1_property_lemmas                  false
% 7.91/1.48  --bmc1_k_induction                      false
% 7.91/1.48  --bmc1_non_equiv_states                 false
% 7.91/1.48  --bmc1_deadlock                         false
% 7.91/1.48  --bmc1_ucm                              false
% 7.91/1.48  --bmc1_add_unsat_core                   none
% 7.91/1.48  --bmc1_unsat_core_children              false
% 7.91/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.91/1.48  --bmc1_out_stat                         full
% 7.91/1.48  --bmc1_ground_init                      false
% 7.91/1.48  --bmc1_pre_inst_next_state              false
% 7.91/1.48  --bmc1_pre_inst_state                   false
% 7.91/1.48  --bmc1_pre_inst_reach_state             false
% 7.91/1.48  --bmc1_out_unsat_core                   false
% 7.91/1.48  --bmc1_aig_witness_out                  false
% 7.91/1.48  --bmc1_verbose                          false
% 7.91/1.48  --bmc1_dump_clauses_tptp                false
% 7.91/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.91/1.48  --bmc1_dump_file                        -
% 7.91/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.91/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.91/1.48  --bmc1_ucm_extend_mode                  1
% 7.91/1.48  --bmc1_ucm_init_mode                    2
% 7.91/1.48  --bmc1_ucm_cone_mode                    none
% 7.91/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.91/1.48  --bmc1_ucm_relax_model                  4
% 7.91/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.91/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.91/1.48  --bmc1_ucm_layered_model                none
% 7.91/1.48  --bmc1_ucm_max_lemma_size               10
% 7.91/1.48  
% 7.91/1.48  ------ AIG Options
% 7.91/1.48  
% 7.91/1.48  --aig_mode                              false
% 7.91/1.48  
% 7.91/1.48  ------ Instantiation Options
% 7.91/1.48  
% 7.91/1.48  --instantiation_flag                    true
% 7.91/1.48  --inst_sos_flag                         true
% 7.91/1.48  --inst_sos_phase                        true
% 7.91/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.91/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.91/1.48  --inst_lit_sel_side                     none
% 7.91/1.48  --inst_solver_per_active                1400
% 7.91/1.48  --inst_solver_calls_frac                1.
% 7.91/1.48  --inst_passive_queue_type               priority_queues
% 7.91/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.91/1.48  --inst_passive_queues_freq              [25;2]
% 7.91/1.48  --inst_dismatching                      true
% 7.91/1.48  --inst_eager_unprocessed_to_passive     true
% 7.91/1.48  --inst_prop_sim_given                   true
% 7.91/1.48  --inst_prop_sim_new                     false
% 7.91/1.48  --inst_subs_new                         false
% 7.91/1.48  --inst_eq_res_simp                      false
% 7.91/1.48  --inst_subs_given                       false
% 7.91/1.48  --inst_orphan_elimination               true
% 7.91/1.48  --inst_learning_loop_flag               true
% 7.91/1.48  --inst_learning_start                   3000
% 7.91/1.48  --inst_learning_factor                  2
% 7.91/1.48  --inst_start_prop_sim_after_learn       3
% 7.91/1.48  --inst_sel_renew                        solver
% 7.91/1.48  --inst_lit_activity_flag                true
% 7.91/1.48  --inst_restr_to_given                   false
% 7.91/1.48  --inst_activity_threshold               500
% 7.91/1.48  --inst_out_proof                        true
% 7.91/1.48  
% 7.91/1.48  ------ Resolution Options
% 7.91/1.48  
% 7.91/1.48  --resolution_flag                       false
% 7.91/1.48  --res_lit_sel                           adaptive
% 7.91/1.48  --res_lit_sel_side                      none
% 7.91/1.48  --res_ordering                          kbo
% 7.91/1.48  --res_to_prop_solver                    active
% 7.91/1.48  --res_prop_simpl_new                    false
% 7.91/1.48  --res_prop_simpl_given                  true
% 7.91/1.48  --res_passive_queue_type                priority_queues
% 7.91/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.91/1.48  --res_passive_queues_freq               [15;5]
% 7.91/1.48  --res_forward_subs                      full
% 7.91/1.48  --res_backward_subs                     full
% 7.91/1.48  --res_forward_subs_resolution           true
% 7.91/1.48  --res_backward_subs_resolution          true
% 7.91/1.48  --res_orphan_elimination                true
% 7.91/1.48  --res_time_limit                        2.
% 7.91/1.48  --res_out_proof                         true
% 7.91/1.48  
% 7.91/1.48  ------ Superposition Options
% 7.91/1.48  
% 7.91/1.48  --superposition_flag                    true
% 7.91/1.48  --sup_passive_queue_type                priority_queues
% 7.91/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.91/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.91/1.48  --demod_completeness_check              fast
% 7.91/1.48  --demod_use_ground                      true
% 7.91/1.48  --sup_to_prop_solver                    passive
% 7.91/1.48  --sup_prop_simpl_new                    true
% 7.91/1.48  --sup_prop_simpl_given                  true
% 7.91/1.48  --sup_fun_splitting                     true
% 7.91/1.48  --sup_smt_interval                      50000
% 7.91/1.48  
% 7.91/1.48  ------ Superposition Simplification Setup
% 7.91/1.48  
% 7.91/1.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.91/1.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.91/1.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.91/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.91/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.91/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.91/1.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.91/1.48  --sup_immed_triv                        [TrivRules]
% 7.91/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.91/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.91/1.48  --sup_immed_bw_main                     []
% 7.91/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.91/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.91/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.91/1.48  --sup_input_bw                          []
% 7.91/1.48  
% 7.91/1.48  ------ Combination Options
% 7.91/1.48  
% 7.91/1.48  --comb_res_mult                         3
% 7.91/1.48  --comb_sup_mult                         2
% 7.91/1.48  --comb_inst_mult                        10
% 7.91/1.48  
% 7.91/1.48  ------ Debug Options
% 7.91/1.48  
% 7.91/1.48  --dbg_backtrace                         false
% 7.91/1.48  --dbg_dump_prop_clauses                 false
% 7.91/1.48  --dbg_dump_prop_clauses_file            -
% 7.91/1.48  --dbg_out_stat                          false
% 7.91/1.48  
% 7.91/1.48  
% 7.91/1.48  
% 7.91/1.48  
% 7.91/1.48  ------ Proving...
% 7.91/1.48  
% 7.91/1.48  
% 7.91/1.48  % SZS status Theorem for theBenchmark.p
% 7.91/1.48  
% 7.91/1.48   Resolution empty clause
% 7.91/1.48  
% 7.91/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 7.91/1.48  
% 7.91/1.48  fof(f6,axiom,(
% 7.91/1.48    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 7.91/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.91/1.48  
% 7.91/1.48  fof(f33,plain,(
% 7.91/1.48    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 7.91/1.48    inference(cnf_transformation,[],[f6])).
% 7.91/1.48  
% 7.91/1.48  fof(f1,axiom,(
% 7.91/1.48    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 7.91/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.91/1.48  
% 7.91/1.48  fof(f28,plain,(
% 7.91/1.48    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 7.91/1.48    inference(cnf_transformation,[],[f1])).
% 7.91/1.48  
% 7.91/1.48  fof(f4,axiom,(
% 7.91/1.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 7.91/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.91/1.48  
% 7.91/1.48  fof(f31,plain,(
% 7.91/1.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 7.91/1.48    inference(cnf_transformation,[],[f4])).
% 7.91/1.48  
% 7.91/1.48  fof(f3,axiom,(
% 7.91/1.48    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 7.91/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.91/1.48  
% 7.91/1.48  fof(f30,plain,(
% 7.91/1.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 7.91/1.48    inference(cnf_transformation,[],[f3])).
% 7.91/1.48  
% 7.91/1.48  fof(f43,plain,(
% 7.91/1.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 7.91/1.48    inference(definition_unfolding,[],[f31,f30])).
% 7.91/1.48  
% 7.91/1.48  fof(f44,plain,(
% 7.91/1.48    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X0)) )),
% 7.91/1.48    inference(definition_unfolding,[],[f28,f43])).
% 7.91/1.48  
% 7.91/1.48  fof(f8,axiom,(
% 7.91/1.48    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 7.91/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.91/1.48  
% 7.91/1.48  fof(f36,plain,(
% 7.91/1.48    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 7.91/1.48    inference(cnf_transformation,[],[f8])).
% 7.91/1.48  
% 7.91/1.48  fof(f10,axiom,(
% 7.91/1.48    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 7.91/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.91/1.48  
% 7.91/1.48  fof(f20,plain,(
% 7.91/1.48    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.91/1.48    inference(ennf_transformation,[],[f10])).
% 7.91/1.48  
% 7.91/1.48  fof(f21,plain,(
% 7.91/1.48    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 7.91/1.48    inference(flattening,[],[f20])).
% 7.91/1.48  
% 7.91/1.48  fof(f38,plain,(
% 7.91/1.48    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 7.91/1.48    inference(cnf_transformation,[],[f21])).
% 7.91/1.48  
% 7.91/1.48  fof(f13,axiom,(
% 7.91/1.48    ! [X0,X1] : (v1_relat_1(X1) => k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0))),
% 7.91/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.91/1.48  
% 7.91/1.48  fof(f24,plain,(
% 7.91/1.48    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.91/1.48    inference(ennf_transformation,[],[f13])).
% 7.91/1.48  
% 7.91/1.48  fof(f41,plain,(
% 7.91/1.48    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.91/1.48    inference(cnf_transformation,[],[f24])).
% 7.91/1.48  
% 7.91/1.48  fof(f7,axiom,(
% 7.91/1.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2))))),
% 7.91/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.91/1.48  
% 7.91/1.48  fof(f18,plain,(
% 7.91/1.48    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 7.91/1.48    inference(ennf_transformation,[],[f7])).
% 7.91/1.48  
% 7.91/1.48  fof(f34,plain,(
% 7.91/1.48    ( ! [X2,X0,X1] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 7.91/1.48    inference(cnf_transformation,[],[f18])).
% 7.91/1.48  
% 7.91/1.48  fof(f5,axiom,(
% 7.91/1.48    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 7.91/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.91/1.48  
% 7.91/1.48  fof(f16,plain,(
% 7.91/1.48    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 7.91/1.48    inference(ennf_transformation,[],[f5])).
% 7.91/1.48  
% 7.91/1.48  fof(f17,plain,(
% 7.91/1.48    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 7.91/1.48    inference(flattening,[],[f16])).
% 7.91/1.48  
% 7.91/1.48  fof(f32,plain,(
% 7.91/1.48    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 7.91/1.48    inference(cnf_transformation,[],[f17])).
% 7.91/1.48  
% 7.91/1.48  fof(f2,axiom,(
% 7.91/1.48    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 7.91/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.91/1.48  
% 7.91/1.48  fof(f29,plain,(
% 7.91/1.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 7.91/1.48    inference(cnf_transformation,[],[f2])).
% 7.91/1.48  
% 7.91/1.48  fof(f45,plain,(
% 7.91/1.48    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 7.91/1.48    inference(definition_unfolding,[],[f29,f30,f30])).
% 7.91/1.48  
% 7.91/1.48  fof(f12,axiom,(
% 7.91/1.48    ! [X0,X1] : (v1_relat_1(X1) => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)))),
% 7.91/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.91/1.48  
% 7.91/1.48  fof(f23,plain,(
% 7.91/1.48    ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 7.91/1.48    inference(ennf_transformation,[],[f12])).
% 7.91/1.48  
% 7.91/1.48  fof(f40,plain,(
% 7.91/1.48    ( ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 7.91/1.48    inference(cnf_transformation,[],[f23])).
% 7.91/1.48  
% 7.91/1.48  fof(f46,plain,(
% 7.91/1.48    ( ! [X0,X1] : (k1_setfam_1(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),X0)) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 7.91/1.48    inference(definition_unfolding,[],[f40,f43])).
% 7.91/1.48  
% 7.91/1.48  fof(f35,plain,(
% 7.91/1.48    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 7.91/1.48    inference(cnf_transformation,[],[f8])).
% 7.91/1.48  
% 7.91/1.48  fof(f9,axiom,(
% 7.91/1.48    ! [X0] : (v1_relat_1(X0) => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0)),
% 7.91/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.91/1.48  
% 7.91/1.48  fof(f19,plain,(
% 7.91/1.48    ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0))),
% 7.91/1.48    inference(ennf_transformation,[],[f9])).
% 7.91/1.48  
% 7.91/1.48  fof(f37,plain,(
% 7.91/1.48    ( ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0)) )),
% 7.91/1.48    inference(cnf_transformation,[],[f19])).
% 7.91/1.48  
% 7.91/1.48  fof(f11,axiom,(
% 7.91/1.48    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 7.91/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.91/1.48  
% 7.91/1.48  fof(f22,plain,(
% 7.91/1.48    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 7.91/1.48    inference(ennf_transformation,[],[f11])).
% 7.91/1.48  
% 7.91/1.48  fof(f39,plain,(
% 7.91/1.48    ( ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 7.91/1.48    inference(cnf_transformation,[],[f22])).
% 7.91/1.48  
% 7.91/1.48  fof(f14,conjecture,(
% 7.91/1.48    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 7.91/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.91/1.48  
% 7.91/1.48  fof(f15,negated_conjecture,(
% 7.91/1.48    ~! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 7.91/1.48    inference(negated_conjecture,[],[f14])).
% 7.91/1.48  
% 7.91/1.48  fof(f25,plain,(
% 7.91/1.48    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))),
% 7.91/1.48    inference(ennf_transformation,[],[f15])).
% 7.91/1.48  
% 7.91/1.48  fof(f26,plain,(
% 7.91/1.48    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 7.91/1.48    introduced(choice_axiom,[])).
% 7.91/1.48  
% 7.91/1.48  fof(f27,plain,(
% 7.91/1.48    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 7.91/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f26])).
% 7.91/1.48  
% 7.91/1.48  fof(f42,plain,(
% 7.91/1.48    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 7.91/1.48    inference(cnf_transformation,[],[f27])).
% 7.91/1.48  
% 7.91/1.48  fof(f47,plain,(
% 7.91/1.48    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1)))),
% 7.91/1.48    inference(definition_unfolding,[],[f42,f43])).
% 7.91/1.48  
% 7.91/1.48  cnf(c_3,plain,
% 7.91/1.48      ( v1_relat_1(k6_relat_1(X0)) ),
% 7.91/1.48      inference(cnf_transformation,[],[f33]) ).
% 7.91/1.48  
% 7.91/1.48  cnf(c_314,plain,
% 7.91/1.48      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 7.91/1.48      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.91/1.48  
% 7.91/1.48  cnf(c_0,plain,
% 7.91/1.48      ( r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X0) ),
% 7.91/1.48      inference(cnf_transformation,[],[f44]) ).
% 7.91/1.48  
% 7.91/1.48  cnf(c_316,plain,
% 7.91/1.48      ( r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X0) = iProver_top ),
% 7.91/1.48      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.91/1.48  
% 7.91/1.48  cnf(c_5,plain,
% 7.91/1.48      ( k2_relat_1(k6_relat_1(X0)) = X0 ),
% 7.91/1.48      inference(cnf_transformation,[],[f36]) ).
% 7.91/1.48  
% 7.91/1.48  cnf(c_8,plain,
% 7.91/1.48      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 7.91/1.48      | ~ v1_relat_1(X0)
% 7.91/1.48      | k5_relat_1(X0,k6_relat_1(X1)) = X0 ),
% 7.91/1.48      inference(cnf_transformation,[],[f38]) ).
% 7.91/1.48  
% 7.91/1.48  cnf(c_311,plain,
% 7.91/1.48      ( k5_relat_1(X0,k6_relat_1(X1)) = X0
% 7.91/1.48      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 7.91/1.48      | v1_relat_1(X0) != iProver_top ),
% 7.91/1.48      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.91/1.48  
% 7.91/1.48  cnf(c_858,plain,
% 7.91/1.48      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k6_relat_1(X0)
% 7.91/1.48      | r1_tarski(X0,X1) != iProver_top
% 7.91/1.48      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 7.91/1.48      inference(superposition,[status(thm)],[c_5,c_311]) ).
% 7.91/1.48  
% 7.91/1.48  cnf(c_11,plain,
% 7.91/1.48      ( ~ v1_relat_1(X0) | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
% 7.91/1.48      inference(cnf_transformation,[],[f41]) ).
% 7.91/1.48  
% 7.91/1.48  cnf(c_308,plain,
% 7.91/1.48      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
% 7.91/1.48      | v1_relat_1(X1) != iProver_top ),
% 7.91/1.48      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.91/1.48  
% 7.91/1.48  cnf(c_823,plain,
% 7.91/1.48      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
% 7.91/1.48      inference(superposition,[status(thm)],[c_314,c_308]) ).
% 7.91/1.48  
% 7.91/1.48  cnf(c_859,plain,
% 7.91/1.48      ( k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X1)
% 7.91/1.48      | r1_tarski(X1,X0) != iProver_top
% 7.91/1.48      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 7.91/1.48      inference(demodulation,[status(thm)],[c_858,c_823]) ).
% 7.91/1.48  
% 7.91/1.48  cnf(c_1146,plain,
% 7.91/1.48      ( k7_relat_1(k6_relat_1(X0),k1_setfam_1(k1_enumset1(X0,X0,X1))) = k6_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1)))
% 7.91/1.48      | v1_relat_1(k6_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1)))) != iProver_top ),
% 7.91/1.48      inference(superposition,[status(thm)],[c_316,c_859]) ).
% 7.91/1.48  
% 7.91/1.48  cnf(c_4568,plain,
% 7.91/1.48      ( k7_relat_1(k6_relat_1(X0),k1_setfam_1(k1_enumset1(X0,X0,X1))) = k6_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1))) ),
% 7.91/1.48      inference(superposition,[status(thm)],[c_314,c_1146]) ).
% 7.91/1.48  
% 7.91/1.48  cnf(c_4,plain,
% 7.91/1.48      ( ~ v1_relat_1(X0)
% 7.91/1.48      | ~ v1_relat_1(X1)
% 7.91/1.48      | ~ v1_relat_1(X2)
% 7.91/1.48      | k5_relat_1(k5_relat_1(X1,X0),X2) = k5_relat_1(X1,k5_relat_1(X0,X2)) ),
% 7.91/1.48      inference(cnf_transformation,[],[f34]) ).
% 7.91/1.48  
% 7.91/1.48  cnf(c_313,plain,
% 7.91/1.48      ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
% 7.91/1.48      | v1_relat_1(X1) != iProver_top
% 7.91/1.48      | v1_relat_1(X0) != iProver_top
% 7.91/1.48      | v1_relat_1(X2) != iProver_top ),
% 7.91/1.48      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.91/1.48  
% 7.91/1.48  cnf(c_924,plain,
% 7.91/1.48      ( k5_relat_1(k5_relat_1(k6_relat_1(X0),X1),X2) = k5_relat_1(k6_relat_1(X0),k5_relat_1(X1,X2))
% 7.91/1.48      | v1_relat_1(X1) != iProver_top
% 7.91/1.48      | v1_relat_1(X2) != iProver_top ),
% 7.91/1.48      inference(superposition,[status(thm)],[c_314,c_313]) ).
% 7.91/1.48  
% 7.91/1.48  cnf(c_3922,plain,
% 7.91/1.48      ( k5_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),X2) = k5_relat_1(k6_relat_1(X0),k5_relat_1(k6_relat_1(X1),X2))
% 7.91/1.48      | v1_relat_1(X2) != iProver_top ),
% 7.91/1.48      inference(superposition,[status(thm)],[c_314,c_924]) ).
% 7.91/1.48  
% 7.91/1.48  cnf(c_3925,plain,
% 7.91/1.48      ( k5_relat_1(k6_relat_1(X0),k5_relat_1(k6_relat_1(X1),X2)) = k5_relat_1(k7_relat_1(k6_relat_1(X1),X0),X2)
% 7.91/1.48      | v1_relat_1(X2) != iProver_top ),
% 7.91/1.48      inference(light_normalisation,[status(thm)],[c_3922,c_823]) ).
% 7.91/1.48  
% 7.91/1.48  cnf(c_4185,plain,
% 7.91/1.48      ( k5_relat_1(k6_relat_1(X0),k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) = k5_relat_1(k7_relat_1(k6_relat_1(X1),X0),k6_relat_1(X2)) ),
% 7.91/1.48      inference(superposition,[status(thm)],[c_314,c_3925]) ).
% 7.91/1.48  
% 7.91/1.48  cnf(c_2,plain,
% 7.91/1.48      ( ~ v1_relat_1(X0) | ~ v1_relat_1(X1) | v1_relat_1(k5_relat_1(X1,X0)) ),
% 7.91/1.48      inference(cnf_transformation,[],[f32]) ).
% 7.91/1.48  
% 7.91/1.48  cnf(c_315,plain,
% 7.91/1.48      ( v1_relat_1(X0) != iProver_top
% 7.91/1.48      | v1_relat_1(X1) != iProver_top
% 7.91/1.48      | v1_relat_1(k5_relat_1(X1,X0)) = iProver_top ),
% 7.91/1.48      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.91/1.48  
% 7.91/1.48  cnf(c_905,plain,
% 7.91/1.48      ( v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = iProver_top
% 7.91/1.48      | v1_relat_1(k6_relat_1(X0)) != iProver_top
% 7.91/1.48      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 7.91/1.48      inference(superposition,[status(thm)],[c_823,c_315]) ).
% 7.91/1.48  
% 7.91/1.48  cnf(c_33,plain,
% 7.91/1.48      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 7.91/1.48      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.91/1.48  
% 7.91/1.48  cnf(c_1160,plain,
% 7.91/1.48      ( v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = iProver_top
% 7.91/1.48      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 7.91/1.48      inference(global_propositional_subsumption,[status(thm)],[c_905,c_33]) ).
% 7.91/1.48  
% 7.91/1.48  cnf(c_1165,plain,
% 7.91/1.48      ( k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X1),X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X0)
% 7.91/1.48      | v1_relat_1(k6_relat_1(X2)) != iProver_top ),
% 7.91/1.48      inference(superposition,[status(thm)],[c_1160,c_308]) ).
% 7.91/1.48  
% 7.91/1.48  cnf(c_1227,plain,
% 7.91/1.48      ( k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X1),X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X0) ),
% 7.91/1.48      inference(superposition,[status(thm)],[c_314,c_1165]) ).
% 7.91/1.48  
% 7.91/1.48  cnf(c_4189,plain,
% 7.91/1.48      ( k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X0),X1) ),
% 7.91/1.48      inference(demodulation,[status(thm)],[c_4185,c_823,c_1227]) ).
% 7.91/1.48  
% 7.91/1.48  cnf(c_4677,plain,
% 7.91/1.48      ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),k1_setfam_1(k1_enumset1(X1,X1,X2))) = k5_relat_1(k6_relat_1(k1_setfam_1(k1_enumset1(X1,X1,X2))),k6_relat_1(X0)) ),
% 7.91/1.48      inference(superposition,[status(thm)],[c_4568,c_4189]) ).
% 7.91/1.48  
% 7.91/1.48  cnf(c_4805,plain,
% 7.91/1.48      ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),k1_setfam_1(k1_enumset1(X1,X1,X2))) = k7_relat_1(k6_relat_1(X0),k1_setfam_1(k1_enumset1(X1,X1,X2))) ),
% 7.91/1.48      inference(demodulation,[status(thm)],[c_4677,c_823]) ).
% 7.91/1.48  
% 7.91/1.48  cnf(c_1,plain,
% 7.91/1.48      ( k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
% 7.91/1.48      inference(cnf_transformation,[],[f45]) ).
% 7.91/1.48  
% 7.91/1.48  cnf(c_10,plain,
% 7.91/1.48      ( ~ v1_relat_1(X0)
% 7.91/1.48      | k1_setfam_1(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1)) ),
% 7.91/1.48      inference(cnf_transformation,[],[f46]) ).
% 7.91/1.48  
% 7.91/1.48  cnf(c_309,plain,
% 7.91/1.48      ( k1_setfam_1(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1))
% 7.91/1.48      | v1_relat_1(X0) != iProver_top ),
% 7.91/1.48      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.91/1.48  
% 7.91/1.48  cnf(c_543,plain,
% 7.91/1.48      ( k1_setfam_1(k1_enumset1(k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
% 7.91/1.48      inference(superposition,[status(thm)],[c_314,c_309]) ).
% 7.91/1.48  
% 7.91/1.48  cnf(c_6,plain,
% 7.91/1.48      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 7.91/1.48      inference(cnf_transformation,[],[f35]) ).
% 7.91/1.48  
% 7.91/1.48  cnf(c_544,plain,
% 7.91/1.48      ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
% 7.91/1.48      inference(light_normalisation,[status(thm)],[c_543,c_6]) ).
% 7.91/1.48  
% 7.91/1.48  cnf(c_550,plain,
% 7.91/1.48      ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
% 7.91/1.48      inference(superposition,[status(thm)],[c_1,c_544]) ).
% 7.91/1.48  
% 7.91/1.48  cnf(c_7,plain,
% 7.91/1.48      ( ~ v1_relat_1(X0) | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ),
% 7.91/1.48      inference(cnf_transformation,[],[f37]) ).
% 7.91/1.48  
% 7.91/1.48  cnf(c_312,plain,
% 7.91/1.48      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
% 7.91/1.48      | v1_relat_1(X0) != iProver_top ),
% 7.91/1.48      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.91/1.48  
% 7.91/1.48  cnf(c_1168,plain,
% 7.91/1.48      ( k5_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),k7_relat_1(k6_relat_1(X0),X1)) = k7_relat_1(k6_relat_1(X0),X1)
% 7.91/1.48      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 7.91/1.48      inference(superposition,[status(thm)],[c_1160,c_312]) ).
% 7.91/1.48  
% 7.91/1.48  cnf(c_1306,plain,
% 7.91/1.48      ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k7_relat_1(k6_relat_1(X0),X1)
% 7.91/1.48      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 7.91/1.48      inference(demodulation,[status(thm)],[c_1168,c_1227]) ).
% 7.91/1.48  
% 7.91/1.48  cnf(c_1310,plain,
% 7.91/1.48      ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k7_relat_1(k6_relat_1(X0),X1) ),
% 7.91/1.48      inference(superposition,[status(thm)],[c_314,c_1306]) ).
% 7.91/1.48  
% 7.91/1.48  cnf(c_1316,plain,
% 7.91/1.48      ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),k1_setfam_1(k1_enumset1(X1,X1,X0))) = k7_relat_1(k6_relat_1(X0),X1) ),
% 7.91/1.48      inference(superposition,[status(thm)],[c_550,c_1310]) ).
% 7.91/1.48  
% 7.91/1.48  cnf(c_36050,plain,
% 7.91/1.48      ( k7_relat_1(k6_relat_1(X0),k1_setfam_1(k1_enumset1(X1,X1,X0))) = k7_relat_1(k6_relat_1(X0),X1) ),
% 7.91/1.48      inference(superposition,[status(thm)],[c_4805,c_1316]) ).
% 7.91/1.48  
% 7.91/1.48  cnf(c_4666,plain,
% 7.91/1.48      ( k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k6_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1))) ),
% 7.91/1.48      inference(superposition,[status(thm)],[c_544,c_4568]) ).
% 7.91/1.48  
% 7.91/1.48  cnf(c_36255,plain,
% 7.91/1.48      ( k6_relat_1(k1_setfam_1(k1_enumset1(X0,X0,k1_setfam_1(k1_enumset1(X1,X1,X0))))) = k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
% 7.91/1.48      inference(superposition,[status(thm)],[c_36050,c_4666]) ).
% 7.91/1.48  
% 7.91/1.48  cnf(c_614,plain,
% 7.91/1.48      ( k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
% 7.91/1.48      inference(superposition,[status(thm)],[c_550,c_544]) ).
% 7.91/1.48  
% 7.91/1.48  cnf(c_4665,plain,
% 7.91/1.48      ( k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(k6_relat_1(X1),X0))) = k6_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1))) ),
% 7.91/1.48      inference(superposition,[status(thm)],[c_550,c_4568]) ).
% 7.91/1.48  
% 7.91/1.48  cnf(c_4982,plain,
% 7.91/1.48      ( k6_relat_1(k1_setfam_1(k1_enumset1(k1_setfam_1(k1_enumset1(X0,X0,X1)),k1_setfam_1(k1_enumset1(X0,X0,X1)),X0))) = k7_relat_1(k6_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1))),k1_relat_1(k6_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1))))) ),
% 7.91/1.48      inference(superposition,[status(thm)],[c_4568,c_4665]) ).
% 7.91/1.48  
% 7.91/1.48  cnf(c_9,plain,
% 7.91/1.48      ( ~ v1_relat_1(X0) | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ),
% 7.91/1.48      inference(cnf_transformation,[],[f39]) ).
% 7.91/1.48  
% 7.91/1.48  cnf(c_310,plain,
% 7.91/1.48      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
% 7.91/1.48      | v1_relat_1(X0) != iProver_top ),
% 7.91/1.48      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.91/1.48  
% 7.91/1.48  cnf(c_621,plain,
% 7.91/1.48      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(k2_relat_1(k6_relat_1(X0)))) = k6_relat_1(X0) ),
% 7.91/1.48      inference(superposition,[status(thm)],[c_314,c_310]) ).
% 7.91/1.48  
% 7.91/1.48  cnf(c_622,plain,
% 7.91/1.48      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X0)) = k6_relat_1(X0) ),
% 7.91/1.48      inference(light_normalisation,[status(thm)],[c_621,c_5]) ).
% 7.91/1.48  
% 7.91/1.48  cnf(c_826,plain,
% 7.91/1.48      ( k7_relat_1(k6_relat_1(X0),X0) = k6_relat_1(X0) ),
% 7.91/1.48      inference(superposition,[status(thm)],[c_622,c_823]) ).
% 7.91/1.48  
% 7.91/1.48  cnf(c_546,plain,
% 7.91/1.48      ( k1_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(X0)),X1)) = k1_relat_1(k7_relat_1(X0,X1))
% 7.91/1.48      | v1_relat_1(X0) != iProver_top ),
% 7.91/1.48      inference(demodulation,[status(thm)],[c_544,c_309]) ).
% 7.91/1.48  
% 7.91/1.48  cnf(c_1166,plain,
% 7.91/1.48      ( k1_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X2)) = k1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2))
% 7.91/1.48      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 7.91/1.48      inference(superposition,[status(thm)],[c_1160,c_546]) ).
% 7.91/1.48  
% 7.91/1.48  cnf(c_1603,plain,
% 7.91/1.48      ( k1_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X2)) = k1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)) ),
% 7.91/1.48      inference(superposition,[status(thm)],[c_314,c_1166]) ).
% 7.91/1.48  
% 7.91/1.48  cnf(c_1647,plain,
% 7.91/1.48      ( k1_relat_1(k7_relat_1(k6_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1))),X2)) = k1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)) ),
% 7.91/1.48      inference(superposition,[status(thm)],[c_544,c_1603]) ).
% 7.91/1.48  
% 7.91/1.48  cnf(c_2150,plain,
% 7.91/1.48      ( k1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),k1_setfam_1(k1_enumset1(X0,X0,X1)))) = k1_relat_1(k6_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1)))) ),
% 7.91/1.48      inference(superposition,[status(thm)],[c_826,c_1647]) ).
% 7.91/1.48  
% 7.91/1.48  cnf(c_1314,plain,
% 7.91/1.48      ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),k1_setfam_1(k1_enumset1(X0,X0,X1))) = k7_relat_1(k6_relat_1(X0),X1) ),
% 7.91/1.48      inference(superposition,[status(thm)],[c_544,c_1310]) ).
% 7.91/1.48  
% 7.91/1.48  cnf(c_2177,plain,
% 7.91/1.48      ( k1_relat_1(k6_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1)))) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
% 7.91/1.48      inference(light_normalisation,[status(thm)],[c_2150,c_1314]) ).
% 7.91/1.48  
% 7.91/1.48  cnf(c_2286,plain,
% 7.91/1.48      ( k1_relat_1(k6_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1)))) = k1_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
% 7.91/1.48      inference(superposition,[status(thm)],[c_1,c_2177]) ).
% 7.91/1.48  
% 7.91/1.48  cnf(c_908,plain,
% 7.91/1.48      ( k5_relat_1(k6_relat_1(k1_relat_1(k5_relat_1(X0,X1))),k5_relat_1(X0,X1)) = k5_relat_1(X0,X1)
% 7.91/1.48      | v1_relat_1(X1) != iProver_top
% 7.91/1.48      | v1_relat_1(X0) != iProver_top ),
% 7.91/1.48      inference(superposition,[status(thm)],[c_315,c_312]) ).
% 7.91/1.48  
% 7.91/1.48  cnf(c_1855,plain,
% 7.91/1.48      ( k5_relat_1(k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(X0),X1))),k5_relat_1(k6_relat_1(X0),X1)) = k5_relat_1(k6_relat_1(X0),X1)
% 7.91/1.48      | v1_relat_1(X1) != iProver_top ),
% 7.91/1.48      inference(superposition,[status(thm)],[c_314,c_908]) ).
% 7.91/1.48  
% 7.91/1.48  cnf(c_3820,plain,
% 7.91/1.48      ( k5_relat_1(k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)))),k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) ),
% 7.91/1.48      inference(superposition,[status(thm)],[c_314,c_1855]) ).
% 7.91/1.48  
% 7.91/1.48  cnf(c_3823,plain,
% 7.91/1.48      ( k5_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),k7_relat_1(k6_relat_1(X0),X1)) = k7_relat_1(k6_relat_1(X0),X1) ),
% 7.91/1.48      inference(light_normalisation,[status(thm)],[c_3820,c_823]) ).
% 7.91/1.48  
% 7.91/1.48  cnf(c_4035,plain,
% 7.91/1.48      ( k5_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),k7_relat_1(k6_relat_1(X1),X0)) = k7_relat_1(k6_relat_1(X1),X0) ),
% 7.91/1.48      inference(superposition,[status(thm)],[c_614,c_3823]) ).
% 7.91/1.48  
% 7.91/1.48  cnf(c_4710,plain,
% 7.91/1.48      ( k5_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1))),X0))),k6_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1)))) = k7_relat_1(k6_relat_1(X0),k1_setfam_1(k1_enumset1(X0,X0,X1))) ),
% 7.91/1.48      inference(superposition,[status(thm)],[c_4568,c_4035]) ).
% 7.91/1.48  
% 7.91/1.48  cnf(c_4753,plain,
% 7.91/1.48      ( k5_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1))),X0))),k6_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1)))) = k6_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1))) ),
% 7.91/1.48      inference(demodulation,[status(thm)],[c_4710,c_4568]) ).
% 7.91/1.48  
% 7.91/1.48  cnf(c_1649,plain,
% 7.91/1.48      ( k1_relat_1(k7_relat_1(k6_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1))),X2)) = k1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X1),X0),X2)) ),
% 7.91/1.48      inference(superposition,[status(thm)],[c_550,c_1603]) ).
% 7.91/1.48  
% 7.91/1.48  cnf(c_4754,plain,
% 7.91/1.48      ( k7_relat_1(k6_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1))),k1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X1),X0),X0))) = k6_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1))) ),
% 7.91/1.48      inference(demodulation,[status(thm)],[c_4753,c_823,c_1649]) ).
% 7.91/1.48  
% 7.91/1.48  cnf(c_4201,plain,
% 7.91/1.48      ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X1) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
% 7.91/1.48      inference(superposition,[status(thm)],[c_826,c_4189]) ).
% 7.91/1.48  
% 7.91/1.48  cnf(c_4204,plain,
% 7.91/1.48      ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X1) = k7_relat_1(k6_relat_1(X0),X1) ),
% 7.91/1.48      inference(demodulation,[status(thm)],[c_4201,c_823]) ).
% 7.91/1.48  
% 7.91/1.48  cnf(c_4755,plain,
% 7.91/1.48      ( k7_relat_1(k6_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1))),k1_relat_1(k7_relat_1(k6_relat_1(X1),X0))) = k6_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1))) ),
% 7.91/1.48      inference(demodulation,[status(thm)],[c_4754,c_4204]) ).
% 7.91/1.48  
% 7.91/1.48  cnf(c_5116,plain,
% 7.91/1.48      ( k6_relat_1(k1_setfam_1(k1_enumset1(k1_setfam_1(k1_enumset1(X0,X0,X1)),k1_setfam_1(k1_enumset1(X0,X0,X1)),X0))) = k6_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1))) ),
% 7.91/1.48      inference(light_normalisation,[status(thm)],[c_4982,c_2286,c_4755]) ).
% 7.91/1.48  
% 7.91/1.48  cnf(c_2792,plain,
% 7.91/1.48      ( k1_setfam_1(k1_enumset1(X0,X0,k1_setfam_1(k1_enumset1(X1,X1,X2)))) = k1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X2),X1),X0)) ),
% 7.91/1.48      inference(superposition,[status(thm)],[c_1649,c_550]) ).
% 7.91/1.48  
% 7.91/1.48  cnf(c_617,plain,
% 7.91/1.48      ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = k1_setfam_1(k1_enumset1(X1,X1,X0)) ),
% 7.91/1.48      inference(superposition,[status(thm)],[c_550,c_544]) ).
% 7.91/1.48  
% 7.91/1.48  cnf(c_3544,plain,
% 7.91/1.48      ( k1_setfam_1(k1_enumset1(k1_setfam_1(k1_enumset1(X0,X0,X1)),k1_setfam_1(k1_enumset1(X0,X0,X1)),X2)) = k1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X1),X0),X2)) ),
% 7.91/1.48      inference(superposition,[status(thm)],[c_2792,c_617]) ).
% 7.91/1.48  
% 7.91/1.48  cnf(c_5117,plain,
% 7.91/1.48      ( k6_relat_1(k1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X1))) = k6_relat_1(k1_setfam_1(k1_enumset1(X1,X1,X0))) ),
% 7.91/1.48      inference(demodulation,[status(thm)],[c_5116,c_3544]) ).
% 7.91/1.48  
% 7.91/1.48  cnf(c_5118,plain,
% 7.91/1.48      ( k6_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1))) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X1),X0))) ),
% 7.91/1.48      inference(light_normalisation,[status(thm)],[c_5117,c_4204]) ).
% 7.91/1.48  
% 7.91/1.48  cnf(c_5149,plain,
% 7.91/1.48      ( k6_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1))) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
% 7.91/1.48      inference(superposition,[status(thm)],[c_614,c_5118]) ).
% 7.91/1.48  
% 7.91/1.48  cnf(c_6148,plain,
% 7.91/1.48      ( k2_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)))) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
% 7.91/1.48      inference(superposition,[status(thm)],[c_5149,c_5]) ).
% 7.91/1.48  
% 7.91/1.48  cnf(c_36256,plain,
% 7.91/1.48      ( k1_setfam_1(k1_enumset1(X0,X0,k1_setfam_1(k1_enumset1(X1,X1,X0)))) = k2_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)))) ),
% 7.91/1.48      inference(superposition,[status(thm)],[c_36050,c_6148]) ).
% 7.91/1.48  
% 7.91/1.48  cnf(c_36295,plain,
% 7.91/1.48      ( k1_setfam_1(k1_enumset1(X0,X0,k1_setfam_1(k1_enumset1(X1,X1,X0)))) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
% 7.91/1.48      inference(superposition,[status(thm)],[c_36050,c_544]) ).
% 7.91/1.48  
% 7.91/1.48  cnf(c_36487,plain,
% 7.91/1.48      ( k2_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)))) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
% 7.91/1.48      inference(demodulation,[status(thm)],[c_36256,c_36295]) ).
% 7.91/1.48  
% 7.91/1.48  cnf(c_5138,plain,
% 7.91/1.48      ( k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X1),X0))) ),
% 7.91/1.48      inference(superposition,[status(thm)],[c_544,c_5118]) ).
% 7.91/1.48  
% 7.91/1.48  cnf(c_5696,plain,
% 7.91/1.48      ( k2_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)))) = k1_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
% 7.91/1.48      inference(superposition,[status(thm)],[c_5138,c_5]) ).
% 7.91/1.48  
% 7.91/1.48  cnf(c_4708,plain,
% 7.91/1.48      ( k1_setfam_1(k1_enumset1(X0,X0,k1_setfam_1(k1_enumset1(X0,X0,X1)))) = k1_relat_1(k6_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1)))) ),
% 7.91/1.48      inference(superposition,[status(thm)],[c_4568,c_544]) ).
% 7.91/1.48  
% 7.91/1.48  cnf(c_4759,plain,
% 7.91/1.48      ( k1_setfam_1(k1_enumset1(X0,X0,k1_setfam_1(k1_enumset1(X0,X0,X1)))) = k1_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
% 7.91/1.48      inference(light_normalisation,[status(thm)],[c_4708,c_2286]) ).
% 7.91/1.48  
% 7.91/1.48  cnf(c_8017,plain,
% 7.91/1.48      ( k6_relat_1(k1_setfam_1(k1_enumset1(X0,X0,k1_setfam_1(k1_enumset1(X0,X0,X1))))) = k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(k6_relat_1(X1),X0))) ),
% 7.91/1.48      inference(superposition,[status(thm)],[c_4759,c_4568]) ).
% 7.91/1.48  
% 7.91/1.48  cnf(c_8072,plain,
% 7.91/1.48      ( k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(k6_relat_1(X1),X0))) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X1),X0))) ),
% 7.91/1.48      inference(demodulation,[status(thm)],[c_8017,c_4759]) ).
% 7.91/1.48  
% 7.91/1.48  cnf(c_8977,plain,
% 7.91/1.48      ( k7_relat_1(k6_relat_1(X0),k1_setfam_1(k1_enumset1(X1,X1,X0))) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X1),X0))) ),
% 7.91/1.48      inference(superposition,[status(thm)],[c_544,c_8072]) ).
% 7.91/1.48  
% 7.91/1.48  cnf(c_36148,plain,
% 7.91/1.48      ( k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k7_relat_1(k6_relat_1(X1),X0) ),
% 7.91/1.48      inference(demodulation,[status(thm)],[c_36050,c_8977]) ).
% 7.91/1.48  
% 7.91/1.48  cnf(c_36488,plain,
% 7.91/1.48      ( k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k2_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
% 7.91/1.48      inference(light_normalisation,[status(thm)],[c_36487,c_5696,c_36148]) ).
% 7.91/1.48  
% 7.91/1.48  cnf(c_36489,plain,
% 7.91/1.48      ( k1_setfam_1(k1_enumset1(X0,X0,k1_setfam_1(k1_enumset1(X1,X1,X0)))) = k2_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
% 7.91/1.48      inference(demodulation,[status(thm)],[c_36488,c_36295]) ).
% 7.91/1.48  
% 7.91/1.48  cnf(c_5199,plain,
% 7.91/1.48      ( k5_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),k6_relat_1(X2)) = k7_relat_1(k6_relat_1(X2),k1_setfam_1(k1_enumset1(X1,X1,X0))) ),
% 7.91/1.48      inference(superposition,[status(thm)],[c_5118,c_823]) ).
% 7.91/1.48  
% 7.91/1.48  cnf(c_20945,plain,
% 7.91/1.48      ( k7_relat_1(k6_relat_1(X0),k1_setfam_1(k1_enumset1(X1,X1,X2))) = k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(k6_relat_1(X2),X1))) ),
% 7.91/1.48      inference(superposition,[status(thm)],[c_5199,c_823]) ).
% 7.91/1.48  
% 7.91/1.48  cnf(c_36346,plain,
% 7.91/1.48      ( k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k7_relat_1(k6_relat_1(X0),X1) ),
% 7.91/1.48      inference(superposition,[status(thm)],[c_36050,c_20945]) ).
% 7.91/1.48  
% 7.91/1.48  cnf(c_36490,plain,
% 7.91/1.48      ( k7_relat_1(k6_relat_1(X0),k2_relat_1(k7_relat_1(k6_relat_1(X1),X0))) = k7_relat_1(k6_relat_1(X0),X1) ),
% 7.91/1.48      inference(demodulation,[status(thm)],[c_36488,c_36346]) ).
% 7.91/1.48  
% 7.91/1.48  cnf(c_36493,plain,
% 7.91/1.48      ( k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k7_relat_1(k6_relat_1(X1),X0) ),
% 7.91/1.48      inference(demodulation,[status(thm)],[c_36255,c_36488,c_36489,c_36490]) ).
% 7.91/1.48  
% 7.91/1.48  cnf(c_1169,plain,
% 7.91/1.48      ( k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)))) = k7_relat_1(k6_relat_1(X0),X1)
% 7.91/1.48      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 7.91/1.48      inference(superposition,[status(thm)],[c_1160,c_310]) ).
% 7.91/1.48  
% 7.91/1.48  cnf(c_1554,plain,
% 7.91/1.48      ( k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)))) = k7_relat_1(k6_relat_1(X0),X1) ),
% 7.91/1.48      inference(superposition,[status(thm)],[c_314,c_1169]) ).
% 7.91/1.48  
% 7.91/1.48  cnf(c_4203,plain,
% 7.91/1.48      ( k7_relat_1(k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X0),X1) = k7_relat_1(k6_relat_1(X0),X1) ),
% 7.91/1.48      inference(superposition,[status(thm)],[c_4189,c_1554]) ).
% 7.91/1.48  
% 7.91/1.48  cnf(c_36260,plain,
% 7.91/1.48      ( k7_relat_1(k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X0),k1_setfam_1(k1_enumset1(X1,X1,X0))) = k7_relat_1(k6_relat_1(X0),k1_setfam_1(k1_enumset1(X1,X1,X0))) ),
% 7.91/1.48      inference(superposition,[status(thm)],[c_36050,c_4203]) ).
% 7.91/1.48  
% 7.91/1.48  cnf(c_36264,plain,
% 7.91/1.48      ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),k1_setfam_1(k1_enumset1(X2,X2,X1))) = k5_relat_1(k7_relat_1(k6_relat_1(X1),X2),k6_relat_1(X0)) ),
% 7.91/1.48      inference(superposition,[status(thm)],[c_36050,c_4189]) ).
% 7.91/1.48  
% 7.91/1.48  cnf(c_36031,plain,
% 7.91/1.48      ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),k1_setfam_1(k1_enumset1(X2,X2,X1))) = k7_relat_1(k6_relat_1(X0),k1_setfam_1(k1_enumset1(X1,X1,X2))) ),
% 7.91/1.48      inference(superposition,[status(thm)],[c_1,c_4805]) ).
% 7.91/1.48  
% 7.91/1.48  cnf(c_36479,plain,
% 7.91/1.48      ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),k1_setfam_1(k1_enumset1(X2,X2,X1))) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) ),
% 7.91/1.48      inference(demodulation,[status(thm)],[c_36264,c_4189,c_36031]) ).
% 7.91/1.48  
% 7.91/1.48  cnf(c_36484,plain,
% 7.91/1.48      ( k7_relat_1(k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X0),k1_setfam_1(k1_enumset1(X1,X1,X0))) = k7_relat_1(k6_relat_1(X0),X1) ),
% 7.91/1.48      inference(demodulation,[status(thm)],[c_36260,c_36050,c_36479]) ).
% 7.91/1.48  
% 7.91/1.48  cnf(c_36494,plain,
% 7.91/1.48      ( k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X1),k1_setfam_1(k1_enumset1(X0,X0,X1))) = k7_relat_1(k6_relat_1(X1),X0) ),
% 7.91/1.48      inference(demodulation,[status(thm)],[c_36493,c_36484]) ).
% 7.91/1.48  
% 7.91/1.48  cnf(c_36495,plain,
% 7.91/1.48      ( k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X1),X0) ),
% 7.91/1.48      inference(light_normalisation,[status(thm)],[c_36494,c_1314,c_4204]) ).
% 7.91/1.48  
% 7.91/1.48  cnf(c_12,negated_conjecture,
% 7.91/1.48      ( k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))) ),
% 7.91/1.48      inference(cnf_transformation,[],[f47]) ).
% 7.91/1.48  
% 7.91/1.48  cnf(c_443,plain,
% 7.91/1.48      ( k6_relat_1(k1_setfam_1(k1_enumset1(sK1,sK1,sK0))) != k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) ),
% 7.91/1.48      inference(demodulation,[status(thm)],[c_1,c_12]) ).
% 7.91/1.48  
% 7.91/1.48  cnf(c_825,plain,
% 7.91/1.48      ( k6_relat_1(k1_setfam_1(k1_enumset1(sK1,sK1,sK0))) != k7_relat_1(k6_relat_1(sK0),sK1) ),
% 7.91/1.48      inference(demodulation,[status(thm)],[c_823,c_443]) ).
% 7.91/1.48  
% 7.91/1.48  cnf(c_36720,plain,
% 7.91/1.48      ( k6_relat_1(k1_setfam_1(k1_enumset1(sK1,sK1,sK0))) != k7_relat_1(k6_relat_1(sK1),sK0) ),
% 7.91/1.48      inference(demodulation,[status(thm)],[c_36495,c_825]) ).
% 7.91/1.48  
% 7.91/1.48  cnf(c_4673,plain,
% 7.91/1.48      ( k7_relat_1(k6_relat_1(X0),k1_setfam_1(k1_enumset1(X1,X1,X0))) = k6_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1))) ),
% 7.91/1.48      inference(superposition,[status(thm)],[c_1,c_4568]) ).
% 7.91/1.48  
% 7.91/1.48  cnf(c_36149,plain,
% 7.91/1.48      ( k6_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1))) = k7_relat_1(k6_relat_1(X0),X1) ),
% 7.91/1.48      inference(demodulation,[status(thm)],[c_36050,c_4673]) ).
% 7.91/1.48  
% 7.91/1.48  cnf(c_36727,plain,
% 7.91/1.48      ( k7_relat_1(k6_relat_1(sK1),sK0) != k7_relat_1(k6_relat_1(sK1),sK0) ),
% 7.91/1.48      inference(demodulation,[status(thm)],[c_36720,c_36149]) ).
% 7.91/1.48  
% 7.91/1.48  cnf(c_36728,plain,
% 7.91/1.48      ( $false ),
% 7.91/1.48      inference(equality_resolution_simp,[status(thm)],[c_36727]) ).
% 7.91/1.48  
% 7.91/1.48  
% 7.91/1.48  % SZS output end CNFRefutation for theBenchmark.p
% 7.91/1.48  
% 7.91/1.48  ------                               Statistics
% 7.91/1.48  
% 7.91/1.48  ------ General
% 7.91/1.48  
% 7.91/1.48  abstr_ref_over_cycles:                  0
% 7.91/1.48  abstr_ref_under_cycles:                 0
% 7.91/1.48  gc_basic_clause_elim:                   0
% 7.91/1.48  forced_gc_time:                         0
% 7.91/1.48  parsing_time:                           0.009
% 7.91/1.48  unif_index_cands_time:                  0.
% 7.91/1.48  unif_index_add_time:                    0.
% 7.91/1.48  orderings_time:                         0.
% 7.91/1.48  out_proof_time:                         0.01
% 7.91/1.48  total_time:                             0.898
% 7.91/1.48  num_of_symbols:                         42
% 7.91/1.48  num_of_terms:                           34237
% 7.91/1.48  
% 7.91/1.48  ------ Preprocessing
% 7.91/1.48  
% 7.91/1.48  num_of_splits:                          0
% 7.91/1.48  num_of_split_atoms:                     0
% 7.91/1.48  num_of_reused_defs:                     0
% 7.91/1.48  num_eq_ax_congr_red:                    6
% 7.91/1.48  num_of_sem_filtered_clauses:            1
% 7.91/1.48  num_of_subtypes:                        0
% 7.91/1.48  monotx_restored_types:                  0
% 7.91/1.48  sat_num_of_epr_types:                   0
% 7.91/1.48  sat_num_of_non_cyclic_types:            0
% 7.91/1.48  sat_guarded_non_collapsed_types:        0
% 7.91/1.48  num_pure_diseq_elim:                    0
% 7.91/1.48  simp_replaced_by:                       0
% 7.91/1.48  res_preprocessed:                       60
% 7.91/1.48  prep_upred:                             0
% 7.91/1.48  prep_unflattend:                        1
% 7.91/1.48  smt_new_axioms:                         0
% 7.91/1.48  pred_elim_cands:                        2
% 7.91/1.48  pred_elim:                              0
% 7.91/1.48  pred_elim_cl:                           0
% 7.91/1.48  pred_elim_cycles:                       1
% 7.91/1.48  merged_defs:                            0
% 7.91/1.48  merged_defs_ncl:                        0
% 7.91/1.48  bin_hyper_res:                          0
% 7.91/1.48  prep_cycles:                            3
% 7.91/1.48  pred_elim_time:                         0.
% 7.91/1.48  splitting_time:                         0.
% 7.91/1.48  sem_filter_time:                        0.
% 7.91/1.48  monotx_time:                            0.
% 7.91/1.48  subtype_inf_time:                       0.
% 7.91/1.48  
% 7.91/1.48  ------ Problem properties
% 7.91/1.48  
% 7.91/1.48  clauses:                                13
% 7.91/1.48  conjectures:                            1
% 7.91/1.48  epr:                                    0
% 7.91/1.48  horn:                                   13
% 7.91/1.48  ground:                                 1
% 7.91/1.48  unary:                                  6
% 7.91/1.48  binary:                                 4
% 7.91/1.48  lits:                                   24
% 7.91/1.48  lits_eq:                                10
% 7.91/1.48  fd_pure:                                0
% 7.91/1.48  fd_pseudo:                              0
% 7.91/1.48  fd_cond:                                0
% 7.91/1.48  fd_pseudo_cond:                         0
% 7.91/1.48  ac_symbols:                             0
% 7.91/1.48  
% 7.91/1.48  ------ Propositional Solver
% 7.91/1.48  
% 7.91/1.48  prop_solver_calls:                      31
% 7.91/1.48  prop_fast_solver_calls:                 538
% 7.91/1.48  smt_solver_calls:                       0
% 7.91/1.48  smt_fast_solver_calls:                  0
% 7.91/1.48  prop_num_of_clauses:                    5876
% 7.91/1.48  prop_preprocess_simplified:             10373
% 7.91/1.48  prop_fo_subsumed:                       2
% 7.91/1.48  prop_solver_time:                       0.
% 7.91/1.48  smt_solver_time:                        0.
% 7.91/1.48  smt_fast_solver_time:                   0.
% 7.91/1.48  prop_fast_solver_time:                  0.
% 7.91/1.48  prop_unsat_core_time:                   0.
% 7.91/1.48  
% 7.91/1.48  ------ QBF
% 7.91/1.48  
% 7.91/1.48  qbf_q_res:                              0
% 7.91/1.48  qbf_num_tautologies:                    0
% 7.91/1.48  qbf_prep_cycles:                        0
% 7.91/1.48  
% 7.91/1.48  ------ BMC1
% 7.91/1.48  
% 7.91/1.48  bmc1_current_bound:                     -1
% 7.91/1.48  bmc1_last_solved_bound:                 -1
% 7.91/1.48  bmc1_unsat_core_size:                   -1
% 7.91/1.48  bmc1_unsat_core_parents_size:           -1
% 7.91/1.48  bmc1_merge_next_fun:                    0
% 7.91/1.48  bmc1_unsat_core_clauses_time:           0.
% 7.91/1.48  
% 7.91/1.48  ------ Instantiation
% 7.91/1.48  
% 7.91/1.48  inst_num_of_clauses:                    2733
% 7.91/1.48  inst_num_in_passive:                    1637
% 7.91/1.48  inst_num_in_active:                     1037
% 7.91/1.48  inst_num_in_unprocessed:                59
% 7.91/1.48  inst_num_of_loops:                      1090
% 7.91/1.48  inst_num_of_learning_restarts:          0
% 7.91/1.48  inst_num_moves_active_passive:          47
% 7.91/1.48  inst_lit_activity:                      0
% 7.91/1.48  inst_lit_activity_moves:                0
% 7.91/1.48  inst_num_tautologies:                   0
% 7.91/1.48  inst_num_prop_implied:                  0
% 7.91/1.48  inst_num_existing_simplified:           0
% 7.91/1.48  inst_num_eq_res_simplified:             0
% 7.91/1.48  inst_num_child_elim:                    0
% 7.91/1.48  inst_num_of_dismatching_blockings:      790
% 7.91/1.48  inst_num_of_non_proper_insts:           3631
% 7.91/1.48  inst_num_of_duplicates:                 0
% 7.91/1.48  inst_inst_num_from_inst_to_res:         0
% 7.91/1.48  inst_dismatching_checking_time:         0.
% 7.91/1.48  
% 7.91/1.48  ------ Resolution
% 7.91/1.48  
% 7.91/1.48  res_num_of_clauses:                     0
% 7.91/1.48  res_num_in_passive:                     0
% 7.91/1.48  res_num_in_active:                      0
% 7.91/1.48  res_num_of_loops:                       63
% 7.91/1.48  res_forward_subset_subsumed:            684
% 7.91/1.48  res_backward_subset_subsumed:           0
% 7.91/1.48  res_forward_subsumed:                   0
% 7.91/1.48  res_backward_subsumed:                  0
% 7.91/1.48  res_forward_subsumption_resolution:     0
% 7.91/1.48  res_backward_subsumption_resolution:    0
% 7.91/1.48  res_clause_to_clause_subsumption:       8150
% 7.91/1.48  res_orphan_elimination:                 0
% 7.91/1.48  res_tautology_del:                      339
% 7.91/1.48  res_num_eq_res_simplified:              0
% 7.91/1.48  res_num_sel_changes:                    0
% 7.91/1.48  res_moves_from_active_to_pass:          0
% 7.91/1.48  
% 7.91/1.48  ------ Superposition
% 7.91/1.48  
% 7.91/1.48  sup_time_total:                         0.
% 7.91/1.48  sup_time_generating:                    0.
% 7.91/1.48  sup_time_sim_full:                      0.
% 7.91/1.48  sup_time_sim_immed:                     0.
% 7.91/1.48  
% 7.91/1.48  sup_num_of_clauses:                     1029
% 7.91/1.48  sup_num_in_active:                      197
% 7.91/1.48  sup_num_in_passive:                     832
% 7.91/1.48  sup_num_of_loops:                       216
% 7.91/1.48  sup_fw_superposition:                   8781
% 7.91/1.48  sup_bw_superposition:                   7889
% 7.91/1.48  sup_immediate_simplified:               7473
% 7.91/1.48  sup_given_eliminated:                   0
% 7.91/1.48  comparisons_done:                       0
% 7.91/1.48  comparisons_avoided:                    0
% 7.91/1.48  
% 7.91/1.48  ------ Simplifications
% 7.91/1.48  
% 7.91/1.48  
% 7.91/1.48  sim_fw_subset_subsumed:                 2
% 7.91/1.48  sim_bw_subset_subsumed:                 34
% 7.91/1.48  sim_fw_subsumed:                        369
% 7.91/1.48  sim_bw_subsumed:                        13
% 7.91/1.48  sim_fw_subsumption_res:                 0
% 7.91/1.48  sim_bw_subsumption_res:                 0
% 7.91/1.48  sim_tautology_del:                      28
% 7.91/1.48  sim_eq_tautology_del:                   1159
% 7.91/1.48  sim_eq_res_simp:                        0
% 7.91/1.48  sim_fw_demodulated:                     3950
% 7.91/1.48  sim_bw_demodulated:                     37
% 7.91/1.48  sim_light_normalised:                   5630
% 7.91/1.48  sim_joinable_taut:                      0
% 7.91/1.48  sim_joinable_simp:                      0
% 7.91/1.48  sim_ac_normalised:                      0
% 7.91/1.48  sim_smt_subsumption:                    0
% 7.91/1.48  
%------------------------------------------------------------------------------
