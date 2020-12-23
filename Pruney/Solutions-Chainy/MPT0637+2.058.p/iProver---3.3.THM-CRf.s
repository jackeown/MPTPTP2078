%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:50:05 EST 2020

% Result     : Theorem 3.69s
% Output     : CNFRefutation 3.69s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 752 expanded)
%              Number of clauses        :   52 ( 345 expanded)
%              Number of leaves         :   13 ( 161 expanded)
%              Depth                    :   18
%              Number of atoms          :  145 (1092 expanded)
%              Number of equality atoms :  101 ( 684 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    7 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f51,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f36,f35])).

fof(f52,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f34,f51])).

fof(f9,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f5,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k1_enumset1(X0,X0,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f39,f51])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f47,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),X0)) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f48,f51])).

fof(f42,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f16,conjecture,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f16])).

fof(f31,plain,(
    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f17])).

fof(f32,plain,
    ( ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))
   => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f31,f32])).

fof(f50,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f33])).

fof(f55,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))) ),
    inference(definition_unfolding,[],[f50,f51])).

cnf(c_0,plain,
    ( r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_431,plain,
    ( r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_6,plain,
    ( k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_10,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_relat_1(X1)) = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_423,plain,
    ( k5_relat_1(X0,k6_relat_1(X1)) = X0
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1921,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k6_relat_1(X0)
    | r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_423])).

cnf(c_2,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_429,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_13,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_420,plain,
    ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1030,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(superposition,[status(thm)],[c_429,c_420])).

cnf(c_1925,plain,
    ( k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X1)
    | r1_tarski(X1,X0) != iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1921,c_1030])).

cnf(c_11415,plain,
    ( k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X1)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1925,c_429])).

cnf(c_11417,plain,
    ( k7_relat_1(k6_relat_1(X0),k1_setfam_1(k1_enumset1(X0,X0,X1))) = k6_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1))) ),
    inference(superposition,[status(thm)],[c_431,c_11415])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(X0,k1_setfam_1(k1_enumset1(X1,X1,X2))) = k7_relat_1(k7_relat_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_428,plain,
    ( k7_relat_1(X0,k1_setfam_1(k1_enumset1(X1,X1,X2))) = k7_relat_1(k7_relat_1(X0,X1),X2)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1225,plain,
    ( k7_relat_1(k6_relat_1(X0),k1_setfam_1(k1_enumset1(X1,X1,X2))) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) ),
    inference(superposition,[status(thm)],[c_429,c_428])).

cnf(c_11622,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X0),X1) = k6_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1))) ),
    inference(superposition,[status(thm)],[c_11417,c_1225])).

cnf(c_11,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_422,plain,
    ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_604,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(k2_relat_1(k6_relat_1(X0)))) = k6_relat_1(X0) ),
    inference(superposition,[status(thm)],[c_429,c_422])).

cnf(c_605,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X0)) = k6_relat_1(X0) ),
    inference(light_normalisation,[status(thm)],[c_604,c_6])).

cnf(c_1418,plain,
    ( k7_relat_1(k6_relat_1(X0),X0) = k6_relat_1(X0) ),
    inference(superposition,[status(thm)],[c_1030,c_605])).

cnf(c_11682,plain,
    ( k6_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1))) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(light_normalisation,[status(thm)],[c_11622,c_1418])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k9_relat_1(X0,k2_relat_1(X1)) = k2_relat_1(k5_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_427,plain,
    ( k9_relat_1(X0,k2_relat_1(X1)) = k2_relat_1(k5_relat_1(X1,X0))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2055,plain,
    ( k9_relat_1(k6_relat_1(X0),k2_relat_1(X1)) = k2_relat_1(k5_relat_1(X1,k6_relat_1(X0)))
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_429,c_427])).

cnf(c_3617,plain,
    ( k9_relat_1(k6_relat_1(X0),k2_relat_1(k6_relat_1(X1))) = k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))) ),
    inference(superposition,[status(thm)],[c_429,c_2055])).

cnf(c_3619,plain,
    ( k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k9_relat_1(k6_relat_1(X0),X1) ),
    inference(demodulation,[status(thm)],[c_3617,c_6,c_1030])).

cnf(c_11614,plain,
    ( k9_relat_1(k6_relat_1(X0),k1_setfam_1(k1_enumset1(X0,X0,X1))) = k2_relat_1(k6_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1)))) ),
    inference(superposition,[status(thm)],[c_11417,c_3619])).

cnf(c_12,plain,
    ( ~ v1_relat_1(X0)
    | k1_setfam_1(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_421,plain,
    ( k1_setfam_1(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_917,plain,
    ( k1_setfam_1(k1_enumset1(k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(superposition,[status(thm)],[c_429,c_421])).

cnf(c_7,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_918,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(light_normalisation,[status(thm)],[c_917,c_7])).

cnf(c_1817,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1))),X0),X1) = k6_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1))) ),
    inference(superposition,[status(thm)],[c_1225,c_1418])).

cnf(c_3493,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X0),X1) = k6_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1))) ),
    inference(superposition,[status(thm)],[c_918,c_1817])).

cnf(c_1813,plain,
    ( k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(k6_relat_1(X1),X2))) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) ),
    inference(superposition,[status(thm)],[c_918,c_1225])).

cnf(c_2709,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X0),X1) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
    inference(superposition,[status(thm)],[c_1813,c_1418])).

cnf(c_4544,plain,
    ( k6_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1))) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
    inference(superposition,[status(thm)],[c_3493,c_2709])).

cnf(c_5184,plain,
    ( k2_relat_1(k6_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1)))) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(superposition,[status(thm)],[c_4544,c_6])).

cnf(c_11904,plain,
    ( k9_relat_1(k6_relat_1(X0),k1_setfam_1(k1_enumset1(X0,X0,X1))) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(light_normalisation,[status(thm)],[c_11614,c_5184])).

cnf(c_3632,plain,
    ( k9_relat_1(k6_relat_1(X0),k1_setfam_1(k1_enumset1(X1,X1,X2))) = k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)) ),
    inference(superposition,[status(thm)],[c_1225,c_3619])).

cnf(c_12238,plain,
    ( k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X0),X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(superposition,[status(thm)],[c_11904,c_3632])).

cnf(c_12248,plain,
    ( k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k9_relat_1(k6_relat_1(X0),X1) ),
    inference(light_normalisation,[status(thm)],[c_12238,c_1418,c_3619])).

cnf(c_12292,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = k9_relat_1(k6_relat_1(X0),X1) ),
    inference(demodulation,[status(thm)],[c_12248,c_918])).

cnf(c_12770,plain,
    ( k6_relat_1(k9_relat_1(k6_relat_1(X0),X1)) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(light_normalisation,[status(thm)],[c_11682,c_12292])).

cnf(c_14,negated_conjecture,
    ( k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1415,plain,
    ( k6_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))) != k7_relat_1(k6_relat_1(sK0),sK1) ),
    inference(demodulation,[status(thm)],[c_1030,c_14])).

cnf(c_12608,plain,
    ( k6_relat_1(k9_relat_1(k6_relat_1(sK0),sK1)) != k7_relat_1(k6_relat_1(sK0),sK1) ),
    inference(demodulation,[status(thm)],[c_12292,c_1415])).

cnf(c_12774,plain,
    ( k7_relat_1(k6_relat_1(sK0),sK1) != k7_relat_1(k6_relat_1(sK0),sK1) ),
    inference(demodulation,[status(thm)],[c_12770,c_12608])).

cnf(c_12775,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_12774])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n018.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:36:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.69/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.69/0.98  
% 3.69/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.69/0.98  
% 3.69/0.98  ------  iProver source info
% 3.69/0.98  
% 3.69/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.69/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.69/0.98  git: non_committed_changes: false
% 3.69/0.98  git: last_make_outside_of_git: false
% 3.69/0.98  
% 3.69/0.98  ------ 
% 3.69/0.98  
% 3.69/0.98  ------ Input Options
% 3.69/0.98  
% 3.69/0.98  --out_options                           all
% 3.69/0.98  --tptp_safe_out                         true
% 3.69/0.98  --problem_path                          ""
% 3.69/0.98  --include_path                          ""
% 3.69/0.98  --clausifier                            res/vclausify_rel
% 3.69/0.98  --clausifier_options                    --mode clausify
% 3.69/0.98  --stdin                                 false
% 3.69/0.98  --stats_out                             all
% 3.69/0.98  
% 3.69/0.98  ------ General Options
% 3.69/0.98  
% 3.69/0.98  --fof                                   false
% 3.69/0.98  --time_out_real                         305.
% 3.69/0.98  --time_out_virtual                      -1.
% 3.69/0.98  --symbol_type_check                     false
% 3.69/0.98  --clausify_out                          false
% 3.69/0.98  --sig_cnt_out                           false
% 3.69/0.98  --trig_cnt_out                          false
% 3.69/0.98  --trig_cnt_out_tolerance                1.
% 3.69/0.98  --trig_cnt_out_sk_spl                   false
% 3.69/0.98  --abstr_cl_out                          false
% 3.69/0.98  
% 3.69/0.98  ------ Global Options
% 3.69/0.98  
% 3.69/0.98  --schedule                              default
% 3.69/0.98  --add_important_lit                     false
% 3.69/0.98  --prop_solver_per_cl                    1000
% 3.69/0.98  --min_unsat_core                        false
% 3.69/0.98  --soft_assumptions                      false
% 3.69/0.98  --soft_lemma_size                       3
% 3.69/0.98  --prop_impl_unit_size                   0
% 3.69/0.98  --prop_impl_unit                        []
% 3.69/0.98  --share_sel_clauses                     true
% 3.69/0.98  --reset_solvers                         false
% 3.69/0.98  --bc_imp_inh                            [conj_cone]
% 3.69/0.98  --conj_cone_tolerance                   3.
% 3.69/0.98  --extra_neg_conj                        none
% 3.69/0.98  --large_theory_mode                     true
% 3.69/0.98  --prolific_symb_bound                   200
% 3.69/0.98  --lt_threshold                          2000
% 3.69/0.98  --clause_weak_htbl                      true
% 3.69/0.98  --gc_record_bc_elim                     false
% 3.69/0.98  
% 3.69/0.98  ------ Preprocessing Options
% 3.69/0.98  
% 3.69/0.98  --preprocessing_flag                    true
% 3.69/0.98  --time_out_prep_mult                    0.1
% 3.69/0.98  --splitting_mode                        input
% 3.69/0.98  --splitting_grd                         true
% 3.69/0.98  --splitting_cvd                         false
% 3.69/0.98  --splitting_cvd_svl                     false
% 3.69/0.98  --splitting_nvd                         32
% 3.69/0.98  --sub_typing                            true
% 3.69/0.98  --prep_gs_sim                           true
% 3.69/0.98  --prep_unflatten                        true
% 3.69/0.98  --prep_res_sim                          true
% 3.69/0.98  --prep_upred                            true
% 3.69/0.98  --prep_sem_filter                       exhaustive
% 3.69/0.98  --prep_sem_filter_out                   false
% 3.69/0.98  --pred_elim                             true
% 3.69/0.98  --res_sim_input                         true
% 3.69/0.98  --eq_ax_congr_red                       true
% 3.69/0.98  --pure_diseq_elim                       true
% 3.69/0.98  --brand_transform                       false
% 3.69/0.98  --non_eq_to_eq                          false
% 3.69/0.98  --prep_def_merge                        true
% 3.69/0.98  --prep_def_merge_prop_impl              false
% 3.69/0.98  --prep_def_merge_mbd                    true
% 3.69/0.98  --prep_def_merge_tr_red                 false
% 3.69/0.98  --prep_def_merge_tr_cl                  false
% 3.69/0.98  --smt_preprocessing                     true
% 3.69/0.98  --smt_ac_axioms                         fast
% 3.69/0.98  --preprocessed_out                      false
% 3.69/0.98  --preprocessed_stats                    false
% 3.69/0.98  
% 3.69/0.98  ------ Abstraction refinement Options
% 3.69/0.98  
% 3.69/0.98  --abstr_ref                             []
% 3.69/0.98  --abstr_ref_prep                        false
% 3.69/0.98  --abstr_ref_until_sat                   false
% 3.69/0.98  --abstr_ref_sig_restrict                funpre
% 3.69/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.69/0.98  --abstr_ref_under                       []
% 3.69/0.98  
% 3.69/0.98  ------ SAT Options
% 3.69/0.98  
% 3.69/0.98  --sat_mode                              false
% 3.69/0.98  --sat_fm_restart_options                ""
% 3.69/0.98  --sat_gr_def                            false
% 3.69/0.98  --sat_epr_types                         true
% 3.69/0.98  --sat_non_cyclic_types                  false
% 3.69/0.98  --sat_finite_models                     false
% 3.69/0.98  --sat_fm_lemmas                         false
% 3.69/0.98  --sat_fm_prep                           false
% 3.69/0.98  --sat_fm_uc_incr                        true
% 3.69/0.98  --sat_out_model                         small
% 3.69/0.98  --sat_out_clauses                       false
% 3.69/0.98  
% 3.69/0.98  ------ QBF Options
% 3.69/0.98  
% 3.69/0.98  --qbf_mode                              false
% 3.69/0.98  --qbf_elim_univ                         false
% 3.69/0.98  --qbf_dom_inst                          none
% 3.69/0.98  --qbf_dom_pre_inst                      false
% 3.69/0.98  --qbf_sk_in                             false
% 3.69/0.98  --qbf_pred_elim                         true
% 3.69/0.98  --qbf_split                             512
% 3.69/0.98  
% 3.69/0.98  ------ BMC1 Options
% 3.69/0.98  
% 3.69/0.98  --bmc1_incremental                      false
% 3.69/0.98  --bmc1_axioms                           reachable_all
% 3.69/0.98  --bmc1_min_bound                        0
% 3.69/0.98  --bmc1_max_bound                        -1
% 3.69/0.98  --bmc1_max_bound_default                -1
% 3.69/0.98  --bmc1_symbol_reachability              true
% 3.69/0.98  --bmc1_property_lemmas                  false
% 3.69/0.98  --bmc1_k_induction                      false
% 3.69/0.98  --bmc1_non_equiv_states                 false
% 3.69/0.98  --bmc1_deadlock                         false
% 3.69/0.98  --bmc1_ucm                              false
% 3.69/0.98  --bmc1_add_unsat_core                   none
% 3.69/0.98  --bmc1_unsat_core_children              false
% 3.69/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.69/0.98  --bmc1_out_stat                         full
% 3.69/0.98  --bmc1_ground_init                      false
% 3.69/0.98  --bmc1_pre_inst_next_state              false
% 3.69/0.98  --bmc1_pre_inst_state                   false
% 3.69/0.98  --bmc1_pre_inst_reach_state             false
% 3.69/0.98  --bmc1_out_unsat_core                   false
% 3.69/0.98  --bmc1_aig_witness_out                  false
% 3.69/0.98  --bmc1_verbose                          false
% 3.69/0.98  --bmc1_dump_clauses_tptp                false
% 3.69/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.69/0.98  --bmc1_dump_file                        -
% 3.69/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.69/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.69/0.98  --bmc1_ucm_extend_mode                  1
% 3.69/0.98  --bmc1_ucm_init_mode                    2
% 3.69/0.98  --bmc1_ucm_cone_mode                    none
% 3.69/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.69/0.98  --bmc1_ucm_relax_model                  4
% 3.69/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.69/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.69/0.98  --bmc1_ucm_layered_model                none
% 3.69/0.98  --bmc1_ucm_max_lemma_size               10
% 3.69/0.98  
% 3.69/0.98  ------ AIG Options
% 3.69/0.98  
% 3.69/0.98  --aig_mode                              false
% 3.69/0.98  
% 3.69/0.98  ------ Instantiation Options
% 3.69/0.98  
% 3.69/0.98  --instantiation_flag                    true
% 3.69/0.98  --inst_sos_flag                         false
% 3.69/0.98  --inst_sos_phase                        true
% 3.69/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.69/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.69/0.98  --inst_lit_sel_side                     num_symb
% 3.69/0.98  --inst_solver_per_active                1400
% 3.69/0.98  --inst_solver_calls_frac                1.
% 3.69/0.98  --inst_passive_queue_type               priority_queues
% 3.69/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.69/0.98  --inst_passive_queues_freq              [25;2]
% 3.69/0.98  --inst_dismatching                      true
% 3.69/0.98  --inst_eager_unprocessed_to_passive     true
% 3.69/0.98  --inst_prop_sim_given                   true
% 3.69/0.98  --inst_prop_sim_new                     false
% 3.69/0.98  --inst_subs_new                         false
% 3.69/0.98  --inst_eq_res_simp                      false
% 3.69/0.98  --inst_subs_given                       false
% 3.69/0.98  --inst_orphan_elimination               true
% 3.69/0.98  --inst_learning_loop_flag               true
% 3.69/0.98  --inst_learning_start                   3000
% 3.69/0.98  --inst_learning_factor                  2
% 3.69/0.98  --inst_start_prop_sim_after_learn       3
% 3.69/0.98  --inst_sel_renew                        solver
% 3.69/0.98  --inst_lit_activity_flag                true
% 3.69/0.98  --inst_restr_to_given                   false
% 3.69/0.98  --inst_activity_threshold               500
% 3.69/0.98  --inst_out_proof                        true
% 3.69/0.98  
% 3.69/0.98  ------ Resolution Options
% 3.69/0.98  
% 3.69/0.98  --resolution_flag                       true
% 3.69/0.98  --res_lit_sel                           adaptive
% 3.69/0.98  --res_lit_sel_side                      none
% 3.69/0.98  --res_ordering                          kbo
% 3.69/0.98  --res_to_prop_solver                    active
% 3.69/0.98  --res_prop_simpl_new                    false
% 3.69/0.98  --res_prop_simpl_given                  true
% 3.69/0.98  --res_passive_queue_type                priority_queues
% 3.69/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.69/0.98  --res_passive_queues_freq               [15;5]
% 3.69/0.98  --res_forward_subs                      full
% 3.69/0.98  --res_backward_subs                     full
% 3.69/0.98  --res_forward_subs_resolution           true
% 3.69/0.98  --res_backward_subs_resolution          true
% 3.69/0.98  --res_orphan_elimination                true
% 3.69/0.98  --res_time_limit                        2.
% 3.69/0.98  --res_out_proof                         true
% 3.69/0.98  
% 3.69/0.98  ------ Superposition Options
% 3.69/0.98  
% 3.69/0.98  --superposition_flag                    true
% 3.69/0.98  --sup_passive_queue_type                priority_queues
% 3.69/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.69/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.69/0.98  --demod_completeness_check              fast
% 3.69/0.98  --demod_use_ground                      true
% 3.69/0.98  --sup_to_prop_solver                    passive
% 3.69/0.98  --sup_prop_simpl_new                    true
% 3.69/0.98  --sup_prop_simpl_given                  true
% 3.69/0.98  --sup_fun_splitting                     false
% 3.69/0.98  --sup_smt_interval                      50000
% 3.69/0.98  
% 3.69/0.98  ------ Superposition Simplification Setup
% 3.69/0.98  
% 3.69/0.98  --sup_indices_passive                   []
% 3.69/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.69/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.69/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.69/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.69/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.69/0.98  --sup_full_bw                           [BwDemod]
% 3.69/0.98  --sup_immed_triv                        [TrivRules]
% 3.69/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.69/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.69/0.98  --sup_immed_bw_main                     []
% 3.69/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.69/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.69/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.69/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.69/0.98  
% 3.69/0.98  ------ Combination Options
% 3.69/0.98  
% 3.69/0.98  --comb_res_mult                         3
% 3.69/0.98  --comb_sup_mult                         2
% 3.69/0.98  --comb_inst_mult                        10
% 3.69/0.98  
% 3.69/0.98  ------ Debug Options
% 3.69/0.98  
% 3.69/0.98  --dbg_backtrace                         false
% 3.69/0.98  --dbg_dump_prop_clauses                 false
% 3.69/0.98  --dbg_dump_prop_clauses_file            -
% 3.69/0.98  --dbg_out_stat                          false
% 3.69/0.98  ------ Parsing...
% 3.69/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.69/0.98  
% 3.69/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.69/0.98  
% 3.69/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.69/0.98  
% 3.69/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.69/0.98  ------ Proving...
% 3.69/0.98  ------ Problem Properties 
% 3.69/0.98  
% 3.69/0.98  
% 3.69/0.98  clauses                                 15
% 3.69/0.98  conjectures                             1
% 3.69/0.98  EPR                                     0
% 3.69/0.98  Horn                                    15
% 3.69/0.98  unary                                   5
% 3.69/0.98  binary                                  5
% 3.69/0.98  lits                                    31
% 3.69/0.98  lits eq                                 12
% 3.69/0.98  fd_pure                                 0
% 3.69/0.98  fd_pseudo                               0
% 3.69/0.98  fd_cond                                 0
% 3.69/0.98  fd_pseudo_cond                          0
% 3.69/0.98  AC symbols                              0
% 3.69/0.98  
% 3.69/0.98  ------ Schedule dynamic 5 is on 
% 3.69/0.98  
% 3.69/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.69/0.98  
% 3.69/0.98  
% 3.69/0.98  ------ 
% 3.69/0.98  Current options:
% 3.69/0.98  ------ 
% 3.69/0.98  
% 3.69/0.98  ------ Input Options
% 3.69/0.98  
% 3.69/0.98  --out_options                           all
% 3.69/0.98  --tptp_safe_out                         true
% 3.69/0.98  --problem_path                          ""
% 3.69/0.98  --include_path                          ""
% 3.69/0.98  --clausifier                            res/vclausify_rel
% 3.69/0.98  --clausifier_options                    --mode clausify
% 3.69/0.98  --stdin                                 false
% 3.69/0.98  --stats_out                             all
% 3.69/0.98  
% 3.69/0.98  ------ General Options
% 3.69/0.98  
% 3.69/0.98  --fof                                   false
% 3.69/0.98  --time_out_real                         305.
% 3.69/0.98  --time_out_virtual                      -1.
% 3.69/0.98  --symbol_type_check                     false
% 3.69/0.98  --clausify_out                          false
% 3.69/0.98  --sig_cnt_out                           false
% 3.69/0.98  --trig_cnt_out                          false
% 3.69/0.98  --trig_cnt_out_tolerance                1.
% 3.69/0.98  --trig_cnt_out_sk_spl                   false
% 3.69/0.98  --abstr_cl_out                          false
% 3.69/0.98  
% 3.69/0.98  ------ Global Options
% 3.69/0.98  
% 3.69/0.98  --schedule                              default
% 3.69/0.98  --add_important_lit                     false
% 3.69/0.98  --prop_solver_per_cl                    1000
% 3.69/0.98  --min_unsat_core                        false
% 3.69/0.98  --soft_assumptions                      false
% 3.69/0.98  --soft_lemma_size                       3
% 3.69/0.98  --prop_impl_unit_size                   0
% 3.69/0.98  --prop_impl_unit                        []
% 3.69/0.98  --share_sel_clauses                     true
% 3.69/0.98  --reset_solvers                         false
% 3.69/0.98  --bc_imp_inh                            [conj_cone]
% 3.69/0.98  --conj_cone_tolerance                   3.
% 3.69/0.98  --extra_neg_conj                        none
% 3.69/0.98  --large_theory_mode                     true
% 3.69/0.98  --prolific_symb_bound                   200
% 3.69/0.98  --lt_threshold                          2000
% 3.69/0.98  --clause_weak_htbl                      true
% 3.69/0.98  --gc_record_bc_elim                     false
% 3.69/0.98  
% 3.69/0.98  ------ Preprocessing Options
% 3.69/0.98  
% 3.69/0.98  --preprocessing_flag                    true
% 3.69/0.98  --time_out_prep_mult                    0.1
% 3.69/0.98  --splitting_mode                        input
% 3.69/0.98  --splitting_grd                         true
% 3.69/0.98  --splitting_cvd                         false
% 3.69/0.98  --splitting_cvd_svl                     false
% 3.69/0.98  --splitting_nvd                         32
% 3.69/0.98  --sub_typing                            true
% 3.69/0.98  --prep_gs_sim                           true
% 3.69/0.98  --prep_unflatten                        true
% 3.69/0.98  --prep_res_sim                          true
% 3.69/0.98  --prep_upred                            true
% 3.69/0.98  --prep_sem_filter                       exhaustive
% 3.69/0.98  --prep_sem_filter_out                   false
% 3.69/0.98  --pred_elim                             true
% 3.69/0.98  --res_sim_input                         true
% 3.69/0.98  --eq_ax_congr_red                       true
% 3.69/0.98  --pure_diseq_elim                       true
% 3.69/0.98  --brand_transform                       false
% 3.69/0.98  --non_eq_to_eq                          false
% 3.69/0.98  --prep_def_merge                        true
% 3.69/0.98  --prep_def_merge_prop_impl              false
% 3.69/0.98  --prep_def_merge_mbd                    true
% 3.69/0.98  --prep_def_merge_tr_red                 false
% 3.69/0.98  --prep_def_merge_tr_cl                  false
% 3.69/0.98  --smt_preprocessing                     true
% 3.69/0.98  --smt_ac_axioms                         fast
% 3.69/0.98  --preprocessed_out                      false
% 3.69/0.98  --preprocessed_stats                    false
% 3.69/0.98  
% 3.69/0.98  ------ Abstraction refinement Options
% 3.69/0.98  
% 3.69/0.98  --abstr_ref                             []
% 3.69/0.98  --abstr_ref_prep                        false
% 3.69/0.98  --abstr_ref_until_sat                   false
% 3.69/0.98  --abstr_ref_sig_restrict                funpre
% 3.69/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.69/0.98  --abstr_ref_under                       []
% 3.69/0.98  
% 3.69/0.98  ------ SAT Options
% 3.69/0.98  
% 3.69/0.98  --sat_mode                              false
% 3.69/0.98  --sat_fm_restart_options                ""
% 3.69/0.98  --sat_gr_def                            false
% 3.69/0.98  --sat_epr_types                         true
% 3.69/0.98  --sat_non_cyclic_types                  false
% 3.69/0.98  --sat_finite_models                     false
% 3.69/0.98  --sat_fm_lemmas                         false
% 3.69/0.98  --sat_fm_prep                           false
% 3.69/0.98  --sat_fm_uc_incr                        true
% 3.69/0.98  --sat_out_model                         small
% 3.69/0.98  --sat_out_clauses                       false
% 3.69/0.98  
% 3.69/0.98  ------ QBF Options
% 3.69/0.98  
% 3.69/0.98  --qbf_mode                              false
% 3.69/0.98  --qbf_elim_univ                         false
% 3.69/0.98  --qbf_dom_inst                          none
% 3.69/0.98  --qbf_dom_pre_inst                      false
% 3.69/0.98  --qbf_sk_in                             false
% 3.69/0.98  --qbf_pred_elim                         true
% 3.69/0.98  --qbf_split                             512
% 3.69/0.98  
% 3.69/0.98  ------ BMC1 Options
% 3.69/0.98  
% 3.69/0.98  --bmc1_incremental                      false
% 3.69/0.98  --bmc1_axioms                           reachable_all
% 3.69/0.98  --bmc1_min_bound                        0
% 3.69/0.98  --bmc1_max_bound                        -1
% 3.69/0.98  --bmc1_max_bound_default                -1
% 3.69/0.98  --bmc1_symbol_reachability              true
% 3.69/0.98  --bmc1_property_lemmas                  false
% 3.69/0.98  --bmc1_k_induction                      false
% 3.69/0.98  --bmc1_non_equiv_states                 false
% 3.69/0.98  --bmc1_deadlock                         false
% 3.69/0.98  --bmc1_ucm                              false
% 3.69/0.98  --bmc1_add_unsat_core                   none
% 3.69/0.98  --bmc1_unsat_core_children              false
% 3.69/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.69/0.98  --bmc1_out_stat                         full
% 3.69/0.98  --bmc1_ground_init                      false
% 3.69/0.98  --bmc1_pre_inst_next_state              false
% 3.69/0.98  --bmc1_pre_inst_state                   false
% 3.69/0.98  --bmc1_pre_inst_reach_state             false
% 3.69/0.98  --bmc1_out_unsat_core                   false
% 3.69/0.98  --bmc1_aig_witness_out                  false
% 3.69/0.98  --bmc1_verbose                          false
% 3.69/0.98  --bmc1_dump_clauses_tptp                false
% 3.69/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.69/0.98  --bmc1_dump_file                        -
% 3.69/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.69/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.69/0.98  --bmc1_ucm_extend_mode                  1
% 3.69/0.98  --bmc1_ucm_init_mode                    2
% 3.69/0.98  --bmc1_ucm_cone_mode                    none
% 3.69/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.69/0.98  --bmc1_ucm_relax_model                  4
% 3.69/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.69/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.69/0.98  --bmc1_ucm_layered_model                none
% 3.69/0.98  --bmc1_ucm_max_lemma_size               10
% 3.69/0.98  
% 3.69/0.98  ------ AIG Options
% 3.69/0.98  
% 3.69/0.98  --aig_mode                              false
% 3.69/0.98  
% 3.69/0.98  ------ Instantiation Options
% 3.69/0.98  
% 3.69/0.98  --instantiation_flag                    true
% 3.69/0.98  --inst_sos_flag                         false
% 3.69/0.98  --inst_sos_phase                        true
% 3.69/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.69/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.69/0.98  --inst_lit_sel_side                     none
% 3.69/0.98  --inst_solver_per_active                1400
% 3.69/0.98  --inst_solver_calls_frac                1.
% 3.69/0.98  --inst_passive_queue_type               priority_queues
% 3.69/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.69/0.98  --inst_passive_queues_freq              [25;2]
% 3.69/0.98  --inst_dismatching                      true
% 3.69/0.98  --inst_eager_unprocessed_to_passive     true
% 3.69/0.98  --inst_prop_sim_given                   true
% 3.69/0.98  --inst_prop_sim_new                     false
% 3.69/0.98  --inst_subs_new                         false
% 3.69/0.98  --inst_eq_res_simp                      false
% 3.69/0.98  --inst_subs_given                       false
% 3.69/0.98  --inst_orphan_elimination               true
% 3.69/0.98  --inst_learning_loop_flag               true
% 3.69/0.98  --inst_learning_start                   3000
% 3.69/0.98  --inst_learning_factor                  2
% 3.69/0.98  --inst_start_prop_sim_after_learn       3
% 3.69/0.98  --inst_sel_renew                        solver
% 3.69/0.98  --inst_lit_activity_flag                true
% 3.69/0.98  --inst_restr_to_given                   false
% 3.69/0.98  --inst_activity_threshold               500
% 3.69/0.98  --inst_out_proof                        true
% 3.69/0.98  
% 3.69/0.98  ------ Resolution Options
% 3.69/0.98  
% 3.69/0.98  --resolution_flag                       false
% 3.69/0.98  --res_lit_sel                           adaptive
% 3.69/0.98  --res_lit_sel_side                      none
% 3.69/0.98  --res_ordering                          kbo
% 3.69/0.98  --res_to_prop_solver                    active
% 3.69/0.98  --res_prop_simpl_new                    false
% 3.69/0.98  --res_prop_simpl_given                  true
% 3.69/0.98  --res_passive_queue_type                priority_queues
% 3.69/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.69/0.98  --res_passive_queues_freq               [15;5]
% 3.69/0.98  --res_forward_subs                      full
% 3.69/0.98  --res_backward_subs                     full
% 3.69/0.98  --res_forward_subs_resolution           true
% 3.69/0.98  --res_backward_subs_resolution          true
% 3.69/0.98  --res_orphan_elimination                true
% 3.69/0.98  --res_time_limit                        2.
% 3.69/0.98  --res_out_proof                         true
% 3.69/0.98  
% 3.69/0.98  ------ Superposition Options
% 3.69/0.98  
% 3.69/0.98  --superposition_flag                    true
% 3.69/0.98  --sup_passive_queue_type                priority_queues
% 3.69/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.69/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.69/0.98  --demod_completeness_check              fast
% 3.69/0.98  --demod_use_ground                      true
% 3.69/0.98  --sup_to_prop_solver                    passive
% 3.69/0.98  --sup_prop_simpl_new                    true
% 3.69/0.98  --sup_prop_simpl_given                  true
% 3.69/0.98  --sup_fun_splitting                     false
% 3.69/0.98  --sup_smt_interval                      50000
% 3.69/0.98  
% 3.69/0.98  ------ Superposition Simplification Setup
% 3.69/0.98  
% 3.69/0.98  --sup_indices_passive                   []
% 3.69/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.69/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.69/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.69/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.69/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.69/0.98  --sup_full_bw                           [BwDemod]
% 3.69/0.98  --sup_immed_triv                        [TrivRules]
% 3.69/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.69/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.69/0.98  --sup_immed_bw_main                     []
% 3.69/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.69/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.69/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.69/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.69/0.98  
% 3.69/0.98  ------ Combination Options
% 3.69/0.98  
% 3.69/0.98  --comb_res_mult                         3
% 3.69/0.98  --comb_sup_mult                         2
% 3.69/0.98  --comb_inst_mult                        10
% 3.69/0.98  
% 3.69/0.98  ------ Debug Options
% 3.69/0.98  
% 3.69/0.98  --dbg_backtrace                         false
% 3.69/0.98  --dbg_dump_prop_clauses                 false
% 3.69/0.98  --dbg_dump_prop_clauses_file            -
% 3.69/0.98  --dbg_out_stat                          false
% 3.69/0.98  
% 3.69/0.98  
% 3.69/0.98  
% 3.69/0.98  
% 3.69/0.98  ------ Proving...
% 3.69/0.98  
% 3.69/0.98  
% 3.69/0.98  % SZS status Theorem for theBenchmark.p
% 3.69/0.98  
% 3.69/0.98   Resolution empty clause
% 3.69/0.98  
% 3.69/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.69/0.98  
% 3.69/0.98  fof(f1,axiom,(
% 3.69/0.98    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 3.69/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.69/0.98  
% 3.69/0.98  fof(f34,plain,(
% 3.69/0.98    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 3.69/0.98    inference(cnf_transformation,[],[f1])).
% 3.69/0.98  
% 3.69/0.98  fof(f3,axiom,(
% 3.69/0.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.69/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.69/0.98  
% 3.69/0.98  fof(f36,plain,(
% 3.69/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.69/0.98    inference(cnf_transformation,[],[f3])).
% 3.69/0.98  
% 3.69/0.98  fof(f2,axiom,(
% 3.69/0.98    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.69/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.69/0.98  
% 3.69/0.98  fof(f35,plain,(
% 3.69/0.98    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.69/0.98    inference(cnf_transformation,[],[f2])).
% 3.69/0.98  
% 3.69/0.98  fof(f51,plain,(
% 3.69/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 3.69/0.98    inference(definition_unfolding,[],[f36,f35])).
% 3.69/0.98  
% 3.69/0.98  fof(f52,plain,(
% 3.69/0.98    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X0)) )),
% 3.69/0.98    inference(definition_unfolding,[],[f34,f51])).
% 3.69/0.98  
% 3.69/0.98  fof(f9,axiom,(
% 3.69/0.98    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 3.69/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.69/0.98  
% 3.69/0.98  fof(f43,plain,(
% 3.69/0.98    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 3.69/0.98    inference(cnf_transformation,[],[f9])).
% 3.69/0.98  
% 3.69/0.98  fof(f12,axiom,(
% 3.69/0.98    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 3.69/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.69/0.98  
% 3.69/0.98  fof(f26,plain,(
% 3.69/0.98    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.69/0.98    inference(ennf_transformation,[],[f12])).
% 3.69/0.98  
% 3.69/0.98  fof(f27,plain,(
% 3.69/0.98    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 3.69/0.98    inference(flattening,[],[f26])).
% 3.69/0.98  
% 3.69/0.98  fof(f46,plain,(
% 3.69/0.98    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 3.69/0.98    inference(cnf_transformation,[],[f27])).
% 3.69/0.98  
% 3.69/0.98  fof(f5,axiom,(
% 3.69/0.98    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 3.69/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.69/0.98  
% 3.69/0.98  fof(f38,plain,(
% 3.69/0.98    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 3.69/0.98    inference(cnf_transformation,[],[f5])).
% 3.69/0.98  
% 3.69/0.98  fof(f15,axiom,(
% 3.69/0.98    ! [X0,X1] : (v1_relat_1(X1) => k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0))),
% 3.69/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.69/0.98  
% 3.69/0.98  fof(f30,plain,(
% 3.69/0.98    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.69/0.98    inference(ennf_transformation,[],[f15])).
% 3.69/0.98  
% 3.69/0.98  fof(f49,plain,(
% 3.69/0.98    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.69/0.98    inference(cnf_transformation,[],[f30])).
% 3.69/0.98  
% 3.69/0.98  fof(f6,axiom,(
% 3.69/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1))),
% 3.69/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.69/0.98  
% 3.69/0.98  fof(f20,plain,(
% 3.69/0.98    ! [X0,X1,X2] : (k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2))),
% 3.69/0.98    inference(ennf_transformation,[],[f6])).
% 3.69/0.98  
% 3.69/0.98  fof(f39,plain,(
% 3.69/0.98    ( ! [X2,X0,X1] : (k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 3.69/0.98    inference(cnf_transformation,[],[f20])).
% 3.69/0.98  
% 3.69/0.98  fof(f53,plain,(
% 3.69/0.98    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k1_enumset1(X0,X0,X1))) | ~v1_relat_1(X2)) )),
% 3.69/0.98    inference(definition_unfolding,[],[f39,f51])).
% 3.69/0.98  
% 3.69/0.98  fof(f13,axiom,(
% 3.69/0.98    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 3.69/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.69/0.98  
% 3.69/0.98  fof(f28,plain,(
% 3.69/0.98    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 3.69/0.98    inference(ennf_transformation,[],[f13])).
% 3.69/0.98  
% 3.69/0.98  fof(f47,plain,(
% 3.69/0.98    ( ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 3.69/0.98    inference(cnf_transformation,[],[f28])).
% 3.69/0.98  
% 3.69/0.98  fof(f7,axiom,(
% 3.69/0.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 3.69/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.69/0.98  
% 3.69/0.98  fof(f21,plain,(
% 3.69/0.98    ! [X0] : (! [X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.69/0.98    inference(ennf_transformation,[],[f7])).
% 3.69/0.98  
% 3.69/0.98  fof(f40,plain,(
% 3.69/0.98    ( ! [X0,X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.69/0.98    inference(cnf_transformation,[],[f21])).
% 3.69/0.98  
% 3.69/0.98  fof(f14,axiom,(
% 3.69/0.98    ! [X0,X1] : (v1_relat_1(X1) => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)))),
% 3.69/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.69/0.98  
% 3.69/0.98  fof(f29,plain,(
% 3.69/0.98    ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 3.69/0.98    inference(ennf_transformation,[],[f14])).
% 3.69/0.98  
% 3.69/0.98  fof(f48,plain,(
% 3.69/0.98    ( ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 3.69/0.98    inference(cnf_transformation,[],[f29])).
% 3.69/0.98  
% 3.69/0.98  fof(f54,plain,(
% 3.69/0.98    ( ! [X0,X1] : (k1_setfam_1(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),X0)) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 3.69/0.98    inference(definition_unfolding,[],[f48,f51])).
% 3.69/0.98  
% 3.69/0.98  fof(f42,plain,(
% 3.69/0.98    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 3.69/0.98    inference(cnf_transformation,[],[f9])).
% 3.69/0.98  
% 3.69/0.98  fof(f16,conjecture,(
% 3.69/0.98    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 3.69/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.69/0.98  
% 3.69/0.98  fof(f17,negated_conjecture,(
% 3.69/0.98    ~! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 3.69/0.98    inference(negated_conjecture,[],[f16])).
% 3.69/0.98  
% 3.69/0.98  fof(f31,plain,(
% 3.69/0.98    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))),
% 3.69/0.98    inference(ennf_transformation,[],[f17])).
% 3.69/0.98  
% 3.69/0.98  fof(f32,plain,(
% 3.69/0.98    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 3.69/0.98    introduced(choice_axiom,[])).
% 3.69/0.98  
% 3.69/0.98  fof(f33,plain,(
% 3.69/0.98    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 3.69/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f31,f32])).
% 3.69/0.98  
% 3.69/0.98  fof(f50,plain,(
% 3.69/0.98    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 3.69/0.98    inference(cnf_transformation,[],[f33])).
% 3.69/0.98  
% 3.69/0.98  fof(f55,plain,(
% 3.69/0.98    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1)))),
% 3.69/0.98    inference(definition_unfolding,[],[f50,f51])).
% 3.69/0.98  
% 3.69/0.98  cnf(c_0,plain,
% 3.69/0.98      ( r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X0) ),
% 3.69/0.98      inference(cnf_transformation,[],[f52]) ).
% 3.69/0.98  
% 3.69/0.98  cnf(c_431,plain,
% 3.69/0.98      ( r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X0) = iProver_top ),
% 3.69/0.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.69/0.98  
% 3.69/0.98  cnf(c_6,plain,
% 3.69/0.98      ( k2_relat_1(k6_relat_1(X0)) = X0 ),
% 3.69/0.98      inference(cnf_transformation,[],[f43]) ).
% 3.69/0.98  
% 3.69/0.98  cnf(c_10,plain,
% 3.69/0.98      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 3.69/0.98      | ~ v1_relat_1(X0)
% 3.69/0.98      | k5_relat_1(X0,k6_relat_1(X1)) = X0 ),
% 3.69/0.98      inference(cnf_transformation,[],[f46]) ).
% 3.69/0.98  
% 3.69/0.98  cnf(c_423,plain,
% 3.69/0.98      ( k5_relat_1(X0,k6_relat_1(X1)) = X0
% 3.69/0.98      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 3.69/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.69/0.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.69/0.98  
% 3.69/0.98  cnf(c_1921,plain,
% 3.69/0.98      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k6_relat_1(X0)
% 3.69/0.98      | r1_tarski(X0,X1) != iProver_top
% 3.69/0.98      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 3.69/0.98      inference(superposition,[status(thm)],[c_6,c_423]) ).
% 3.69/0.98  
% 3.69/0.98  cnf(c_2,plain,
% 3.69/0.98      ( v1_relat_1(k6_relat_1(X0)) ),
% 3.69/0.98      inference(cnf_transformation,[],[f38]) ).
% 3.69/0.98  
% 3.69/0.98  cnf(c_429,plain,
% 3.69/0.98      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 3.69/0.98      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.69/0.98  
% 3.69/0.98  cnf(c_13,plain,
% 3.69/0.98      ( ~ v1_relat_1(X0) | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
% 3.69/0.98      inference(cnf_transformation,[],[f49]) ).
% 3.69/0.98  
% 3.69/0.98  cnf(c_420,plain,
% 3.69/0.98      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
% 3.69/0.98      | v1_relat_1(X1) != iProver_top ),
% 3.69/0.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.69/0.98  
% 3.69/0.98  cnf(c_1030,plain,
% 3.69/0.98      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
% 3.69/0.98      inference(superposition,[status(thm)],[c_429,c_420]) ).
% 3.69/0.98  
% 3.69/0.98  cnf(c_1925,plain,
% 3.69/0.98      ( k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X1)
% 3.69/0.98      | r1_tarski(X1,X0) != iProver_top
% 3.69/0.98      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 3.69/0.98      inference(demodulation,[status(thm)],[c_1921,c_1030]) ).
% 3.69/0.98  
% 3.69/0.98  cnf(c_11415,plain,
% 3.69/0.98      ( k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X1)
% 3.69/0.98      | r1_tarski(X1,X0) != iProver_top ),
% 3.69/0.98      inference(forward_subsumption_resolution,[status(thm)],[c_1925,c_429]) ).
% 3.69/0.98  
% 3.69/0.98  cnf(c_11417,plain,
% 3.69/0.98      ( k7_relat_1(k6_relat_1(X0),k1_setfam_1(k1_enumset1(X0,X0,X1))) = k6_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1))) ),
% 3.69/0.98      inference(superposition,[status(thm)],[c_431,c_11415]) ).
% 3.69/0.98  
% 3.69/0.98  cnf(c_3,plain,
% 3.69/0.98      ( ~ v1_relat_1(X0)
% 3.69/0.98      | k7_relat_1(X0,k1_setfam_1(k1_enumset1(X1,X1,X2))) = k7_relat_1(k7_relat_1(X0,X1),X2) ),
% 3.69/0.98      inference(cnf_transformation,[],[f53]) ).
% 3.69/0.98  
% 3.69/0.98  cnf(c_428,plain,
% 3.69/0.98      ( k7_relat_1(X0,k1_setfam_1(k1_enumset1(X1,X1,X2))) = k7_relat_1(k7_relat_1(X0,X1),X2)
% 3.69/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.69/0.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.69/0.98  
% 3.69/0.98  cnf(c_1225,plain,
% 3.69/0.98      ( k7_relat_1(k6_relat_1(X0),k1_setfam_1(k1_enumset1(X1,X1,X2))) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) ),
% 3.69/0.98      inference(superposition,[status(thm)],[c_429,c_428]) ).
% 3.69/0.98  
% 3.69/0.98  cnf(c_11622,plain,
% 3.69/0.98      ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X0),X1) = k6_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1))) ),
% 3.69/0.98      inference(superposition,[status(thm)],[c_11417,c_1225]) ).
% 3.69/0.98  
% 3.69/0.98  cnf(c_11,plain,
% 3.69/0.98      ( ~ v1_relat_1(X0) | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ),
% 3.69/0.98      inference(cnf_transformation,[],[f47]) ).
% 3.69/0.98  
% 3.69/0.98  cnf(c_422,plain,
% 3.69/0.98      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
% 3.69/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.69/0.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.69/0.98  
% 3.69/0.98  cnf(c_604,plain,
% 3.69/0.98      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(k2_relat_1(k6_relat_1(X0)))) = k6_relat_1(X0) ),
% 3.69/0.98      inference(superposition,[status(thm)],[c_429,c_422]) ).
% 3.69/0.98  
% 3.69/0.98  cnf(c_605,plain,
% 3.69/0.98      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X0)) = k6_relat_1(X0) ),
% 3.69/0.98      inference(light_normalisation,[status(thm)],[c_604,c_6]) ).
% 3.69/0.98  
% 3.69/0.98  cnf(c_1418,plain,
% 3.69/0.98      ( k7_relat_1(k6_relat_1(X0),X0) = k6_relat_1(X0) ),
% 3.69/0.98      inference(superposition,[status(thm)],[c_1030,c_605]) ).
% 3.69/0.98  
% 3.69/0.98  cnf(c_11682,plain,
% 3.69/0.98      ( k6_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1))) = k7_relat_1(k6_relat_1(X0),X1) ),
% 3.69/0.98      inference(light_normalisation,[status(thm)],[c_11622,c_1418]) ).
% 3.69/0.98  
% 3.69/0.98  cnf(c_4,plain,
% 3.69/0.98      ( ~ v1_relat_1(X0)
% 3.69/0.98      | ~ v1_relat_1(X1)
% 3.69/0.98      | k9_relat_1(X0,k2_relat_1(X1)) = k2_relat_1(k5_relat_1(X1,X0)) ),
% 3.69/0.98      inference(cnf_transformation,[],[f40]) ).
% 3.69/0.98  
% 3.69/0.98  cnf(c_427,plain,
% 3.69/0.98      ( k9_relat_1(X0,k2_relat_1(X1)) = k2_relat_1(k5_relat_1(X1,X0))
% 3.69/0.98      | v1_relat_1(X0) != iProver_top
% 3.69/0.98      | v1_relat_1(X1) != iProver_top ),
% 3.69/0.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.69/0.98  
% 3.69/0.98  cnf(c_2055,plain,
% 3.69/0.98      ( k9_relat_1(k6_relat_1(X0),k2_relat_1(X1)) = k2_relat_1(k5_relat_1(X1,k6_relat_1(X0)))
% 3.69/0.98      | v1_relat_1(X1) != iProver_top ),
% 3.69/0.98      inference(superposition,[status(thm)],[c_429,c_427]) ).
% 3.69/0.98  
% 3.69/0.98  cnf(c_3617,plain,
% 3.69/0.98      ( k9_relat_1(k6_relat_1(X0),k2_relat_1(k6_relat_1(X1))) = k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))) ),
% 3.69/0.98      inference(superposition,[status(thm)],[c_429,c_2055]) ).
% 3.69/0.98  
% 3.69/0.98  cnf(c_3619,plain,
% 3.69/0.98      ( k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k9_relat_1(k6_relat_1(X0),X1) ),
% 3.69/0.98      inference(demodulation,[status(thm)],[c_3617,c_6,c_1030]) ).
% 3.69/0.98  
% 3.69/0.98  cnf(c_11614,plain,
% 3.69/0.98      ( k9_relat_1(k6_relat_1(X0),k1_setfam_1(k1_enumset1(X0,X0,X1))) = k2_relat_1(k6_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1)))) ),
% 3.69/0.98      inference(superposition,[status(thm)],[c_11417,c_3619]) ).
% 3.69/0.98  
% 3.69/0.98  cnf(c_12,plain,
% 3.69/0.98      ( ~ v1_relat_1(X0)
% 3.69/0.98      | k1_setfam_1(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1)) ),
% 3.69/0.98      inference(cnf_transformation,[],[f54]) ).
% 3.69/0.98  
% 3.69/0.98  cnf(c_421,plain,
% 3.69/0.98      ( k1_setfam_1(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1))
% 3.69/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.69/0.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.69/0.98  
% 3.69/0.98  cnf(c_917,plain,
% 3.69/0.98      ( k1_setfam_1(k1_enumset1(k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
% 3.69/0.98      inference(superposition,[status(thm)],[c_429,c_421]) ).
% 3.69/0.98  
% 3.69/0.98  cnf(c_7,plain,
% 3.69/0.98      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 3.69/0.98      inference(cnf_transformation,[],[f42]) ).
% 3.69/0.98  
% 3.69/0.98  cnf(c_918,plain,
% 3.69/0.98      ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
% 3.69/0.98      inference(light_normalisation,[status(thm)],[c_917,c_7]) ).
% 3.69/0.98  
% 3.69/0.98  cnf(c_1817,plain,
% 3.69/0.98      ( k7_relat_1(k7_relat_1(k6_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1))),X0),X1) = k6_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1))) ),
% 3.69/0.98      inference(superposition,[status(thm)],[c_1225,c_1418]) ).
% 3.69/0.98  
% 3.69/0.98  cnf(c_3493,plain,
% 3.69/0.98      ( k7_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X0),X1) = k6_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1))) ),
% 3.69/0.98      inference(superposition,[status(thm)],[c_918,c_1817]) ).
% 3.69/0.98  
% 3.69/0.98  cnf(c_1813,plain,
% 3.69/0.98      ( k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(k6_relat_1(X1),X2))) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) ),
% 3.69/0.98      inference(superposition,[status(thm)],[c_918,c_1225]) ).
% 3.69/0.98  
% 3.69/0.98  cnf(c_2709,plain,
% 3.69/0.98      ( k7_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X0),X1) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
% 3.69/0.98      inference(superposition,[status(thm)],[c_1813,c_1418]) ).
% 3.69/0.98  
% 3.69/0.98  cnf(c_4544,plain,
% 3.69/0.98      ( k6_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1))) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
% 3.69/0.98      inference(superposition,[status(thm)],[c_3493,c_2709]) ).
% 3.69/0.98  
% 3.69/0.98  cnf(c_5184,plain,
% 3.69/0.98      ( k2_relat_1(k6_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1)))) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
% 3.69/0.98      inference(superposition,[status(thm)],[c_4544,c_6]) ).
% 3.69/0.98  
% 3.69/0.98  cnf(c_11904,plain,
% 3.69/0.98      ( k9_relat_1(k6_relat_1(X0),k1_setfam_1(k1_enumset1(X0,X0,X1))) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
% 3.69/0.98      inference(light_normalisation,[status(thm)],[c_11614,c_5184]) ).
% 3.69/0.98  
% 3.69/0.98  cnf(c_3632,plain,
% 3.69/0.98      ( k9_relat_1(k6_relat_1(X0),k1_setfam_1(k1_enumset1(X1,X1,X2))) = k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)) ),
% 3.69/0.98      inference(superposition,[status(thm)],[c_1225,c_3619]) ).
% 3.69/0.98  
% 3.69/0.98  cnf(c_12238,plain,
% 3.69/0.98      ( k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X0),X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
% 3.69/0.98      inference(superposition,[status(thm)],[c_11904,c_3632]) ).
% 3.69/0.98  
% 3.69/0.98  cnf(c_12248,plain,
% 3.69/0.98      ( k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k9_relat_1(k6_relat_1(X0),X1) ),
% 3.69/0.98      inference(light_normalisation,[status(thm)],[c_12238,c_1418,c_3619]) ).
% 3.69/0.98  
% 3.69/0.98  cnf(c_12292,plain,
% 3.69/0.98      ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = k9_relat_1(k6_relat_1(X0),X1) ),
% 3.69/0.98      inference(demodulation,[status(thm)],[c_12248,c_918]) ).
% 3.69/0.98  
% 3.69/0.98  cnf(c_12770,plain,
% 3.69/0.98      ( k6_relat_1(k9_relat_1(k6_relat_1(X0),X1)) = k7_relat_1(k6_relat_1(X0),X1) ),
% 3.69/0.98      inference(light_normalisation,[status(thm)],[c_11682,c_12292]) ).
% 3.69/0.98  
% 3.69/0.98  cnf(c_14,negated_conjecture,
% 3.69/0.98      ( k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))) ),
% 3.69/0.98      inference(cnf_transformation,[],[f55]) ).
% 3.69/0.98  
% 3.69/0.98  cnf(c_1415,plain,
% 3.69/0.98      ( k6_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))) != k7_relat_1(k6_relat_1(sK0),sK1) ),
% 3.69/0.98      inference(demodulation,[status(thm)],[c_1030,c_14]) ).
% 3.69/0.98  
% 3.69/0.98  cnf(c_12608,plain,
% 3.69/0.98      ( k6_relat_1(k9_relat_1(k6_relat_1(sK0),sK1)) != k7_relat_1(k6_relat_1(sK0),sK1) ),
% 3.69/0.98      inference(demodulation,[status(thm)],[c_12292,c_1415]) ).
% 3.69/0.98  
% 3.69/0.98  cnf(c_12774,plain,
% 3.69/0.98      ( k7_relat_1(k6_relat_1(sK0),sK1) != k7_relat_1(k6_relat_1(sK0),sK1) ),
% 3.69/0.98      inference(demodulation,[status(thm)],[c_12770,c_12608]) ).
% 3.69/0.98  
% 3.69/0.98  cnf(c_12775,plain,
% 3.69/0.98      ( $false ),
% 3.69/0.98      inference(equality_resolution_simp,[status(thm)],[c_12774]) ).
% 3.69/0.98  
% 3.69/0.98  
% 3.69/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.69/0.98  
% 3.69/0.98  ------                               Statistics
% 3.69/0.98  
% 3.69/0.98  ------ General
% 3.69/0.98  
% 3.69/0.98  abstr_ref_over_cycles:                  0
% 3.69/0.98  abstr_ref_under_cycles:                 0
% 3.69/0.98  gc_basic_clause_elim:                   0
% 3.69/0.98  forced_gc_time:                         0
% 3.69/0.98  parsing_time:                           0.009
% 3.69/0.98  unif_index_cands_time:                  0.
% 3.69/0.98  unif_index_add_time:                    0.
% 3.69/0.98  orderings_time:                         0.
% 3.69/0.98  out_proof_time:                         0.007
% 3.69/0.98  total_time:                             0.368
% 3.69/0.98  num_of_symbols:                         43
% 3.69/0.98  num_of_terms:                           17466
% 3.69/0.98  
% 3.69/0.98  ------ Preprocessing
% 3.69/0.98  
% 3.69/0.98  num_of_splits:                          0
% 3.69/0.98  num_of_split_atoms:                     0
% 3.69/0.98  num_of_reused_defs:                     0
% 3.69/0.98  num_eq_ax_congr_red:                    4
% 3.69/0.98  num_of_sem_filtered_clauses:            1
% 3.69/0.98  num_of_subtypes:                        0
% 3.69/0.98  monotx_restored_types:                  0
% 3.69/0.98  sat_num_of_epr_types:                   0
% 3.69/0.98  sat_num_of_non_cyclic_types:            0
% 3.69/0.98  sat_guarded_non_collapsed_types:        0
% 3.69/0.98  num_pure_diseq_elim:                    0
% 3.69/0.98  simp_replaced_by:                       0
% 3.69/0.98  res_preprocessed:                       70
% 3.69/0.98  prep_upred:                             0
% 3.69/0.98  prep_unflattend:                        2
% 3.69/0.98  smt_new_axioms:                         0
% 3.69/0.98  pred_elim_cands:                        2
% 3.69/0.98  pred_elim:                              0
% 3.69/0.98  pred_elim_cl:                           0
% 3.69/0.98  pred_elim_cycles:                       1
% 3.69/0.98  merged_defs:                            0
% 3.69/0.98  merged_defs_ncl:                        0
% 3.69/0.98  bin_hyper_res:                          0
% 3.69/0.98  prep_cycles:                            3
% 3.69/0.98  pred_elim_time:                         0.
% 3.69/0.98  splitting_time:                         0.
% 3.69/0.98  sem_filter_time:                        0.
% 3.69/0.98  monotx_time:                            0.
% 3.69/0.98  subtype_inf_time:                       0.
% 3.69/0.98  
% 3.69/0.98  ------ Problem properties
% 3.69/0.98  
% 3.69/0.98  clauses:                                15
% 3.69/0.98  conjectures:                            1
% 3.69/0.98  epr:                                    0
% 3.69/0.98  horn:                                   15
% 3.69/0.98  ground:                                 1
% 3.69/0.98  unary:                                  5
% 3.69/0.98  binary:                                 5
% 3.69/0.98  lits:                                   31
% 3.69/0.98  lits_eq:                                12
% 3.69/0.98  fd_pure:                                0
% 3.69/0.98  fd_pseudo:                              0
% 3.69/0.98  fd_cond:                                0
% 3.69/0.98  fd_pseudo_cond:                         0
% 3.69/0.98  ac_symbols:                             0
% 3.69/0.98  
% 3.69/0.98  ------ Propositional Solver
% 3.69/0.98  
% 3.69/0.98  prop_solver_calls:                      25
% 3.69/0.98  prop_fast_solver_calls:                 460
% 3.69/0.98  smt_solver_calls:                       0
% 3.69/0.98  smt_fast_solver_calls:                  0
% 3.69/0.98  prop_num_of_clauses:                    4783
% 3.69/0.98  prop_preprocess_simplified:             9187
% 3.69/0.98  prop_fo_subsumed:                       1
% 3.69/0.98  prop_solver_time:                       0.
% 3.69/0.98  smt_solver_time:                        0.
% 3.69/0.98  smt_fast_solver_time:                   0.
% 3.69/0.98  prop_fast_solver_time:                  0.
% 3.69/0.98  prop_unsat_core_time:                   0.
% 3.69/0.98  
% 3.69/0.98  ------ QBF
% 3.69/0.98  
% 3.69/0.98  qbf_q_res:                              0
% 3.69/0.98  qbf_num_tautologies:                    0
% 3.69/0.98  qbf_prep_cycles:                        0
% 3.69/0.98  
% 3.69/0.98  ------ BMC1
% 3.69/0.98  
% 3.69/0.98  bmc1_current_bound:                     -1
% 3.69/0.98  bmc1_last_solved_bound:                 -1
% 3.69/0.98  bmc1_unsat_core_size:                   -1
% 3.69/0.98  bmc1_unsat_core_parents_size:           -1
% 3.69/0.98  bmc1_merge_next_fun:                    0
% 3.69/0.98  bmc1_unsat_core_clauses_time:           0.
% 3.69/0.98  
% 3.69/0.98  ------ Instantiation
% 3.69/0.98  
% 3.69/0.98  inst_num_of_clauses:                    1509
% 3.69/0.98  inst_num_in_passive:                    490
% 3.69/0.98  inst_num_in_active:                     496
% 3.69/0.98  inst_num_in_unprocessed:                524
% 3.69/0.98  inst_num_of_loops:                      530
% 3.69/0.98  inst_num_of_learning_restarts:          0
% 3.69/0.98  inst_num_moves_active_passive:          32
% 3.69/0.98  inst_lit_activity:                      0
% 3.69/0.98  inst_lit_activity_moves:                1
% 3.69/0.98  inst_num_tautologies:                   0
% 3.69/0.98  inst_num_prop_implied:                  0
% 3.69/0.98  inst_num_existing_simplified:           0
% 3.69/0.98  inst_num_eq_res_simplified:             0
% 3.69/0.98  inst_num_child_elim:                    0
% 3.69/0.98  inst_num_of_dismatching_blockings:      523
% 3.69/0.98  inst_num_of_non_proper_insts:           1059
% 3.69/0.98  inst_num_of_duplicates:                 0
% 3.69/0.98  inst_inst_num_from_inst_to_res:         0
% 3.69/0.98  inst_dismatching_checking_time:         0.
% 3.69/0.98  
% 3.69/0.98  ------ Resolution
% 3.69/0.98  
% 3.69/0.98  res_num_of_clauses:                     0
% 3.69/0.98  res_num_in_passive:                     0
% 3.69/0.98  res_num_in_active:                      0
% 3.69/0.98  res_num_of_loops:                       73
% 3.69/0.98  res_forward_subset_subsumed:            166
% 3.69/0.98  res_backward_subset_subsumed:           6
% 3.69/0.98  res_forward_subsumed:                   0
% 3.69/0.98  res_backward_subsumed:                  0
% 3.69/0.98  res_forward_subsumption_resolution:     0
% 3.69/0.98  res_backward_subsumption_resolution:    0
% 3.69/0.98  res_clause_to_clause_subsumption:       1739
% 3.69/0.98  res_orphan_elimination:                 0
% 3.69/0.98  res_tautology_del:                      105
% 3.69/0.98  res_num_eq_res_simplified:              0
% 3.69/0.98  res_num_sel_changes:                    0
% 3.69/0.98  res_moves_from_active_to_pass:          0
% 3.69/0.98  
% 3.69/0.98  ------ Superposition
% 3.69/0.98  
% 3.69/0.98  sup_time_total:                         0.
% 3.69/0.98  sup_time_generating:                    0.
% 3.69/0.98  sup_time_sim_full:                      0.
% 3.69/0.98  sup_time_sim_immed:                     0.
% 3.69/0.98  
% 3.69/0.98  sup_num_of_clauses:                     375
% 3.69/0.98  sup_num_in_active:                      44
% 3.69/0.98  sup_num_in_passive:                     331
% 3.69/0.98  sup_num_of_loops:                       105
% 3.69/0.98  sup_fw_superposition:                   1004
% 3.69/0.98  sup_bw_superposition:                   644
% 3.69/0.98  sup_immediate_simplified:               828
% 3.69/0.98  sup_given_eliminated:                   2
% 3.69/0.98  comparisons_done:                       0
% 3.69/0.98  comparisons_avoided:                    0
% 3.69/0.98  
% 3.69/0.98  ------ Simplifications
% 3.69/0.98  
% 3.69/0.98  
% 3.69/0.98  sim_fw_subset_subsumed:                 0
% 3.69/0.98  sim_bw_subset_subsumed:                 5
% 3.69/0.98  sim_fw_subsumed:                        158
% 3.69/0.98  sim_bw_subsumed:                        0
% 3.69/0.98  sim_fw_subsumption_res:                 2
% 3.69/0.98  sim_bw_subsumption_res:                 0
% 3.69/0.98  sim_tautology_del:                      3
% 3.69/0.98  sim_eq_tautology_del:                   173
% 3.69/0.98  sim_eq_res_simp:                        0
% 3.69/0.98  sim_fw_demodulated:                     344
% 3.69/0.98  sim_bw_demodulated:                     103
% 3.69/0.98  sim_light_normalised:                   505
% 3.69/0.98  sim_joinable_taut:                      0
% 3.69/0.98  sim_joinable_simp:                      0
% 3.69/0.98  sim_ac_normalised:                      0
% 3.69/0.98  sim_smt_subsumption:                    0
% 3.69/0.98  
%------------------------------------------------------------------------------
