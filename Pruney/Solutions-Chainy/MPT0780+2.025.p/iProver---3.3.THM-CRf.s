%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:54:26 EST 2020

% Result     : Theorem 3.89s
% Output     : CNFRefutation 3.89s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 208 expanded)
%              Number of clauses        :   48 (  81 expanded)
%              Number of leaves         :   15 (  42 expanded)
%              Depth                    :   18
%              Number of atoms          :  177 ( 390 expanded)
%              Number of equality atoms :  103 ( 210 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k2_wellord1(X2,X0) = k2_wellord1(k2_wellord1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => k2_wellord1(X2,X0) = k2_wellord1(k2_wellord1(X2,X1),X0) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f29,plain,(
    ? [X0,X1,X2] :
      ( k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f30,plain,(
    ? [X0,X1,X2] :
      ( k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f29])).

fof(f33,plain,
    ( ? [X0,X1,X2] :
        ( k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0)
        & r1_tarski(X0,X1)
        & v1_relat_1(X2) )
   => ( k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0)
      & r1_tarski(sK0,sK1)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0)
    & r1_tarski(sK0,sK1)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f30,f33])).

fof(f57,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f13,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f53,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f21])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f31])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f67,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f36])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k6_subset_1(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k6_subset_1(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k6_subset_1(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f2,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f10,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f59,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k6_subset_1(X0,k6_subset_1(X0,X1)) ),
    inference(definition_unfolding,[],[f42,f46,f46])).

fof(f62,plain,(
    ! [X0] : k1_xboole_0 = k6_subset_1(X0,k6_subset_1(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f38,f59])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f64,plain,(
    ! [X0] : k6_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f41,f46])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f63,plain,(
    ! [X0,X1] : r1_tarski(k6_subset_1(X0,X1),X0) ),
    inference(definition_unfolding,[],[f40,f46])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f56,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k2_wellord1(X2,k3_xboole_0(X0,X1)) = k2_wellord1(k2_wellord1(X2,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k2_wellord1(X2,k3_xboole_0(X0,X1)) = k2_wellord1(k2_wellord1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k2_wellord1(X2,k3_xboole_0(X0,X1)) = k2_wellord1(k2_wellord1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(X2,k6_subset_1(X0,k6_subset_1(X0,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f54,f59])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f58,plain,(
    k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_17,negated_conjecture,
    ( r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_401,plain,
    ( r1_tarski(sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_10,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_12,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_405,plain,
    ( k7_relat_1(X0,X1) = X0
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1189,plain,
    ( k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X0)
    | r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_10,c_405])).

cnf(c_13,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_27,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1605,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1189,c_27])).

cnf(c_1606,plain,
    ( k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X0)
    | r1_tarski(X0,X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_1605])).

cnf(c_1616,plain,
    ( k7_relat_1(k6_relat_1(sK0),sK1) = k6_relat_1(sK0) ),
    inference(superposition,[status(thm)],[c_401,c_1606])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_410,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1613,plain,
    ( k7_relat_1(k6_relat_1(X0),X0) = k6_relat_1(X0) ),
    inference(superposition,[status(thm)],[c_410,c_1606])).

cnf(c_404,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | k6_subset_1(k7_relat_1(X0,X1),k7_relat_1(X0,X2)) = k7_relat_1(X0,k6_subset_1(X1,X2)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_407,plain,
    ( k6_subset_1(k7_relat_1(X0,X1),k7_relat_1(X0,X2)) = k7_relat_1(X0,k6_subset_1(X1,X2))
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1423,plain,
    ( k6_subset_1(k7_relat_1(k6_relat_1(X0),X1),k7_relat_1(k6_relat_1(X0),X2)) = k7_relat_1(k6_relat_1(X0),k6_subset_1(X1,X2)) ),
    inference(superposition,[status(thm)],[c_404,c_407])).

cnf(c_4512,plain,
    ( k6_subset_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X0),X1)) = k7_relat_1(k6_relat_1(X0),k6_subset_1(X0,X1)) ),
    inference(superposition,[status(thm)],[c_1613,c_1423])).

cnf(c_11159,plain,
    ( k7_relat_1(k6_relat_1(sK0),k6_subset_1(sK0,sK1)) = k6_subset_1(k6_relat_1(sK0),k6_relat_1(sK0)) ),
    inference(superposition,[status(thm)],[c_1616,c_4512])).

cnf(c_3,plain,
    ( k6_subset_1(X0,k6_subset_1(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_6,plain,
    ( k6_subset_1(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_430,plain,
    ( k6_subset_1(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3,c_6])).

cnf(c_11243,plain,
    ( k7_relat_1(k6_relat_1(sK0),k6_subset_1(sK0,sK1)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_11159,c_430])).

cnf(c_11484,plain,
    ( k7_relat_1(k6_relat_1(sK0),k6_subset_1(sK0,k6_subset_1(sK0,sK1))) = k6_subset_1(k6_relat_1(sK0),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_11243,c_4512])).

cnf(c_11887,plain,
    ( k7_relat_1(k6_relat_1(sK0),k6_subset_1(sK0,k6_subset_1(sK0,sK1))) = k6_relat_1(sK0) ),
    inference(demodulation,[status(thm)],[c_11484,c_6])).

cnf(c_5,plain,
    ( r1_tarski(k6_subset_1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_408,plain,
    ( r1_tarski(k6_subset_1(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_11,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_406,plain,
    ( k1_relat_1(k7_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1438,plain,
    ( k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = X1
    | r1_tarski(X1,X0) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_10,c_406])).

cnf(c_1628,plain,
    ( r1_tarski(X1,X0) != iProver_top
    | k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1438,c_27])).

cnf(c_1629,plain,
    ( k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = X1
    | r1_tarski(X1,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_1628])).

cnf(c_1638,plain,
    ( k1_relat_1(k7_relat_1(k6_relat_1(X0),k6_subset_1(X0,X1))) = k6_subset_1(X0,X1) ),
    inference(superposition,[status(thm)],[c_408,c_1629])).

cnf(c_12215,plain,
    ( k6_subset_1(sK0,k6_subset_1(sK0,sK1)) = k1_relat_1(k6_relat_1(sK0)) ),
    inference(superposition,[status(thm)],[c_11887,c_1638])).

cnf(c_12217,plain,
    ( k6_subset_1(sK0,k6_subset_1(sK0,sK1)) = sK0 ),
    inference(demodulation,[status(thm)],[c_12215,c_10])).

cnf(c_18,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_400,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_14,plain,
    ( ~ v1_relat_1(X0)
    | k2_wellord1(X0,k6_subset_1(X1,k6_subset_1(X1,X2))) = k2_wellord1(k2_wellord1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_403,plain,
    ( k2_wellord1(X0,k6_subset_1(X1,k6_subset_1(X1,X2))) = k2_wellord1(k2_wellord1(X0,X1),X2)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1177,plain,
    ( k2_wellord1(sK2,k6_subset_1(X0,k6_subset_1(X0,X1))) = k2_wellord1(k2_wellord1(sK2,X0),X1) ),
    inference(superposition,[status(thm)],[c_400,c_403])).

cnf(c_12562,plain,
    ( k2_wellord1(k2_wellord1(sK2,sK0),sK1) = k2_wellord1(sK2,sK0) ),
    inference(superposition,[status(thm)],[c_12217,c_1177])).

cnf(c_15,plain,
    ( ~ v1_relat_1(X0)
    | k2_wellord1(k2_wellord1(X0,X1),X2) = k2_wellord1(k2_wellord1(X0,X2),X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_402,plain,
    ( k2_wellord1(k2_wellord1(X0,X1),X2) = k2_wellord1(k2_wellord1(X0,X2),X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_973,plain,
    ( k2_wellord1(k2_wellord1(sK2,X0),X1) = k2_wellord1(k2_wellord1(sK2,X1),X0) ),
    inference(superposition,[status(thm)],[c_400,c_402])).

cnf(c_16,negated_conjecture,
    ( k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_2152,plain,
    ( k2_wellord1(k2_wellord1(sK2,sK0),sK1) != k2_wellord1(sK2,sK0) ),
    inference(demodulation,[status(thm)],[c_973,c_16])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_12562,c_2152])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:40:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.89/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.89/0.98  
% 3.89/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.89/0.98  
% 3.89/0.98  ------  iProver source info
% 3.89/0.98  
% 3.89/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.89/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.89/0.98  git: non_committed_changes: false
% 3.89/0.98  git: last_make_outside_of_git: false
% 3.89/0.98  
% 3.89/0.98  ------ 
% 3.89/0.98  
% 3.89/0.98  ------ Input Options
% 3.89/0.98  
% 3.89/0.98  --out_options                           all
% 3.89/0.98  --tptp_safe_out                         true
% 3.89/0.98  --problem_path                          ""
% 3.89/0.98  --include_path                          ""
% 3.89/0.98  --clausifier                            res/vclausify_rel
% 3.89/0.98  --clausifier_options                    --mode clausify
% 3.89/0.98  --stdin                                 false
% 3.89/0.98  --stats_out                             sel
% 3.89/0.98  
% 3.89/0.98  ------ General Options
% 3.89/0.98  
% 3.89/0.98  --fof                                   false
% 3.89/0.98  --time_out_real                         604.99
% 3.89/0.98  --time_out_virtual                      -1.
% 3.89/0.98  --symbol_type_check                     false
% 3.89/0.98  --clausify_out                          false
% 3.89/0.98  --sig_cnt_out                           false
% 3.89/0.98  --trig_cnt_out                          false
% 3.89/0.98  --trig_cnt_out_tolerance                1.
% 3.89/0.98  --trig_cnt_out_sk_spl                   false
% 3.89/0.98  --abstr_cl_out                          false
% 3.89/0.98  
% 3.89/0.98  ------ Global Options
% 3.89/0.98  
% 3.89/0.98  --schedule                              none
% 3.89/0.98  --add_important_lit                     false
% 3.89/0.98  --prop_solver_per_cl                    1000
% 3.89/0.98  --min_unsat_core                        false
% 3.89/0.98  --soft_assumptions                      false
% 3.89/0.98  --soft_lemma_size                       3
% 3.89/0.98  --prop_impl_unit_size                   0
% 3.89/0.98  --prop_impl_unit                        []
% 3.89/0.98  --share_sel_clauses                     true
% 3.89/0.98  --reset_solvers                         false
% 3.89/0.98  --bc_imp_inh                            [conj_cone]
% 3.89/0.98  --conj_cone_tolerance                   3.
% 3.89/0.98  --extra_neg_conj                        none
% 3.89/0.98  --large_theory_mode                     true
% 3.89/0.98  --prolific_symb_bound                   200
% 3.89/0.98  --lt_threshold                          2000
% 3.89/0.98  --clause_weak_htbl                      true
% 3.89/0.98  --gc_record_bc_elim                     false
% 3.89/0.98  
% 3.89/0.98  ------ Preprocessing Options
% 3.89/0.98  
% 3.89/0.98  --preprocessing_flag                    true
% 3.89/0.98  --time_out_prep_mult                    0.1
% 3.89/0.98  --splitting_mode                        input
% 3.89/0.98  --splitting_grd                         true
% 3.89/0.98  --splitting_cvd                         false
% 3.89/0.98  --splitting_cvd_svl                     false
% 3.89/0.98  --splitting_nvd                         32
% 3.89/0.98  --sub_typing                            true
% 3.89/0.98  --prep_gs_sim                           false
% 3.89/0.98  --prep_unflatten                        true
% 3.89/0.98  --prep_res_sim                          true
% 3.89/0.98  --prep_upred                            true
% 3.89/0.98  --prep_sem_filter                       exhaustive
% 3.89/0.98  --prep_sem_filter_out                   false
% 3.89/0.98  --pred_elim                             false
% 3.89/0.98  --res_sim_input                         true
% 3.89/0.98  --eq_ax_congr_red                       true
% 3.89/0.98  --pure_diseq_elim                       true
% 3.89/0.98  --brand_transform                       false
% 3.89/0.98  --non_eq_to_eq                          false
% 3.89/0.98  --prep_def_merge                        true
% 3.89/0.98  --prep_def_merge_prop_impl              false
% 3.89/0.98  --prep_def_merge_mbd                    true
% 3.89/0.98  --prep_def_merge_tr_red                 false
% 3.89/0.98  --prep_def_merge_tr_cl                  false
% 3.89/0.98  --smt_preprocessing                     true
% 3.89/0.98  --smt_ac_axioms                         fast
% 3.89/0.98  --preprocessed_out                      false
% 3.89/0.98  --preprocessed_stats                    false
% 3.89/0.98  
% 3.89/0.98  ------ Abstraction refinement Options
% 3.89/0.98  
% 3.89/0.98  --abstr_ref                             []
% 3.89/0.98  --abstr_ref_prep                        false
% 3.89/0.98  --abstr_ref_until_sat                   false
% 3.89/0.98  --abstr_ref_sig_restrict                funpre
% 3.89/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.89/0.98  --abstr_ref_under                       []
% 3.89/0.98  
% 3.89/0.98  ------ SAT Options
% 3.89/0.98  
% 3.89/0.98  --sat_mode                              false
% 3.89/0.98  --sat_fm_restart_options                ""
% 3.89/0.98  --sat_gr_def                            false
% 3.89/0.98  --sat_epr_types                         true
% 3.89/0.98  --sat_non_cyclic_types                  false
% 3.89/0.98  --sat_finite_models                     false
% 3.89/0.98  --sat_fm_lemmas                         false
% 3.89/0.98  --sat_fm_prep                           false
% 3.89/0.98  --sat_fm_uc_incr                        true
% 3.89/0.98  --sat_out_model                         small
% 3.89/0.98  --sat_out_clauses                       false
% 3.89/0.98  
% 3.89/0.98  ------ QBF Options
% 3.89/0.98  
% 3.89/0.98  --qbf_mode                              false
% 3.89/0.98  --qbf_elim_univ                         false
% 3.89/0.98  --qbf_dom_inst                          none
% 3.89/0.98  --qbf_dom_pre_inst                      false
% 3.89/0.98  --qbf_sk_in                             false
% 3.89/0.98  --qbf_pred_elim                         true
% 3.89/0.98  --qbf_split                             512
% 3.89/0.98  
% 3.89/0.98  ------ BMC1 Options
% 3.89/0.98  
% 3.89/0.98  --bmc1_incremental                      false
% 3.89/0.98  --bmc1_axioms                           reachable_all
% 3.89/0.98  --bmc1_min_bound                        0
% 3.89/0.98  --bmc1_max_bound                        -1
% 3.89/0.98  --bmc1_max_bound_default                -1
% 3.89/0.98  --bmc1_symbol_reachability              true
% 3.89/0.98  --bmc1_property_lemmas                  false
% 3.89/0.98  --bmc1_k_induction                      false
% 3.89/0.98  --bmc1_non_equiv_states                 false
% 3.89/0.98  --bmc1_deadlock                         false
% 3.89/0.98  --bmc1_ucm                              false
% 3.89/0.98  --bmc1_add_unsat_core                   none
% 3.89/0.98  --bmc1_unsat_core_children              false
% 3.89/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.89/0.98  --bmc1_out_stat                         full
% 3.89/0.98  --bmc1_ground_init                      false
% 3.89/0.98  --bmc1_pre_inst_next_state              false
% 3.89/0.98  --bmc1_pre_inst_state                   false
% 3.89/0.98  --bmc1_pre_inst_reach_state             false
% 3.89/0.98  --bmc1_out_unsat_core                   false
% 3.89/0.98  --bmc1_aig_witness_out                  false
% 3.89/0.98  --bmc1_verbose                          false
% 3.89/0.98  --bmc1_dump_clauses_tptp                false
% 3.89/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.89/0.98  --bmc1_dump_file                        -
% 3.89/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.89/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.89/0.98  --bmc1_ucm_extend_mode                  1
% 3.89/0.98  --bmc1_ucm_init_mode                    2
% 3.89/0.98  --bmc1_ucm_cone_mode                    none
% 3.89/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.89/0.98  --bmc1_ucm_relax_model                  4
% 3.89/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.89/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.89/0.98  --bmc1_ucm_layered_model                none
% 3.89/0.98  --bmc1_ucm_max_lemma_size               10
% 3.89/0.98  
% 3.89/0.98  ------ AIG Options
% 3.89/0.98  
% 3.89/0.98  --aig_mode                              false
% 3.89/0.98  
% 3.89/0.98  ------ Instantiation Options
% 3.89/0.98  
% 3.89/0.98  --instantiation_flag                    true
% 3.89/0.98  --inst_sos_flag                         false
% 3.89/0.98  --inst_sos_phase                        true
% 3.89/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.89/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.89/0.98  --inst_lit_sel_side                     num_symb
% 3.89/0.98  --inst_solver_per_active                1400
% 3.89/0.98  --inst_solver_calls_frac                1.
% 3.89/0.98  --inst_passive_queue_type               priority_queues
% 3.89/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.89/0.98  --inst_passive_queues_freq              [25;2]
% 3.89/0.98  --inst_dismatching                      true
% 3.89/0.98  --inst_eager_unprocessed_to_passive     true
% 3.89/0.98  --inst_prop_sim_given                   true
% 3.89/0.98  --inst_prop_sim_new                     false
% 3.89/0.98  --inst_subs_new                         false
% 3.89/0.98  --inst_eq_res_simp                      false
% 3.89/0.98  --inst_subs_given                       false
% 3.89/0.98  --inst_orphan_elimination               true
% 3.89/0.98  --inst_learning_loop_flag               true
% 3.89/0.98  --inst_learning_start                   3000
% 3.89/0.98  --inst_learning_factor                  2
% 3.89/0.98  --inst_start_prop_sim_after_learn       3
% 3.89/0.98  --inst_sel_renew                        solver
% 3.89/0.98  --inst_lit_activity_flag                true
% 3.89/0.98  --inst_restr_to_given                   false
% 3.89/0.98  --inst_activity_threshold               500
% 3.89/0.98  --inst_out_proof                        true
% 3.89/0.98  
% 3.89/0.98  ------ Resolution Options
% 3.89/0.98  
% 3.89/0.98  --resolution_flag                       true
% 3.89/0.98  --res_lit_sel                           adaptive
% 3.89/0.98  --res_lit_sel_side                      none
% 3.89/0.98  --res_ordering                          kbo
% 3.89/0.98  --res_to_prop_solver                    active
% 3.89/0.98  --res_prop_simpl_new                    false
% 3.89/0.98  --res_prop_simpl_given                  true
% 3.89/0.98  --res_passive_queue_type                priority_queues
% 3.89/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.89/0.98  --res_passive_queues_freq               [15;5]
% 3.89/0.98  --res_forward_subs                      full
% 3.89/0.98  --res_backward_subs                     full
% 3.89/0.98  --res_forward_subs_resolution           true
% 3.89/0.98  --res_backward_subs_resolution          true
% 3.89/0.98  --res_orphan_elimination                true
% 3.89/0.98  --res_time_limit                        2.
% 3.89/0.98  --res_out_proof                         true
% 3.89/0.98  
% 3.89/0.98  ------ Superposition Options
% 3.89/0.98  
% 3.89/0.98  --superposition_flag                    true
% 3.89/0.98  --sup_passive_queue_type                priority_queues
% 3.89/0.98  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.89/0.98  --sup_passive_queues_freq               [1;4]
% 3.89/0.98  --demod_completeness_check              fast
% 3.89/0.98  --demod_use_ground                      true
% 3.89/0.98  --sup_to_prop_solver                    passive
% 3.89/0.98  --sup_prop_simpl_new                    true
% 3.89/0.98  --sup_prop_simpl_given                  true
% 3.89/0.98  --sup_fun_splitting                     false
% 3.89/0.98  --sup_smt_interval                      50000
% 3.89/0.98  
% 3.89/0.98  ------ Superposition Simplification Setup
% 3.89/0.99  
% 3.89/0.99  --sup_indices_passive                   []
% 3.89/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.89/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.89/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.89/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.89/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.89/0.99  --sup_full_bw                           [BwDemod]
% 3.89/0.99  --sup_immed_triv                        [TrivRules]
% 3.89/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.89/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.89/0.99  --sup_immed_bw_main                     []
% 3.89/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.89/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.89/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.89/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.89/0.99  
% 3.89/0.99  ------ Combination Options
% 3.89/0.99  
% 3.89/0.99  --comb_res_mult                         3
% 3.89/0.99  --comb_sup_mult                         2
% 3.89/0.99  --comb_inst_mult                        10
% 3.89/0.99  
% 3.89/0.99  ------ Debug Options
% 3.89/0.99  
% 3.89/0.99  --dbg_backtrace                         false
% 3.89/0.99  --dbg_dump_prop_clauses                 false
% 3.89/0.99  --dbg_dump_prop_clauses_file            -
% 3.89/0.99  --dbg_out_stat                          false
% 3.89/0.99  ------ Parsing...
% 3.89/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.89/0.99  
% 3.89/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 3.89/0.99  
% 3.89/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.89/0.99  
% 3.89/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.89/0.99  ------ Proving...
% 3.89/0.99  ------ Problem Properties 
% 3.89/0.99  
% 3.89/0.99  
% 3.89/0.99  clauses                                 18
% 3.89/0.99  conjectures                             3
% 3.89/0.99  EPR                                     5
% 3.89/0.99  Horn                                    18
% 3.89/0.99  unary                                   12
% 3.89/0.99  binary                                  3
% 3.89/0.99  lits                                    27
% 3.89/0.99  lits eq                                 12
% 3.89/0.99  fd_pure                                 0
% 3.89/0.99  fd_pseudo                               0
% 3.89/0.99  fd_cond                                 0
% 3.89/0.99  fd_pseudo_cond                          1
% 3.89/0.99  AC symbols                              0
% 3.89/0.99  
% 3.89/0.99  ------ Input Options Time Limit: Unbounded
% 3.89/0.99  
% 3.89/0.99  
% 3.89/0.99  ------ 
% 3.89/0.99  Current options:
% 3.89/0.99  ------ 
% 3.89/0.99  
% 3.89/0.99  ------ Input Options
% 3.89/0.99  
% 3.89/0.99  --out_options                           all
% 3.89/0.99  --tptp_safe_out                         true
% 3.89/0.99  --problem_path                          ""
% 3.89/0.99  --include_path                          ""
% 3.89/0.99  --clausifier                            res/vclausify_rel
% 3.89/0.99  --clausifier_options                    --mode clausify
% 3.89/0.99  --stdin                                 false
% 3.89/0.99  --stats_out                             sel
% 3.89/0.99  
% 3.89/0.99  ------ General Options
% 3.89/0.99  
% 3.89/0.99  --fof                                   false
% 3.89/0.99  --time_out_real                         604.99
% 3.89/0.99  --time_out_virtual                      -1.
% 3.89/0.99  --symbol_type_check                     false
% 3.89/0.99  --clausify_out                          false
% 3.89/0.99  --sig_cnt_out                           false
% 3.89/0.99  --trig_cnt_out                          false
% 3.89/0.99  --trig_cnt_out_tolerance                1.
% 3.89/0.99  --trig_cnt_out_sk_spl                   false
% 3.89/0.99  --abstr_cl_out                          false
% 3.89/0.99  
% 3.89/0.99  ------ Global Options
% 3.89/0.99  
% 3.89/0.99  --schedule                              none
% 3.89/0.99  --add_important_lit                     false
% 3.89/0.99  --prop_solver_per_cl                    1000
% 3.89/0.99  --min_unsat_core                        false
% 3.89/0.99  --soft_assumptions                      false
% 3.89/0.99  --soft_lemma_size                       3
% 3.89/0.99  --prop_impl_unit_size                   0
% 3.89/0.99  --prop_impl_unit                        []
% 3.89/0.99  --share_sel_clauses                     true
% 3.89/0.99  --reset_solvers                         false
% 3.89/0.99  --bc_imp_inh                            [conj_cone]
% 3.89/0.99  --conj_cone_tolerance                   3.
% 3.89/0.99  --extra_neg_conj                        none
% 3.89/0.99  --large_theory_mode                     true
% 3.89/0.99  --prolific_symb_bound                   200
% 3.89/0.99  --lt_threshold                          2000
% 3.89/0.99  --clause_weak_htbl                      true
% 3.89/0.99  --gc_record_bc_elim                     false
% 3.89/0.99  
% 3.89/0.99  ------ Preprocessing Options
% 3.89/0.99  
% 3.89/0.99  --preprocessing_flag                    true
% 3.89/0.99  --time_out_prep_mult                    0.1
% 3.89/0.99  --splitting_mode                        input
% 3.89/0.99  --splitting_grd                         true
% 3.89/0.99  --splitting_cvd                         false
% 3.89/0.99  --splitting_cvd_svl                     false
% 3.89/0.99  --splitting_nvd                         32
% 3.89/0.99  --sub_typing                            true
% 3.89/0.99  --prep_gs_sim                           false
% 3.89/0.99  --prep_unflatten                        true
% 3.89/0.99  --prep_res_sim                          true
% 3.89/0.99  --prep_upred                            true
% 3.89/0.99  --prep_sem_filter                       exhaustive
% 3.89/0.99  --prep_sem_filter_out                   false
% 3.89/0.99  --pred_elim                             false
% 3.89/0.99  --res_sim_input                         true
% 3.89/0.99  --eq_ax_congr_red                       true
% 3.89/0.99  --pure_diseq_elim                       true
% 3.89/0.99  --brand_transform                       false
% 3.89/0.99  --non_eq_to_eq                          false
% 3.89/0.99  --prep_def_merge                        true
% 3.89/0.99  --prep_def_merge_prop_impl              false
% 3.89/0.99  --prep_def_merge_mbd                    true
% 3.89/0.99  --prep_def_merge_tr_red                 false
% 3.89/0.99  --prep_def_merge_tr_cl                  false
% 3.89/0.99  --smt_preprocessing                     true
% 3.89/0.99  --smt_ac_axioms                         fast
% 3.89/0.99  --preprocessed_out                      false
% 3.89/0.99  --preprocessed_stats                    false
% 3.89/0.99  
% 3.89/0.99  ------ Abstraction refinement Options
% 3.89/0.99  
% 3.89/0.99  --abstr_ref                             []
% 3.89/0.99  --abstr_ref_prep                        false
% 3.89/0.99  --abstr_ref_until_sat                   false
% 3.89/0.99  --abstr_ref_sig_restrict                funpre
% 3.89/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.89/0.99  --abstr_ref_under                       []
% 3.89/0.99  
% 3.89/0.99  ------ SAT Options
% 3.89/0.99  
% 3.89/0.99  --sat_mode                              false
% 3.89/0.99  --sat_fm_restart_options                ""
% 3.89/0.99  --sat_gr_def                            false
% 3.89/0.99  --sat_epr_types                         true
% 3.89/0.99  --sat_non_cyclic_types                  false
% 3.89/0.99  --sat_finite_models                     false
% 3.89/0.99  --sat_fm_lemmas                         false
% 3.89/0.99  --sat_fm_prep                           false
% 3.89/0.99  --sat_fm_uc_incr                        true
% 3.89/0.99  --sat_out_model                         small
% 3.89/0.99  --sat_out_clauses                       false
% 3.89/0.99  
% 3.89/0.99  ------ QBF Options
% 3.89/0.99  
% 3.89/0.99  --qbf_mode                              false
% 3.89/0.99  --qbf_elim_univ                         false
% 3.89/0.99  --qbf_dom_inst                          none
% 3.89/0.99  --qbf_dom_pre_inst                      false
% 3.89/0.99  --qbf_sk_in                             false
% 3.89/0.99  --qbf_pred_elim                         true
% 3.89/0.99  --qbf_split                             512
% 3.89/0.99  
% 3.89/0.99  ------ BMC1 Options
% 3.89/0.99  
% 3.89/0.99  --bmc1_incremental                      false
% 3.89/0.99  --bmc1_axioms                           reachable_all
% 3.89/0.99  --bmc1_min_bound                        0
% 3.89/0.99  --bmc1_max_bound                        -1
% 3.89/0.99  --bmc1_max_bound_default                -1
% 3.89/0.99  --bmc1_symbol_reachability              true
% 3.89/0.99  --bmc1_property_lemmas                  false
% 3.89/0.99  --bmc1_k_induction                      false
% 3.89/0.99  --bmc1_non_equiv_states                 false
% 3.89/0.99  --bmc1_deadlock                         false
% 3.89/0.99  --bmc1_ucm                              false
% 3.89/0.99  --bmc1_add_unsat_core                   none
% 3.89/0.99  --bmc1_unsat_core_children              false
% 3.89/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.89/0.99  --bmc1_out_stat                         full
% 3.89/0.99  --bmc1_ground_init                      false
% 3.89/0.99  --bmc1_pre_inst_next_state              false
% 3.89/0.99  --bmc1_pre_inst_state                   false
% 3.89/0.99  --bmc1_pre_inst_reach_state             false
% 3.89/0.99  --bmc1_out_unsat_core                   false
% 3.89/0.99  --bmc1_aig_witness_out                  false
% 3.89/0.99  --bmc1_verbose                          false
% 3.89/0.99  --bmc1_dump_clauses_tptp                false
% 3.89/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.89/0.99  --bmc1_dump_file                        -
% 3.89/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.89/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.89/0.99  --bmc1_ucm_extend_mode                  1
% 3.89/0.99  --bmc1_ucm_init_mode                    2
% 3.89/0.99  --bmc1_ucm_cone_mode                    none
% 3.89/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.89/0.99  --bmc1_ucm_relax_model                  4
% 3.89/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.89/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.89/0.99  --bmc1_ucm_layered_model                none
% 3.89/0.99  --bmc1_ucm_max_lemma_size               10
% 3.89/0.99  
% 3.89/0.99  ------ AIG Options
% 3.89/0.99  
% 3.89/0.99  --aig_mode                              false
% 3.89/0.99  
% 3.89/0.99  ------ Instantiation Options
% 3.89/0.99  
% 3.89/0.99  --instantiation_flag                    true
% 3.89/0.99  --inst_sos_flag                         false
% 3.89/0.99  --inst_sos_phase                        true
% 3.89/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.89/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.89/0.99  --inst_lit_sel_side                     num_symb
% 3.89/0.99  --inst_solver_per_active                1400
% 3.89/0.99  --inst_solver_calls_frac                1.
% 3.89/0.99  --inst_passive_queue_type               priority_queues
% 3.89/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.89/0.99  --inst_passive_queues_freq              [25;2]
% 3.89/0.99  --inst_dismatching                      true
% 3.89/0.99  --inst_eager_unprocessed_to_passive     true
% 3.89/0.99  --inst_prop_sim_given                   true
% 3.89/0.99  --inst_prop_sim_new                     false
% 3.89/0.99  --inst_subs_new                         false
% 3.89/0.99  --inst_eq_res_simp                      false
% 3.89/0.99  --inst_subs_given                       false
% 3.89/0.99  --inst_orphan_elimination               true
% 3.89/0.99  --inst_learning_loop_flag               true
% 3.89/0.99  --inst_learning_start                   3000
% 3.89/0.99  --inst_learning_factor                  2
% 3.89/0.99  --inst_start_prop_sim_after_learn       3
% 3.89/0.99  --inst_sel_renew                        solver
% 3.89/0.99  --inst_lit_activity_flag                true
% 3.89/0.99  --inst_restr_to_given                   false
% 3.89/0.99  --inst_activity_threshold               500
% 3.89/0.99  --inst_out_proof                        true
% 3.89/0.99  
% 3.89/0.99  ------ Resolution Options
% 3.89/0.99  
% 3.89/0.99  --resolution_flag                       true
% 3.89/0.99  --res_lit_sel                           adaptive
% 3.89/0.99  --res_lit_sel_side                      none
% 3.89/0.99  --res_ordering                          kbo
% 3.89/0.99  --res_to_prop_solver                    active
% 3.89/0.99  --res_prop_simpl_new                    false
% 3.89/0.99  --res_prop_simpl_given                  true
% 3.89/0.99  --res_passive_queue_type                priority_queues
% 3.89/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.89/0.99  --res_passive_queues_freq               [15;5]
% 3.89/0.99  --res_forward_subs                      full
% 3.89/0.99  --res_backward_subs                     full
% 3.89/0.99  --res_forward_subs_resolution           true
% 3.89/0.99  --res_backward_subs_resolution          true
% 3.89/0.99  --res_orphan_elimination                true
% 3.89/0.99  --res_time_limit                        2.
% 3.89/0.99  --res_out_proof                         true
% 3.89/0.99  
% 3.89/0.99  ------ Superposition Options
% 3.89/0.99  
% 3.89/0.99  --superposition_flag                    true
% 3.89/0.99  --sup_passive_queue_type                priority_queues
% 3.89/0.99  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.89/0.99  --sup_passive_queues_freq               [1;4]
% 3.89/0.99  --demod_completeness_check              fast
% 3.89/0.99  --demod_use_ground                      true
% 3.89/0.99  --sup_to_prop_solver                    passive
% 3.89/0.99  --sup_prop_simpl_new                    true
% 3.89/0.99  --sup_prop_simpl_given                  true
% 3.89/0.99  --sup_fun_splitting                     false
% 3.89/0.99  --sup_smt_interval                      50000
% 3.89/0.99  
% 3.89/0.99  ------ Superposition Simplification Setup
% 3.89/0.99  
% 3.89/0.99  --sup_indices_passive                   []
% 3.89/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.89/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.89/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.89/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.89/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.89/0.99  --sup_full_bw                           [BwDemod]
% 3.89/0.99  --sup_immed_triv                        [TrivRules]
% 3.89/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.89/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.89/0.99  --sup_immed_bw_main                     []
% 3.89/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.89/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.89/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.89/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.89/0.99  
% 3.89/0.99  ------ Combination Options
% 3.89/0.99  
% 3.89/0.99  --comb_res_mult                         3
% 3.89/0.99  --comb_sup_mult                         2
% 3.89/0.99  --comb_inst_mult                        10
% 3.89/0.99  
% 3.89/0.99  ------ Debug Options
% 3.89/0.99  
% 3.89/0.99  --dbg_backtrace                         false
% 3.89/0.99  --dbg_dump_prop_clauses                 false
% 3.89/0.99  --dbg_dump_prop_clauses_file            -
% 3.89/0.99  --dbg_out_stat                          false
% 3.89/0.99  
% 3.89/0.99  
% 3.89/0.99  
% 3.89/0.99  
% 3.89/0.99  ------ Proving...
% 3.89/0.99  
% 3.89/0.99  
% 3.89/0.99  % SZS status Theorem for theBenchmark.p
% 3.89/0.99  
% 3.89/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.89/0.99  
% 3.89/0.99  fof(f19,conjecture,(
% 3.89/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k2_wellord1(X2,X0) = k2_wellord1(k2_wellord1(X2,X1),X0)))),
% 3.89/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.89/0.99  
% 3.89/0.99  fof(f20,negated_conjecture,(
% 3.89/0.99    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k2_wellord1(X2,X0) = k2_wellord1(k2_wellord1(X2,X1),X0)))),
% 3.89/0.99    inference(negated_conjecture,[],[f19])).
% 3.89/0.99  
% 3.89/0.99  fof(f29,plain,(
% 3.89/0.99    ? [X0,X1,X2] : ((k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0) & r1_tarski(X0,X1)) & v1_relat_1(X2))),
% 3.89/0.99    inference(ennf_transformation,[],[f20])).
% 3.89/0.99  
% 3.89/0.99  fof(f30,plain,(
% 3.89/0.99    ? [X0,X1,X2] : (k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0) & r1_tarski(X0,X1) & v1_relat_1(X2))),
% 3.89/0.99    inference(flattening,[],[f29])).
% 3.89/0.99  
% 3.89/0.99  fof(f33,plain,(
% 3.89/0.99    ? [X0,X1,X2] : (k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0) & r1_tarski(X0,X1) & v1_relat_1(X2)) => (k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0) & r1_tarski(sK0,sK1) & v1_relat_1(sK2))),
% 3.89/0.99    introduced(choice_axiom,[])).
% 3.89/0.99  
% 3.89/0.99  fof(f34,plain,(
% 3.89/0.99    k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0) & r1_tarski(sK0,sK1) & v1_relat_1(sK2)),
% 3.89/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f30,f33])).
% 3.89/0.99  
% 3.89/0.99  fof(f57,plain,(
% 3.89/0.99    r1_tarski(sK0,sK1)),
% 3.89/0.99    inference(cnf_transformation,[],[f34])).
% 3.89/0.99  
% 3.89/0.99  fof(f13,axiom,(
% 3.89/0.99    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 3.89/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.89/0.99  
% 3.89/0.99  fof(f49,plain,(
% 3.89/0.99    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 3.89/0.99    inference(cnf_transformation,[],[f13])).
% 3.89/0.99  
% 3.89/0.99  fof(f15,axiom,(
% 3.89/0.99    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 3.89/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.89/0.99  
% 3.89/0.99  fof(f25,plain,(
% 3.89/0.99    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.89/0.99    inference(ennf_transformation,[],[f15])).
% 3.89/0.99  
% 3.89/0.99  fof(f26,plain,(
% 3.89/0.99    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 3.89/0.99    inference(flattening,[],[f25])).
% 3.89/0.99  
% 3.89/0.99  fof(f52,plain,(
% 3.89/0.99    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 3.89/0.99    inference(cnf_transformation,[],[f26])).
% 3.89/0.99  
% 3.89/0.99  fof(f16,axiom,(
% 3.89/0.99    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 3.89/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.89/0.99  
% 3.89/0.99  fof(f21,plain,(
% 3.89/0.99    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 3.89/0.99    inference(pure_predicate_removal,[],[f16])).
% 3.89/0.99  
% 3.89/0.99  fof(f53,plain,(
% 3.89/0.99    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 3.89/0.99    inference(cnf_transformation,[],[f21])).
% 3.89/0.99  
% 3.89/0.99  fof(f1,axiom,(
% 3.89/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.89/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.89/0.99  
% 3.89/0.99  fof(f31,plain,(
% 3.89/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.89/0.99    inference(nnf_transformation,[],[f1])).
% 3.89/0.99  
% 3.89/0.99  fof(f32,plain,(
% 3.89/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.89/0.99    inference(flattening,[],[f31])).
% 3.89/0.99  
% 3.89/0.99  fof(f36,plain,(
% 3.89/0.99    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.89/0.99    inference(cnf_transformation,[],[f32])).
% 3.89/0.99  
% 3.89/0.99  fof(f67,plain,(
% 3.89/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.89/0.99    inference(equality_resolution,[],[f36])).
% 3.89/0.99  
% 3.89/0.99  fof(f12,axiom,(
% 3.89/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) => k6_subset_1(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1)))),
% 3.89/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.89/0.99  
% 3.89/0.99  fof(f22,plain,(
% 3.89/0.99    ! [X0,X1,X2] : (k6_subset_1(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1)) | ~v1_relat_1(X2))),
% 3.89/0.99    inference(ennf_transformation,[],[f12])).
% 3.89/0.99  
% 3.89/0.99  fof(f48,plain,(
% 3.89/0.99    ( ! [X2,X0,X1] : (k6_subset_1(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1)) | ~v1_relat_1(X2)) )),
% 3.89/0.99    inference(cnf_transformation,[],[f22])).
% 3.89/0.99  
% 3.89/0.99  fof(f2,axiom,(
% 3.89/0.99    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 3.89/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.89/0.99  
% 3.89/0.99  fof(f38,plain,(
% 3.89/0.99    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 3.89/0.99    inference(cnf_transformation,[],[f2])).
% 3.89/0.99  
% 3.89/0.99  fof(f6,axiom,(
% 3.89/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.89/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.89/0.99  
% 3.89/0.99  fof(f42,plain,(
% 3.89/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.89/0.99    inference(cnf_transformation,[],[f6])).
% 3.89/0.99  
% 3.89/0.99  fof(f10,axiom,(
% 3.89/0.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 3.89/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.89/0.99  
% 3.89/0.99  fof(f46,plain,(
% 3.89/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 3.89/0.99    inference(cnf_transformation,[],[f10])).
% 3.89/0.99  
% 3.89/0.99  fof(f59,plain,(
% 3.89/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k6_subset_1(X0,k6_subset_1(X0,X1))) )),
% 3.89/0.99    inference(definition_unfolding,[],[f42,f46,f46])).
% 3.89/0.99  
% 3.89/0.99  fof(f62,plain,(
% 3.89/0.99    ( ! [X0] : (k1_xboole_0 = k6_subset_1(X0,k6_subset_1(X0,k1_xboole_0))) )),
% 3.89/0.99    inference(definition_unfolding,[],[f38,f59])).
% 3.89/0.99  
% 3.89/0.99  fof(f5,axiom,(
% 3.89/0.99    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 3.89/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.89/0.99  
% 3.89/0.99  fof(f41,plain,(
% 3.89/0.99    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.89/0.99    inference(cnf_transformation,[],[f5])).
% 3.89/0.99  
% 3.89/0.99  fof(f64,plain,(
% 3.89/0.99    ( ! [X0] : (k6_subset_1(X0,k1_xboole_0) = X0) )),
% 3.89/0.99    inference(definition_unfolding,[],[f41,f46])).
% 3.89/0.99  
% 3.89/0.99  fof(f4,axiom,(
% 3.89/0.99    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 3.89/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.89/0.99  
% 3.89/0.99  fof(f40,plain,(
% 3.89/0.99    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 3.89/0.99    inference(cnf_transformation,[],[f4])).
% 3.89/0.99  
% 3.89/0.99  fof(f63,plain,(
% 3.89/0.99    ( ! [X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X0)) )),
% 3.89/0.99    inference(definition_unfolding,[],[f40,f46])).
% 3.89/0.99  
% 3.89/0.99  fof(f14,axiom,(
% 3.89/0.99    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 3.89/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.89/0.99  
% 3.89/0.99  fof(f23,plain,(
% 3.89/0.99    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 3.89/0.99    inference(ennf_transformation,[],[f14])).
% 3.89/0.99  
% 3.89/0.99  fof(f24,plain,(
% 3.89/0.99    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 3.89/0.99    inference(flattening,[],[f23])).
% 3.89/0.99  
% 3.89/0.99  fof(f51,plain,(
% 3.89/0.99    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.89/0.99    inference(cnf_transformation,[],[f24])).
% 3.89/0.99  
% 3.89/0.99  fof(f56,plain,(
% 3.89/0.99    v1_relat_1(sK2)),
% 3.89/0.99    inference(cnf_transformation,[],[f34])).
% 3.89/0.99  
% 3.89/0.99  fof(f17,axiom,(
% 3.89/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) => k2_wellord1(X2,k3_xboole_0(X0,X1)) = k2_wellord1(k2_wellord1(X2,X0),X1))),
% 3.89/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.89/0.99  
% 3.89/0.99  fof(f27,plain,(
% 3.89/0.99    ! [X0,X1,X2] : (k2_wellord1(X2,k3_xboole_0(X0,X1)) = k2_wellord1(k2_wellord1(X2,X0),X1) | ~v1_relat_1(X2))),
% 3.89/0.99    inference(ennf_transformation,[],[f17])).
% 3.89/0.99  
% 3.89/0.99  fof(f54,plain,(
% 3.89/0.99    ( ! [X2,X0,X1] : (k2_wellord1(X2,k3_xboole_0(X0,X1)) = k2_wellord1(k2_wellord1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 3.89/0.99    inference(cnf_transformation,[],[f27])).
% 3.89/0.99  
% 3.89/0.99  fof(f66,plain,(
% 3.89/0.99    ( ! [X2,X0,X1] : (k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(X2,k6_subset_1(X0,k6_subset_1(X0,X1))) | ~v1_relat_1(X2)) )),
% 3.89/0.99    inference(definition_unfolding,[],[f54,f59])).
% 3.89/0.99  
% 3.89/0.99  fof(f18,axiom,(
% 3.89/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) => k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0))),
% 3.89/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.89/0.99  
% 3.89/0.99  fof(f28,plain,(
% 3.89/0.99    ! [X0,X1,X2] : (k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0) | ~v1_relat_1(X2))),
% 3.89/0.99    inference(ennf_transformation,[],[f18])).
% 3.89/0.99  
% 3.89/0.99  fof(f55,plain,(
% 3.89/0.99    ( ! [X2,X0,X1] : (k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0) | ~v1_relat_1(X2)) )),
% 3.89/0.99    inference(cnf_transformation,[],[f28])).
% 3.89/0.99  
% 3.89/0.99  fof(f58,plain,(
% 3.89/0.99    k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0)),
% 3.89/0.99    inference(cnf_transformation,[],[f34])).
% 3.89/0.99  
% 3.89/0.99  cnf(c_17,negated_conjecture,
% 3.89/0.99      ( r1_tarski(sK0,sK1) ),
% 3.89/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_401,plain,
% 3.89/0.99      ( r1_tarski(sK0,sK1) = iProver_top ),
% 3.89/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_10,plain,
% 3.89/0.99      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 3.89/0.99      inference(cnf_transformation,[],[f49]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_12,plain,
% 3.89/0.99      ( ~ r1_tarski(k1_relat_1(X0),X1)
% 3.89/0.99      | ~ v1_relat_1(X0)
% 3.89/0.99      | k7_relat_1(X0,X1) = X0 ),
% 3.89/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_405,plain,
% 3.89/0.99      ( k7_relat_1(X0,X1) = X0
% 3.89/0.99      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 3.89/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.89/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_1189,plain,
% 3.89/0.99      ( k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X0)
% 3.89/0.99      | r1_tarski(X0,X1) != iProver_top
% 3.89/0.99      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 3.89/0.99      inference(superposition,[status(thm)],[c_10,c_405]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_13,plain,
% 3.89/0.99      ( v1_relat_1(k6_relat_1(X0)) ),
% 3.89/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_27,plain,
% 3.89/0.99      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 3.89/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_1605,plain,
% 3.89/0.99      ( r1_tarski(X0,X1) != iProver_top
% 3.89/0.99      | k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X0) ),
% 3.89/0.99      inference(global_propositional_subsumption,
% 3.89/0.99                [status(thm)],
% 3.89/0.99                [c_1189,c_27]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_1606,plain,
% 3.89/0.99      ( k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X0)
% 3.89/0.99      | r1_tarski(X0,X1) != iProver_top ),
% 3.89/0.99      inference(renaming,[status(thm)],[c_1605]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_1616,plain,
% 3.89/0.99      ( k7_relat_1(k6_relat_1(sK0),sK1) = k6_relat_1(sK0) ),
% 3.89/0.99      inference(superposition,[status(thm)],[c_401,c_1606]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_1,plain,
% 3.89/0.99      ( r1_tarski(X0,X0) ),
% 3.89/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_410,plain,
% 3.89/0.99      ( r1_tarski(X0,X0) = iProver_top ),
% 3.89/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_1613,plain,
% 3.89/0.99      ( k7_relat_1(k6_relat_1(X0),X0) = k6_relat_1(X0) ),
% 3.89/0.99      inference(superposition,[status(thm)],[c_410,c_1606]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_404,plain,
% 3.89/0.99      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 3.89/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_8,plain,
% 3.89/0.99      ( ~ v1_relat_1(X0)
% 3.89/0.99      | k6_subset_1(k7_relat_1(X0,X1),k7_relat_1(X0,X2)) = k7_relat_1(X0,k6_subset_1(X1,X2)) ),
% 3.89/0.99      inference(cnf_transformation,[],[f48]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_407,plain,
% 3.89/0.99      ( k6_subset_1(k7_relat_1(X0,X1),k7_relat_1(X0,X2)) = k7_relat_1(X0,k6_subset_1(X1,X2))
% 3.89/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.89/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_1423,plain,
% 3.89/0.99      ( k6_subset_1(k7_relat_1(k6_relat_1(X0),X1),k7_relat_1(k6_relat_1(X0),X2)) = k7_relat_1(k6_relat_1(X0),k6_subset_1(X1,X2)) ),
% 3.89/0.99      inference(superposition,[status(thm)],[c_404,c_407]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_4512,plain,
% 3.89/0.99      ( k6_subset_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X0),X1)) = k7_relat_1(k6_relat_1(X0),k6_subset_1(X0,X1)) ),
% 3.89/0.99      inference(superposition,[status(thm)],[c_1613,c_1423]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_11159,plain,
% 3.89/0.99      ( k7_relat_1(k6_relat_1(sK0),k6_subset_1(sK0,sK1)) = k6_subset_1(k6_relat_1(sK0),k6_relat_1(sK0)) ),
% 3.89/0.99      inference(superposition,[status(thm)],[c_1616,c_4512]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_3,plain,
% 3.89/0.99      ( k6_subset_1(X0,k6_subset_1(X0,k1_xboole_0)) = k1_xboole_0 ),
% 3.89/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_6,plain,
% 3.89/0.99      ( k6_subset_1(X0,k1_xboole_0) = X0 ),
% 3.89/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_430,plain,
% 3.89/0.99      ( k6_subset_1(X0,X0) = k1_xboole_0 ),
% 3.89/0.99      inference(light_normalisation,[status(thm)],[c_3,c_6]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_11243,plain,
% 3.89/0.99      ( k7_relat_1(k6_relat_1(sK0),k6_subset_1(sK0,sK1)) = k1_xboole_0 ),
% 3.89/0.99      inference(demodulation,[status(thm)],[c_11159,c_430]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_11484,plain,
% 3.89/0.99      ( k7_relat_1(k6_relat_1(sK0),k6_subset_1(sK0,k6_subset_1(sK0,sK1))) = k6_subset_1(k6_relat_1(sK0),k1_xboole_0) ),
% 3.89/0.99      inference(superposition,[status(thm)],[c_11243,c_4512]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_11887,plain,
% 3.89/0.99      ( k7_relat_1(k6_relat_1(sK0),k6_subset_1(sK0,k6_subset_1(sK0,sK1))) = k6_relat_1(sK0) ),
% 3.89/0.99      inference(demodulation,[status(thm)],[c_11484,c_6]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_5,plain,
% 3.89/0.99      ( r1_tarski(k6_subset_1(X0,X1),X0) ),
% 3.89/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_408,plain,
% 3.89/0.99      ( r1_tarski(k6_subset_1(X0,X1),X0) = iProver_top ),
% 3.89/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_11,plain,
% 3.89/0.99      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 3.89/0.99      | ~ v1_relat_1(X1)
% 3.89/0.99      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
% 3.89/0.99      inference(cnf_transformation,[],[f51]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_406,plain,
% 3.89/0.99      ( k1_relat_1(k7_relat_1(X0,X1)) = X1
% 3.89/0.99      | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
% 3.89/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.89/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_1438,plain,
% 3.89/0.99      ( k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = X1
% 3.89/0.99      | r1_tarski(X1,X0) != iProver_top
% 3.89/0.99      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 3.89/0.99      inference(superposition,[status(thm)],[c_10,c_406]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_1628,plain,
% 3.89/0.99      ( r1_tarski(X1,X0) != iProver_top
% 3.89/0.99      | k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = X1 ),
% 3.89/0.99      inference(global_propositional_subsumption,
% 3.89/0.99                [status(thm)],
% 3.89/0.99                [c_1438,c_27]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_1629,plain,
% 3.89/0.99      ( k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = X1
% 3.89/0.99      | r1_tarski(X1,X0) != iProver_top ),
% 3.89/0.99      inference(renaming,[status(thm)],[c_1628]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_1638,plain,
% 3.89/0.99      ( k1_relat_1(k7_relat_1(k6_relat_1(X0),k6_subset_1(X0,X1))) = k6_subset_1(X0,X1) ),
% 3.89/0.99      inference(superposition,[status(thm)],[c_408,c_1629]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_12215,plain,
% 3.89/0.99      ( k6_subset_1(sK0,k6_subset_1(sK0,sK1)) = k1_relat_1(k6_relat_1(sK0)) ),
% 3.89/0.99      inference(superposition,[status(thm)],[c_11887,c_1638]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_12217,plain,
% 3.89/0.99      ( k6_subset_1(sK0,k6_subset_1(sK0,sK1)) = sK0 ),
% 3.89/0.99      inference(demodulation,[status(thm)],[c_12215,c_10]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_18,negated_conjecture,
% 3.89/0.99      ( v1_relat_1(sK2) ),
% 3.89/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_400,plain,
% 3.89/0.99      ( v1_relat_1(sK2) = iProver_top ),
% 3.89/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_14,plain,
% 3.89/0.99      ( ~ v1_relat_1(X0)
% 3.89/0.99      | k2_wellord1(X0,k6_subset_1(X1,k6_subset_1(X1,X2))) = k2_wellord1(k2_wellord1(X0,X1),X2) ),
% 3.89/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_403,plain,
% 3.89/0.99      ( k2_wellord1(X0,k6_subset_1(X1,k6_subset_1(X1,X2))) = k2_wellord1(k2_wellord1(X0,X1),X2)
% 3.89/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.89/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_1177,plain,
% 3.89/0.99      ( k2_wellord1(sK2,k6_subset_1(X0,k6_subset_1(X0,X1))) = k2_wellord1(k2_wellord1(sK2,X0),X1) ),
% 3.89/0.99      inference(superposition,[status(thm)],[c_400,c_403]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_12562,plain,
% 3.89/0.99      ( k2_wellord1(k2_wellord1(sK2,sK0),sK1) = k2_wellord1(sK2,sK0) ),
% 3.89/0.99      inference(superposition,[status(thm)],[c_12217,c_1177]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_15,plain,
% 3.89/0.99      ( ~ v1_relat_1(X0)
% 3.89/0.99      | k2_wellord1(k2_wellord1(X0,X1),X2) = k2_wellord1(k2_wellord1(X0,X2),X1) ),
% 3.89/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_402,plain,
% 3.89/0.99      ( k2_wellord1(k2_wellord1(X0,X1),X2) = k2_wellord1(k2_wellord1(X0,X2),X1)
% 3.89/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.89/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_973,plain,
% 3.89/0.99      ( k2_wellord1(k2_wellord1(sK2,X0),X1) = k2_wellord1(k2_wellord1(sK2,X1),X0) ),
% 3.89/0.99      inference(superposition,[status(thm)],[c_400,c_402]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_16,negated_conjecture,
% 3.89/0.99      ( k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0) ),
% 3.89/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_2152,plain,
% 3.89/0.99      ( k2_wellord1(k2_wellord1(sK2,sK0),sK1) != k2_wellord1(sK2,sK0) ),
% 3.89/0.99      inference(demodulation,[status(thm)],[c_973,c_16]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(contradiction,plain,
% 3.89/0.99      ( $false ),
% 3.89/0.99      inference(minisat,[status(thm)],[c_12562,c_2152]) ).
% 3.89/0.99  
% 3.89/0.99  
% 3.89/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.89/0.99  
% 3.89/0.99  ------                               Statistics
% 3.89/0.99  
% 3.89/0.99  ------ Selected
% 3.89/0.99  
% 3.89/0.99  total_time:                             0.412
% 3.89/0.99  
%------------------------------------------------------------------------------
