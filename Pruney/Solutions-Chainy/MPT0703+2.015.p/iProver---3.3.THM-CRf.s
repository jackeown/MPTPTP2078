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
% DateTime   : Thu Dec  3 11:52:17 EST 2020

% Result     : Theorem 27.57s
% Output     : CNFRefutation 27.57s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 271 expanded)
%              Number of clauses        :   56 (  88 expanded)
%              Number of leaves         :   10 (  54 expanded)
%              Depth                    :   15
%              Number of atoms          :  216 ( 856 expanded)
%              Number of equality atoms :   79 ( 167 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(X0,k2_relat_1(X2))
          & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( r1_tarski(X0,k2_relat_1(X2))
            & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) )
         => r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_tarski(X0,k2_relat_1(X2))
      & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_tarski(X0,k2_relat_1(X2))
      & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f22,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,X1)
        & r1_tarski(X0,k2_relat_1(X2))
        & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(sK0,sK1)
      & r1_tarski(sK0,k2_relat_1(sK2))
      & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ~ r1_tarski(sK0,sK1)
    & r1_tarski(sK0,k2_relat_1(sK2))
    & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f22])).

fof(f35,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k6_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k6_subset_1(X0,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k6_subset_1(X0,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f13])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k6_subset_1(X0,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f36,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f37,plain,(
    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k6_subset_1(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f28,f32])).

fof(f38,plain,(
    r1_tarski(sK0,k2_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f23])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k6_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f27,f32])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k6_subset_1(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(definition_unfolding,[],[f31,f32])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f19])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f44,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f24])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f39,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_14,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_596,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k6_subset_1(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k10_relat_1(X0,k6_subset_1(X1,X2)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_602,plain,
    ( k6_subset_1(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k10_relat_1(X0,k6_subset_1(X1,X2))
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2121,plain,
    ( k6_subset_1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) = k10_relat_1(sK2,k6_subset_1(X0,X1))
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_596,c_602])).

cnf(c_13,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_16,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2510,plain,
    ( k6_subset_1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) = k10_relat_1(sK2,k6_subset_1(X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2121,c_16])).

cnf(c_12,negated_conjecture,
    ( r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_598,plain,
    ( r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | k6_subset_1(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_607,plain,
    ( k6_subset_1(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1138,plain,
    ( k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_598,c_607])).

cnf(c_2518,plain,
    ( k10_relat_1(sK2,k6_subset_1(sK0,sK1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2510,c_1138])).

cnf(c_11,negated_conjecture,
    ( r1_tarski(sK0,k2_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_599,plain,
    ( r1_tarski(sK0,k2_relat_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_605,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k2_xboole_0(X2,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1302,plain,
    ( k6_subset_1(X0,k2_xboole_0(X1,X2)) = k1_xboole_0
    | r1_tarski(X0,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_605,c_607])).

cnf(c_3769,plain,
    ( k6_subset_1(sK0,k2_xboole_0(X0,k2_relat_1(sK2))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_599,c_1302])).

cnf(c_4,plain,
    ( r1_tarski(X0,X1)
    | k6_subset_1(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_606,plain,
    ( k6_subset_1(X0,X1) != k1_xboole_0
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_4041,plain,
    ( r1_tarski(sK0,k2_xboole_0(X0,k2_relat_1(sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3769,c_606])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
    | r1_tarski(k6_subset_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_603,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
    | r1_tarski(k6_subset_1(X0,X1),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_4319,plain,
    ( r1_tarski(k6_subset_1(sK0,X0),k2_relat_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4041,c_603])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_601,plain,
    ( k9_relat_1(X0,k10_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k2_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_7035,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,k6_subset_1(sK0,X0))) = k6_subset_1(sK0,X0)
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4319,c_601])).

cnf(c_863,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,k2_relat_1(X2)))
    | ~ r1_tarski(X0,k2_relat_1(X2)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1025,plain,
    ( r1_tarski(sK0,k2_xboole_0(X0,k2_relat_1(sK2)))
    | ~ r1_tarski(sK0,k2_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_863])).

cnf(c_748,plain,
    ( ~ r1_tarski(X0,k2_xboole_0(X1,k2_relat_1(X2)))
    | r1_tarski(k6_subset_1(X0,X1),k2_relat_1(X2)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1279,plain,
    ( r1_tarski(k6_subset_1(sK0,X0),k2_relat_1(sK2))
    | ~ r1_tarski(sK0,k2_xboole_0(X0,k2_relat_1(sK2))) ),
    inference(instantiation,[status(thm)],[c_748])).

cnf(c_747,plain,
    ( ~ r1_tarski(k6_subset_1(X0,X1),k2_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | k9_relat_1(X2,k10_relat_1(X2,k6_subset_1(X0,X1))) = k6_subset_1(X0,X1) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1397,plain,
    ( ~ r1_tarski(k6_subset_1(sK0,X0),k2_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k9_relat_1(sK2,k10_relat_1(sK2,k6_subset_1(sK0,X0))) = k6_subset_1(sK0,X0) ),
    inference(instantiation,[status(thm)],[c_747])).

cnf(c_70149,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,k6_subset_1(sK0,X0))) = k6_subset_1(sK0,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7035,c_14,c_13,c_11,c_1025,c_1279,c_1397])).

cnf(c_70153,plain,
    ( k9_relat_1(sK2,k1_xboole_0) = k6_subset_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_2518,c_70149])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_608,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1135,plain,
    ( k6_subset_1(X0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_608,c_607])).

cnf(c_2517,plain,
    ( k10_relat_1(sK2,k6_subset_1(X0,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2510,c_1135])).

cnf(c_2522,plain,
    ( k10_relat_1(sK2,k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2517,c_1135])).

cnf(c_6,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_604,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1105,plain,
    ( k9_relat_1(X0,k10_relat_1(X0,k1_xboole_0)) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_604,c_601])).

cnf(c_5078,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,k1_xboole_0)) = k1_xboole_0
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_596,c_1105])).

cnf(c_737,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k9_relat_1(X0,k10_relat_1(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_740,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k9_relat_1(sK2,k10_relat_1(sK2,k1_xboole_0)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_737])).

cnf(c_738,plain,
    ( r1_tarski(k1_xboole_0,k2_relat_1(X0)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_744,plain,
    ( r1_tarski(k1_xboole_0,k2_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_738])).

cnf(c_5530,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,k1_xboole_0)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5078,c_14,c_13,c_740,c_744])).

cnf(c_25928,plain,
    ( k9_relat_1(sK2,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2522,c_5530])).

cnf(c_70191,plain,
    ( k6_subset_1(sK0,sK1) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_70153,c_25928])).

cnf(c_703,plain,
    ( r1_tarski(sK0,sK1)
    | k6_subset_1(sK0,sK1) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_10,negated_conjecture,
    ( ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f39])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_70191,c_703,c_10])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:04:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 27.57/3.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 27.57/3.99  
% 27.57/3.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 27.57/3.99  
% 27.57/3.99  ------  iProver source info
% 27.57/3.99  
% 27.57/3.99  git: date: 2020-06-30 10:37:57 +0100
% 27.57/3.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 27.57/3.99  git: non_committed_changes: false
% 27.57/3.99  git: last_make_outside_of_git: false
% 27.57/3.99  
% 27.57/3.99  ------ 
% 27.57/3.99  ------ Parsing...
% 27.57/3.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 27.57/3.99  
% 27.57/3.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 27.57/3.99  
% 27.57/3.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 27.57/3.99  
% 27.57/3.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.57/3.99  ------ Proving...
% 27.57/3.99  ------ Problem Properties 
% 27.57/3.99  
% 27.57/3.99  
% 27.57/3.99  clauses                                 14
% 27.57/3.99  conjectures                             5
% 27.57/3.99  EPR                                     6
% 27.57/3.99  Horn                                    14
% 27.57/3.99  unary                                   7
% 27.57/3.99  binary                                  4
% 27.57/3.99  lits                                    25
% 27.57/3.99  lits eq                                 5
% 27.57/3.99  fd_pure                                 0
% 27.57/3.99  fd_pseudo                               0
% 27.57/3.99  fd_cond                                 0
% 27.57/3.99  fd_pseudo_cond                          1
% 27.57/3.99  AC symbols                              0
% 27.57/3.99  
% 27.57/3.99  ------ Input Options Time Limit: Unbounded
% 27.57/3.99  
% 27.57/3.99  
% 27.57/3.99  ------ 
% 27.57/3.99  Current options:
% 27.57/3.99  ------ 
% 27.57/3.99  
% 27.57/3.99  
% 27.57/3.99  
% 27.57/3.99  
% 27.57/3.99  ------ Proving...
% 27.57/3.99  
% 27.57/3.99  
% 27.57/3.99  % SZS status Theorem for theBenchmark.p
% 27.57/3.99  
% 27.57/3.99  % SZS output start CNFRefutation for theBenchmark.p
% 27.57/3.99  
% 27.57/3.99  fof(f9,conjecture,(
% 27.57/3.99    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 27.57/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.57/3.99  
% 27.57/3.99  fof(f10,negated_conjecture,(
% 27.57/3.99    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 27.57/3.99    inference(negated_conjecture,[],[f9])).
% 27.57/3.99  
% 27.57/3.99  fof(f17,plain,(
% 27.57/3.99    ? [X0,X1,X2] : ((~r1_tarski(X0,X1) & (r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 27.57/3.99    inference(ennf_transformation,[],[f10])).
% 27.57/3.99  
% 27.57/3.99  fof(f18,plain,(
% 27.57/3.99    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 27.57/3.99    inference(flattening,[],[f17])).
% 27.57/3.99  
% 27.57/3.99  fof(f22,plain,(
% 27.57/3.99    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_tarski(sK0,sK1) & r1_tarski(sK0,k2_relat_1(sK2)) & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 27.57/3.99    introduced(choice_axiom,[])).
% 27.57/3.99  
% 27.57/3.99  fof(f23,plain,(
% 27.57/3.99    ~r1_tarski(sK0,sK1) & r1_tarski(sK0,k2_relat_1(sK2)) & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 27.57/3.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f22])).
% 27.57/3.99  
% 27.57/3.99  fof(f35,plain,(
% 27.57/3.99    v1_relat_1(sK2)),
% 27.57/3.99    inference(cnf_transformation,[],[f23])).
% 27.57/3.99  
% 27.57/3.99  fof(f7,axiom,(
% 27.57/3.99    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k6_subset_1(X0,X1)))),
% 27.57/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.57/3.99  
% 27.57/3.99  fof(f13,plain,(
% 27.57/3.99    ! [X0,X1,X2] : (k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k6_subset_1(X0,X1)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 27.57/3.99    inference(ennf_transformation,[],[f7])).
% 27.57/3.99  
% 27.57/3.99  fof(f14,plain,(
% 27.57/3.99    ! [X0,X1,X2] : (k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k6_subset_1(X0,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 27.57/3.99    inference(flattening,[],[f13])).
% 27.57/3.99  
% 27.57/3.99  fof(f33,plain,(
% 27.57/3.99    ( ! [X2,X0,X1] : (k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k6_subset_1(X0,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 27.57/3.99    inference(cnf_transformation,[],[f14])).
% 27.57/3.99  
% 27.57/3.99  fof(f36,plain,(
% 27.57/3.99    v1_funct_1(sK2)),
% 27.57/3.99    inference(cnf_transformation,[],[f23])).
% 27.57/3.99  
% 27.57/3.99  fof(f37,plain,(
% 27.57/3.99    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),
% 27.57/3.99    inference(cnf_transformation,[],[f23])).
% 27.57/3.99  
% 27.57/3.99  fof(f2,axiom,(
% 27.57/3.99    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 27.57/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.57/3.99  
% 27.57/3.99  fof(f21,plain,(
% 27.57/3.99    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 27.57/3.99    inference(nnf_transformation,[],[f2])).
% 27.57/3.99  
% 27.57/3.99  fof(f28,plain,(
% 27.57/3.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 27.57/3.99    inference(cnf_transformation,[],[f21])).
% 27.57/3.99  
% 27.57/3.99  fof(f6,axiom,(
% 27.57/3.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 27.57/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.57/3.99  
% 27.57/3.99  fof(f32,plain,(
% 27.57/3.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 27.57/3.99    inference(cnf_transformation,[],[f6])).
% 27.57/3.99  
% 27.57/3.99  fof(f40,plain,(
% 27.57/3.99    ( ! [X0,X1] : (k1_xboole_0 = k6_subset_1(X0,X1) | ~r1_tarski(X0,X1)) )),
% 27.57/3.99    inference(definition_unfolding,[],[f28,f32])).
% 27.57/3.99  
% 27.57/3.99  fof(f38,plain,(
% 27.57/3.99    r1_tarski(sK0,k2_relat_1(sK2))),
% 27.57/3.99    inference(cnf_transformation,[],[f23])).
% 27.57/3.99  
% 27.57/3.99  fof(f3,axiom,(
% 27.57/3.99    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 27.57/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.57/3.99  
% 27.57/3.99  fof(f11,plain,(
% 27.57/3.99    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 27.57/3.99    inference(ennf_transformation,[],[f3])).
% 27.57/3.99  
% 27.57/3.99  fof(f29,plain,(
% 27.57/3.99    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 27.57/3.99    inference(cnf_transformation,[],[f11])).
% 27.57/3.99  
% 27.57/3.99  fof(f27,plain,(
% 27.57/3.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 27.57/3.99    inference(cnf_transformation,[],[f21])).
% 27.57/3.99  
% 27.57/3.99  fof(f41,plain,(
% 27.57/3.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k6_subset_1(X0,X1)) )),
% 27.57/3.99    inference(definition_unfolding,[],[f27,f32])).
% 27.57/3.99  
% 27.57/3.99  fof(f5,axiom,(
% 27.57/3.99    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 27.57/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.57/3.99  
% 27.57/3.99  fof(f12,plain,(
% 27.57/3.99    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 27.57/3.99    inference(ennf_transformation,[],[f5])).
% 27.57/3.99  
% 27.57/3.99  fof(f31,plain,(
% 27.57/3.99    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 27.57/3.99    inference(cnf_transformation,[],[f12])).
% 27.57/3.99  
% 27.57/3.99  fof(f42,plain,(
% 27.57/3.99    ( ! [X2,X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 27.57/3.99    inference(definition_unfolding,[],[f31,f32])).
% 27.57/3.99  
% 27.57/3.99  fof(f8,axiom,(
% 27.57/3.99    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 27.57/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.57/3.99  
% 27.57/3.99  fof(f15,plain,(
% 27.57/3.99    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 27.57/3.99    inference(ennf_transformation,[],[f8])).
% 27.57/3.99  
% 27.57/3.99  fof(f16,plain,(
% 27.57/3.99    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 27.57/3.99    inference(flattening,[],[f15])).
% 27.57/3.99  
% 27.57/3.99  fof(f34,plain,(
% 27.57/3.99    ( ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 27.57/3.99    inference(cnf_transformation,[],[f16])).
% 27.57/3.99  
% 27.57/3.99  fof(f1,axiom,(
% 27.57/3.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 27.57/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.57/3.99  
% 27.57/3.99  fof(f19,plain,(
% 27.57/3.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 27.57/3.99    inference(nnf_transformation,[],[f1])).
% 27.57/3.99  
% 27.57/3.99  fof(f20,plain,(
% 27.57/3.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 27.57/3.99    inference(flattening,[],[f19])).
% 27.57/3.99  
% 27.57/3.99  fof(f24,plain,(
% 27.57/3.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 27.57/3.99    inference(cnf_transformation,[],[f20])).
% 27.57/3.99  
% 27.57/3.99  fof(f44,plain,(
% 27.57/3.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 27.57/3.99    inference(equality_resolution,[],[f24])).
% 27.57/3.99  
% 27.57/3.99  fof(f4,axiom,(
% 27.57/3.99    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 27.57/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.57/3.99  
% 27.57/3.99  fof(f30,plain,(
% 27.57/3.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 27.57/3.99    inference(cnf_transformation,[],[f4])).
% 27.57/3.99  
% 27.57/3.99  fof(f39,plain,(
% 27.57/3.99    ~r1_tarski(sK0,sK1)),
% 27.57/3.99    inference(cnf_transformation,[],[f23])).
% 27.57/3.99  
% 27.57/3.99  cnf(c_14,negated_conjecture,
% 27.57/3.99      ( v1_relat_1(sK2) ),
% 27.57/3.99      inference(cnf_transformation,[],[f35]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_596,plain,
% 27.57/3.99      ( v1_relat_1(sK2) = iProver_top ),
% 27.57/3.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_8,plain,
% 27.57/3.99      ( ~ v1_relat_1(X0)
% 27.57/3.99      | ~ v1_funct_1(X0)
% 27.57/3.99      | k6_subset_1(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k10_relat_1(X0,k6_subset_1(X1,X2)) ),
% 27.57/3.99      inference(cnf_transformation,[],[f33]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_602,plain,
% 27.57/3.99      ( k6_subset_1(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k10_relat_1(X0,k6_subset_1(X1,X2))
% 27.57/3.99      | v1_relat_1(X0) != iProver_top
% 27.57/3.99      | v1_funct_1(X0) != iProver_top ),
% 27.57/3.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_2121,plain,
% 27.57/3.99      ( k6_subset_1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) = k10_relat_1(sK2,k6_subset_1(X0,X1))
% 27.57/3.99      | v1_funct_1(sK2) != iProver_top ),
% 27.57/3.99      inference(superposition,[status(thm)],[c_596,c_602]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_13,negated_conjecture,
% 27.57/3.99      ( v1_funct_1(sK2) ),
% 27.57/3.99      inference(cnf_transformation,[],[f36]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_16,plain,
% 27.57/3.99      ( v1_funct_1(sK2) = iProver_top ),
% 27.57/3.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_2510,plain,
% 27.57/3.99      ( k6_subset_1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) = k10_relat_1(sK2,k6_subset_1(X0,X1)) ),
% 27.57/3.99      inference(global_propositional_subsumption,
% 27.57/3.99                [status(thm)],
% 27.57/3.99                [c_2121,c_16]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_12,negated_conjecture,
% 27.57/3.99      ( r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
% 27.57/3.99      inference(cnf_transformation,[],[f37]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_598,plain,
% 27.57/3.99      ( r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) = iProver_top ),
% 27.57/3.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_3,plain,
% 27.57/3.99      ( ~ r1_tarski(X0,X1) | k6_subset_1(X0,X1) = k1_xboole_0 ),
% 27.57/3.99      inference(cnf_transformation,[],[f40]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_607,plain,
% 27.57/3.99      ( k6_subset_1(X0,X1) = k1_xboole_0
% 27.57/3.99      | r1_tarski(X0,X1) != iProver_top ),
% 27.57/3.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_1138,plain,
% 27.57/3.99      ( k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) = k1_xboole_0 ),
% 27.57/3.99      inference(superposition,[status(thm)],[c_598,c_607]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_2518,plain,
% 27.57/3.99      ( k10_relat_1(sK2,k6_subset_1(sK0,sK1)) = k1_xboole_0 ),
% 27.57/3.99      inference(superposition,[status(thm)],[c_2510,c_1138]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_11,negated_conjecture,
% 27.57/3.99      ( r1_tarski(sK0,k2_relat_1(sK2)) ),
% 27.57/3.99      inference(cnf_transformation,[],[f38]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_599,plain,
% 27.57/3.99      ( r1_tarski(sK0,k2_relat_1(sK2)) = iProver_top ),
% 27.57/3.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_5,plain,
% 27.57/3.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X0,k2_xboole_0(X2,X1)) ),
% 27.57/3.99      inference(cnf_transformation,[],[f29]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_605,plain,
% 27.57/3.99      ( r1_tarski(X0,X1) != iProver_top
% 27.57/3.99      | r1_tarski(X0,k2_xboole_0(X2,X1)) = iProver_top ),
% 27.57/3.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_1302,plain,
% 27.57/3.99      ( k6_subset_1(X0,k2_xboole_0(X1,X2)) = k1_xboole_0
% 27.57/3.99      | r1_tarski(X0,X2) != iProver_top ),
% 27.57/3.99      inference(superposition,[status(thm)],[c_605,c_607]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_3769,plain,
% 27.57/3.99      ( k6_subset_1(sK0,k2_xboole_0(X0,k2_relat_1(sK2))) = k1_xboole_0 ),
% 27.57/3.99      inference(superposition,[status(thm)],[c_599,c_1302]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_4,plain,
% 27.57/3.99      ( r1_tarski(X0,X1) | k6_subset_1(X0,X1) != k1_xboole_0 ),
% 27.57/3.99      inference(cnf_transformation,[],[f41]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_606,plain,
% 27.57/3.99      ( k6_subset_1(X0,X1) != k1_xboole_0
% 27.57/3.99      | r1_tarski(X0,X1) = iProver_top ),
% 27.57/3.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_4041,plain,
% 27.57/3.99      ( r1_tarski(sK0,k2_xboole_0(X0,k2_relat_1(sK2))) = iProver_top ),
% 27.57/3.99      inference(superposition,[status(thm)],[c_3769,c_606]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_7,plain,
% 27.57/3.99      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
% 27.57/3.99      | r1_tarski(k6_subset_1(X0,X1),X2) ),
% 27.57/3.99      inference(cnf_transformation,[],[f42]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_603,plain,
% 27.57/3.99      ( r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
% 27.57/3.99      | r1_tarski(k6_subset_1(X0,X1),X2) = iProver_top ),
% 27.57/3.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_4319,plain,
% 27.57/3.99      ( r1_tarski(k6_subset_1(sK0,X0),k2_relat_1(sK2)) = iProver_top ),
% 27.57/3.99      inference(superposition,[status(thm)],[c_4041,c_603]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_9,plain,
% 27.57/3.99      ( ~ r1_tarski(X0,k2_relat_1(X1))
% 27.57/3.99      | ~ v1_relat_1(X1)
% 27.57/3.99      | ~ v1_funct_1(X1)
% 27.57/3.99      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ),
% 27.57/3.99      inference(cnf_transformation,[],[f34]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_601,plain,
% 27.57/3.99      ( k9_relat_1(X0,k10_relat_1(X0,X1)) = X1
% 27.57/3.99      | r1_tarski(X1,k2_relat_1(X0)) != iProver_top
% 27.57/3.99      | v1_relat_1(X0) != iProver_top
% 27.57/3.99      | v1_funct_1(X0) != iProver_top ),
% 27.57/3.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_7035,plain,
% 27.57/3.99      ( k9_relat_1(sK2,k10_relat_1(sK2,k6_subset_1(sK0,X0))) = k6_subset_1(sK0,X0)
% 27.57/3.99      | v1_relat_1(sK2) != iProver_top
% 27.57/3.99      | v1_funct_1(sK2) != iProver_top ),
% 27.57/3.99      inference(superposition,[status(thm)],[c_4319,c_601]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_863,plain,
% 27.57/3.99      ( r1_tarski(X0,k2_xboole_0(X1,k2_relat_1(X2)))
% 27.57/3.99      | ~ r1_tarski(X0,k2_relat_1(X2)) ),
% 27.57/3.99      inference(instantiation,[status(thm)],[c_5]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_1025,plain,
% 27.57/3.99      ( r1_tarski(sK0,k2_xboole_0(X0,k2_relat_1(sK2)))
% 27.57/3.99      | ~ r1_tarski(sK0,k2_relat_1(sK2)) ),
% 27.57/3.99      inference(instantiation,[status(thm)],[c_863]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_748,plain,
% 27.57/3.99      ( ~ r1_tarski(X0,k2_xboole_0(X1,k2_relat_1(X2)))
% 27.57/3.99      | r1_tarski(k6_subset_1(X0,X1),k2_relat_1(X2)) ),
% 27.57/3.99      inference(instantiation,[status(thm)],[c_7]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_1279,plain,
% 27.57/3.99      ( r1_tarski(k6_subset_1(sK0,X0),k2_relat_1(sK2))
% 27.57/3.99      | ~ r1_tarski(sK0,k2_xboole_0(X0,k2_relat_1(sK2))) ),
% 27.57/3.99      inference(instantiation,[status(thm)],[c_748]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_747,plain,
% 27.57/3.99      ( ~ r1_tarski(k6_subset_1(X0,X1),k2_relat_1(X2))
% 27.57/3.99      | ~ v1_relat_1(X2)
% 27.57/3.99      | ~ v1_funct_1(X2)
% 27.57/3.99      | k9_relat_1(X2,k10_relat_1(X2,k6_subset_1(X0,X1))) = k6_subset_1(X0,X1) ),
% 27.57/3.99      inference(instantiation,[status(thm)],[c_9]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_1397,plain,
% 27.57/3.99      ( ~ r1_tarski(k6_subset_1(sK0,X0),k2_relat_1(sK2))
% 27.57/3.99      | ~ v1_relat_1(sK2)
% 27.57/3.99      | ~ v1_funct_1(sK2)
% 27.57/3.99      | k9_relat_1(sK2,k10_relat_1(sK2,k6_subset_1(sK0,X0))) = k6_subset_1(sK0,X0) ),
% 27.57/3.99      inference(instantiation,[status(thm)],[c_747]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_70149,plain,
% 27.57/3.99      ( k9_relat_1(sK2,k10_relat_1(sK2,k6_subset_1(sK0,X0))) = k6_subset_1(sK0,X0) ),
% 27.57/3.99      inference(global_propositional_subsumption,
% 27.57/3.99                [status(thm)],
% 27.57/3.99                [c_7035,c_14,c_13,c_11,c_1025,c_1279,c_1397]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_70153,plain,
% 27.57/3.99      ( k9_relat_1(sK2,k1_xboole_0) = k6_subset_1(sK0,sK1) ),
% 27.57/3.99      inference(superposition,[status(thm)],[c_2518,c_70149]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_2,plain,
% 27.57/3.99      ( r1_tarski(X0,X0) ),
% 27.57/3.99      inference(cnf_transformation,[],[f44]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_608,plain,
% 27.57/3.99      ( r1_tarski(X0,X0) = iProver_top ),
% 27.57/3.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_1135,plain,
% 27.57/3.99      ( k6_subset_1(X0,X0) = k1_xboole_0 ),
% 27.57/3.99      inference(superposition,[status(thm)],[c_608,c_607]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_2517,plain,
% 27.57/3.99      ( k10_relat_1(sK2,k6_subset_1(X0,X0)) = k1_xboole_0 ),
% 27.57/3.99      inference(superposition,[status(thm)],[c_2510,c_1135]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_2522,plain,
% 27.57/3.99      ( k10_relat_1(sK2,k1_xboole_0) = k1_xboole_0 ),
% 27.57/3.99      inference(light_normalisation,[status(thm)],[c_2517,c_1135]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_6,plain,
% 27.57/3.99      ( r1_tarski(k1_xboole_0,X0) ),
% 27.57/3.99      inference(cnf_transformation,[],[f30]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_604,plain,
% 27.57/3.99      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 27.57/3.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_1105,plain,
% 27.57/3.99      ( k9_relat_1(X0,k10_relat_1(X0,k1_xboole_0)) = k1_xboole_0
% 27.57/3.99      | v1_relat_1(X0) != iProver_top
% 27.57/3.99      | v1_funct_1(X0) != iProver_top ),
% 27.57/3.99      inference(superposition,[status(thm)],[c_604,c_601]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_5078,plain,
% 27.57/3.99      ( k9_relat_1(sK2,k10_relat_1(sK2,k1_xboole_0)) = k1_xboole_0
% 27.57/3.99      | v1_funct_1(sK2) != iProver_top ),
% 27.57/3.99      inference(superposition,[status(thm)],[c_596,c_1105]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_737,plain,
% 27.57/3.99      ( ~ r1_tarski(k1_xboole_0,k2_relat_1(X0))
% 27.57/3.99      | ~ v1_relat_1(X0)
% 27.57/3.99      | ~ v1_funct_1(X0)
% 27.57/3.99      | k9_relat_1(X0,k10_relat_1(X0,k1_xboole_0)) = k1_xboole_0 ),
% 27.57/3.99      inference(instantiation,[status(thm)],[c_9]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_740,plain,
% 27.57/3.99      ( ~ r1_tarski(k1_xboole_0,k2_relat_1(sK2))
% 27.57/3.99      | ~ v1_relat_1(sK2)
% 27.57/3.99      | ~ v1_funct_1(sK2)
% 27.57/3.99      | k9_relat_1(sK2,k10_relat_1(sK2,k1_xboole_0)) = k1_xboole_0 ),
% 27.57/3.99      inference(instantiation,[status(thm)],[c_737]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_738,plain,
% 27.57/3.99      ( r1_tarski(k1_xboole_0,k2_relat_1(X0)) ),
% 27.57/3.99      inference(instantiation,[status(thm)],[c_6]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_744,plain,
% 27.57/3.99      ( r1_tarski(k1_xboole_0,k2_relat_1(sK2)) ),
% 27.57/3.99      inference(instantiation,[status(thm)],[c_738]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_5530,plain,
% 27.57/3.99      ( k9_relat_1(sK2,k10_relat_1(sK2,k1_xboole_0)) = k1_xboole_0 ),
% 27.57/3.99      inference(global_propositional_subsumption,
% 27.57/3.99                [status(thm)],
% 27.57/3.99                [c_5078,c_14,c_13,c_740,c_744]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_25928,plain,
% 27.57/3.99      ( k9_relat_1(sK2,k1_xboole_0) = k1_xboole_0 ),
% 27.57/3.99      inference(demodulation,[status(thm)],[c_2522,c_5530]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_70191,plain,
% 27.57/3.99      ( k6_subset_1(sK0,sK1) = k1_xboole_0 ),
% 27.57/3.99      inference(light_normalisation,[status(thm)],[c_70153,c_25928]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_703,plain,
% 27.57/3.99      ( r1_tarski(sK0,sK1) | k6_subset_1(sK0,sK1) != k1_xboole_0 ),
% 27.57/3.99      inference(instantiation,[status(thm)],[c_4]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_10,negated_conjecture,
% 27.57/3.99      ( ~ r1_tarski(sK0,sK1) ),
% 27.57/3.99      inference(cnf_transformation,[],[f39]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(contradiction,plain,
% 27.57/3.99      ( $false ),
% 27.57/3.99      inference(minisat,[status(thm)],[c_70191,c_703,c_10]) ).
% 27.57/3.99  
% 27.57/3.99  
% 27.57/3.99  % SZS output end CNFRefutation for theBenchmark.p
% 27.57/3.99  
% 27.57/3.99  ------                               Statistics
% 27.57/3.99  
% 27.57/3.99  ------ Selected
% 27.57/3.99  
% 27.57/3.99  total_time:                             3.044
% 27.57/3.99  
%------------------------------------------------------------------------------
