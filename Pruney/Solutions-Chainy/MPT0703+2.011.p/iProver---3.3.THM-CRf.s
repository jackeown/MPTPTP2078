%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:52:16 EST 2020

% Result     : Theorem 27.63s
% Output     : CNFRefutation 27.63s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 298 expanded)
%              Number of clauses        :   62 (  93 expanded)
%              Number of leaves         :   16 (  73 expanded)
%              Depth                    :   13
%              Number of atoms          :  237 ( 880 expanded)
%              Number of equality atoms :  112 ( 211 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(X0,k2_relat_1(X2))
          & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( r1_tarski(X0,k2_relat_1(X2))
            & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) )
         => r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_tarski(X0,k2_relat_1(X2))
      & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_tarski(X0,k2_relat_1(X2))
      & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f25,plain,
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

fof(f26,plain,
    ( ~ r1_tarski(sK0,sK1)
    & r1_tarski(sK0,k2_relat_1(sK2))
    & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f25])).

fof(f41,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k6_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k6_subset_1(X0,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k6_subset_1(X0,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k6_subset_1(X0,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f42,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f10,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f46,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k6_subset_1(X0,k6_subset_1(X0,X1)) ),
    inference(definition_unfolding,[],[f34,f37,f37])).

fof(f47,plain,(
    ! [X0,X1] : k6_subset_1(X0,k6_subset_1(X0,X1)) = k6_subset_1(X1,k6_subset_1(X1,X0)) ),
    inference(definition_unfolding,[],[f27,f46,f46])).

fof(f8,axiom,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f8])).

fof(f52,plain,(
    ! [X0] : k1_xboole_0 = k6_subset_1(k1_xboole_0,X0) ),
    inference(definition_unfolding,[],[f35,f37])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f50,plain,(
    ! [X0] : k6_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f32,f37])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f43,plain,(
    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f26])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k6_subset_1(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f29,f37])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k6_subset_1(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(definition_unfolding,[],[f33,f37])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k6_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f28,f37])).

fof(f45,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f44,plain,(
    r1_tarski(sK0,k2_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_148,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_98811,plain,
    ( k9_relat_1(sK2,X0) != X1
    | k1_xboole_0 != X1
    | k1_xboole_0 = k9_relat_1(sK2,X0) ),
    inference(instantiation,[status(thm)],[c_148])).

cnf(c_98812,plain,
    ( k9_relat_1(sK2,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k9_relat_1(sK2,k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_98811])).

cnf(c_15,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_460,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k6_subset_1(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k10_relat_1(X0,k6_subset_1(X1,X2)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_466,plain,
    ( k6_subset_1(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k10_relat_1(X0,k6_subset_1(X1,X2))
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1531,plain,
    ( k6_subset_1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) = k10_relat_1(sK2,k6_subset_1(X0,X1))
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_460,c_466])).

cnf(c_14,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_600,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k6_subset_1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) = k10_relat_1(sK2,k6_subset_1(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_2093,plain,
    ( k6_subset_1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) = k10_relat_1(sK2,k6_subset_1(X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1531,c_15,c_14,c_600])).

cnf(c_0,plain,
    ( k6_subset_1(X0,k6_subset_1(X0,X1)) = k6_subset_1(X1,k6_subset_1(X1,X0)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_7,plain,
    ( k6_subset_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_830,plain,
    ( k6_subset_1(X0,k6_subset_1(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_7])).

cnf(c_5,plain,
    ( k6_subset_1(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_833,plain,
    ( k6_subset_1(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_830,c_5])).

cnf(c_2105,plain,
    ( k10_relat_1(sK2,k6_subset_1(X0,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2093,c_833])).

cnf(c_2110,plain,
    ( k10_relat_1(sK2,k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2105,c_833])).

cnf(c_4,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_468,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_465,plain,
    ( k9_relat_1(X0,k10_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k2_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_805,plain,
    ( k9_relat_1(X0,k10_relat_1(X0,k1_xboole_0)) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_468,c_465])).

cnf(c_3819,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,k1_xboole_0)) = k1_xboole_0
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_460,c_805])).

cnf(c_590,plain,
    ( ~ r1_tarski(X0,k2_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0 ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_592,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k9_relat_1(sK2,k10_relat_1(sK2,k1_xboole_0)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_590])).

cnf(c_680,plain,
    ( r1_tarski(k1_xboole_0,k2_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_4342,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,k1_xboole_0)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3819,c_15,c_14,c_592,c_680])).

cnf(c_23834,plain,
    ( k9_relat_1(sK2,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2110,c_4342])).

cnf(c_155,plain,
    ( X0 != X1
    | k9_relat_1(X2,X0) = k9_relat_1(X2,X1) ),
    theory(equality)).

cnf(c_19979,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,k6_subset_1(sK0,sK1))) = k9_relat_1(sK2,X0)
    | k10_relat_1(sK2,k6_subset_1(sK0,sK1)) != X0 ),
    inference(instantiation,[status(thm)],[c_155])).

cnf(c_19981,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,k6_subset_1(sK0,sK1))) = k9_relat_1(sK2,k1_xboole_0)
    | k10_relat_1(sK2,k6_subset_1(sK0,sK1)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_19979])).

cnf(c_6371,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,k6_subset_1(sK0,sK1))) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k9_relat_1(sK2,k10_relat_1(sK2,k6_subset_1(sK0,sK1))) ),
    inference(instantiation,[status(thm)],[c_148])).

cnf(c_19978,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,k6_subset_1(sK0,sK1))) != k9_relat_1(sK2,X0)
    | k1_xboole_0 != k9_relat_1(sK2,X0)
    | k1_xboole_0 = k9_relat_1(sK2,k10_relat_1(sK2,k6_subset_1(sK0,sK1))) ),
    inference(instantiation,[status(thm)],[c_6371])).

cnf(c_19980,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,k6_subset_1(sK0,sK1))) != k9_relat_1(sK2,k1_xboole_0)
    | k1_xboole_0 = k9_relat_1(sK2,k10_relat_1(sK2,k6_subset_1(sK0,sK1)))
    | k1_xboole_0 != k9_relat_1(sK2,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_19978])).

cnf(c_629,plain,
    ( k6_subset_1(sK0,sK1) != X0
    | k6_subset_1(sK0,sK1) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_148])).

cnf(c_5830,plain,
    ( k6_subset_1(sK0,sK1) != k9_relat_1(sK2,k10_relat_1(sK2,k6_subset_1(sK0,sK1)))
    | k6_subset_1(sK0,sK1) = k1_xboole_0
    | k1_xboole_0 != k9_relat_1(sK2,k10_relat_1(sK2,k6_subset_1(sK0,sK1))) ),
    inference(instantiation,[status(thm)],[c_629])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_867,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,k2_relat_1(sK2)))
    | ~ r1_tarski(X0,k2_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2263,plain,
    ( r1_tarski(sK0,k2_xboole_0(sK1,k2_relat_1(sK2)))
    | ~ r1_tarski(sK0,k2_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_867])).

cnf(c_13,negated_conjecture,
    ( r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_462,plain,
    ( r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | k6_subset_1(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_471,plain,
    ( k6_subset_1(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1653,plain,
    ( k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_462,c_471])).

cnf(c_2106,plain,
    ( k10_relat_1(sK2,k6_subset_1(sK0,sK1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2093,c_1653])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
    | r1_tarski(k6_subset_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_686,plain,
    ( ~ r1_tarski(X0,k2_xboole_0(X1,k2_relat_1(sK2)))
    | r1_tarski(k6_subset_1(X0,X1),k2_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2016,plain,
    ( r1_tarski(k6_subset_1(sK0,sK1),k2_relat_1(sK2))
    | ~ r1_tarski(sK0,k2_xboole_0(sK1,k2_relat_1(sK2))) ),
    inference(instantiation,[status(thm)],[c_686])).

cnf(c_685,plain,
    ( ~ r1_tarski(k6_subset_1(X0,X1),k2_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k9_relat_1(sK2,k10_relat_1(sK2,k6_subset_1(X0,X1))) = k6_subset_1(X0,X1) ),
    inference(instantiation,[status(thm)],[c_590])).

cnf(c_1455,plain,
    ( ~ r1_tarski(k6_subset_1(sK0,sK1),k2_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k9_relat_1(sK2,k10_relat_1(sK2,k6_subset_1(sK0,sK1))) = k6_subset_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_685])).

cnf(c_770,plain,
    ( X0 != X1
    | k6_subset_1(sK0,sK1) != X1
    | k6_subset_1(sK0,sK1) = X0 ),
    inference(instantiation,[status(thm)],[c_148])).

cnf(c_966,plain,
    ( X0 != k6_subset_1(sK0,sK1)
    | k6_subset_1(sK0,sK1) = X0
    | k6_subset_1(sK0,sK1) != k6_subset_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_770])).

cnf(c_1454,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,k6_subset_1(sK0,sK1))) != k6_subset_1(sK0,sK1)
    | k6_subset_1(sK0,sK1) = k9_relat_1(sK2,k10_relat_1(sK2,k6_subset_1(sK0,sK1)))
    | k6_subset_1(sK0,sK1) != k6_subset_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_966])).

cnf(c_147,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_769,plain,
    ( k6_subset_1(sK0,sK1) = k6_subset_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_147])).

cnf(c_2,plain,
    ( r1_tarski(X0,X1)
    | k6_subset_1(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_561,plain,
    ( r1_tarski(sK0,sK1)
    | k6_subset_1(sK0,sK1) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_166,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_147])).

cnf(c_11,negated_conjecture,
    ( ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_12,negated_conjecture,
    ( r1_tarski(sK0,k2_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f44])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_98812,c_23834,c_19981,c_19980,c_5830,c_2263,c_2106,c_2016,c_1455,c_1454,c_769,c_561,c_166,c_11,c_12,c_14,c_15])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 16:36:26 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  % Running in FOF mode
% 27.63/4.03  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 27.63/4.03  
% 27.63/4.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 27.63/4.03  
% 27.63/4.03  ------  iProver source info
% 27.63/4.03  
% 27.63/4.03  git: date: 2020-06-30 10:37:57 +0100
% 27.63/4.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 27.63/4.03  git: non_committed_changes: false
% 27.63/4.03  git: last_make_outside_of_git: false
% 27.63/4.03  
% 27.63/4.03  ------ 
% 27.63/4.03  ------ Parsing...
% 27.63/4.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 27.63/4.03  
% 27.63/4.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 27.63/4.03  
% 27.63/4.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 27.63/4.03  
% 27.63/4.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.63/4.03  ------ Proving...
% 27.63/4.03  ------ Problem Properties 
% 27.63/4.03  
% 27.63/4.03  
% 27.63/4.03  clauses                                 16
% 27.63/4.03  conjectures                             5
% 27.63/4.03  EPR                                     4
% 27.63/4.03  Horn                                    16
% 27.63/4.03  unary                                   10
% 27.63/4.03  binary                                  4
% 27.63/4.03  lits                                    25
% 27.63/4.03  lits eq                                 8
% 27.63/4.03  fd_pure                                 0
% 27.63/4.03  fd_pseudo                               0
% 27.63/4.03  fd_cond                                 0
% 27.63/4.03  fd_pseudo_cond                          0
% 27.63/4.03  AC symbols                              0
% 27.63/4.03  
% 27.63/4.03  ------ Input Options Time Limit: Unbounded
% 27.63/4.03  
% 27.63/4.03  
% 27.63/4.03  ------ 
% 27.63/4.03  Current options:
% 27.63/4.03  ------ 
% 27.63/4.03  
% 27.63/4.03  
% 27.63/4.03  
% 27.63/4.03  
% 27.63/4.03  ------ Proving...
% 27.63/4.03  
% 27.63/4.03  
% 27.63/4.03  % SZS status Theorem for theBenchmark.p
% 27.63/4.03  
% 27.63/4.03  % SZS output start CNFRefutation for theBenchmark.p
% 27.63/4.03  
% 27.63/4.03  fof(f14,conjecture,(
% 27.63/4.03    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 27.63/4.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.63/4.03  
% 27.63/4.03  fof(f15,negated_conjecture,(
% 27.63/4.03    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 27.63/4.03    inference(negated_conjecture,[],[f14])).
% 27.63/4.03  
% 27.63/4.03  fof(f22,plain,(
% 27.63/4.03    ? [X0,X1,X2] : ((~r1_tarski(X0,X1) & (r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 27.63/4.03    inference(ennf_transformation,[],[f15])).
% 27.63/4.03  
% 27.63/4.03  fof(f23,plain,(
% 27.63/4.03    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 27.63/4.03    inference(flattening,[],[f22])).
% 27.63/4.03  
% 27.63/4.03  fof(f25,plain,(
% 27.63/4.03    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_tarski(sK0,sK1) & r1_tarski(sK0,k2_relat_1(sK2)) & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 27.63/4.03    introduced(choice_axiom,[])).
% 27.63/4.03  
% 27.63/4.03  fof(f26,plain,(
% 27.63/4.03    ~r1_tarski(sK0,sK1) & r1_tarski(sK0,k2_relat_1(sK2)) & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 27.63/4.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f25])).
% 27.63/4.03  
% 27.63/4.03  fof(f41,plain,(
% 27.63/4.03    v1_relat_1(sK2)),
% 27.63/4.03    inference(cnf_transformation,[],[f26])).
% 27.63/4.03  
% 27.63/4.03  fof(f12,axiom,(
% 27.63/4.03    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k6_subset_1(X0,X1)))),
% 27.63/4.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.63/4.03  
% 27.63/4.03  fof(f18,plain,(
% 27.63/4.03    ! [X0,X1,X2] : (k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k6_subset_1(X0,X1)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 27.63/4.03    inference(ennf_transformation,[],[f12])).
% 27.63/4.03  
% 27.63/4.03  fof(f19,plain,(
% 27.63/4.03    ! [X0,X1,X2] : (k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k6_subset_1(X0,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 27.63/4.03    inference(flattening,[],[f18])).
% 27.63/4.03  
% 27.63/4.03  fof(f39,plain,(
% 27.63/4.03    ( ! [X2,X0,X1] : (k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k6_subset_1(X0,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 27.63/4.03    inference(cnf_transformation,[],[f19])).
% 27.63/4.03  
% 27.63/4.03  fof(f42,plain,(
% 27.63/4.03    v1_funct_1(sK2)),
% 27.63/4.03    inference(cnf_transformation,[],[f26])).
% 27.63/4.03  
% 27.63/4.03  fof(f1,axiom,(
% 27.63/4.03    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 27.63/4.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.63/4.03  
% 27.63/4.03  fof(f27,plain,(
% 27.63/4.03    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 27.63/4.03    inference(cnf_transformation,[],[f1])).
% 27.63/4.03  
% 27.63/4.03  fof(f7,axiom,(
% 27.63/4.03    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 27.63/4.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.63/4.03  
% 27.63/4.03  fof(f34,plain,(
% 27.63/4.03    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 27.63/4.03    inference(cnf_transformation,[],[f7])).
% 27.63/4.03  
% 27.63/4.03  fof(f10,axiom,(
% 27.63/4.03    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 27.63/4.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.63/4.03  
% 27.63/4.03  fof(f37,plain,(
% 27.63/4.03    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 27.63/4.03    inference(cnf_transformation,[],[f10])).
% 27.63/4.03  
% 27.63/4.03  fof(f46,plain,(
% 27.63/4.03    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k6_subset_1(X0,k6_subset_1(X0,X1))) )),
% 27.63/4.03    inference(definition_unfolding,[],[f34,f37,f37])).
% 27.63/4.03  
% 27.63/4.03  fof(f47,plain,(
% 27.63/4.03    ( ! [X0,X1] : (k6_subset_1(X0,k6_subset_1(X0,X1)) = k6_subset_1(X1,k6_subset_1(X1,X0))) )),
% 27.63/4.03    inference(definition_unfolding,[],[f27,f46,f46])).
% 27.63/4.03  
% 27.63/4.03  fof(f8,axiom,(
% 27.63/4.03    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0),
% 27.63/4.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.63/4.03  
% 27.63/4.03  fof(f35,plain,(
% 27.63/4.03    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0) )),
% 27.63/4.03    inference(cnf_transformation,[],[f8])).
% 27.63/4.03  
% 27.63/4.03  fof(f52,plain,(
% 27.63/4.03    ( ! [X0] : (k1_xboole_0 = k6_subset_1(k1_xboole_0,X0)) )),
% 27.63/4.03    inference(definition_unfolding,[],[f35,f37])).
% 27.63/4.03  
% 27.63/4.03  fof(f5,axiom,(
% 27.63/4.03    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 27.63/4.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.63/4.03  
% 27.63/4.03  fof(f32,plain,(
% 27.63/4.03    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 27.63/4.03    inference(cnf_transformation,[],[f5])).
% 27.63/4.03  
% 27.63/4.03  fof(f50,plain,(
% 27.63/4.03    ( ! [X0] : (k6_subset_1(X0,k1_xboole_0) = X0) )),
% 27.63/4.03    inference(definition_unfolding,[],[f32,f37])).
% 27.63/4.03  
% 27.63/4.03  fof(f4,axiom,(
% 27.63/4.03    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 27.63/4.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.63/4.03  
% 27.63/4.03  fof(f31,plain,(
% 27.63/4.03    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 27.63/4.03    inference(cnf_transformation,[],[f4])).
% 27.63/4.03  
% 27.63/4.03  fof(f13,axiom,(
% 27.63/4.03    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 27.63/4.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.63/4.03  
% 27.63/4.03  fof(f20,plain,(
% 27.63/4.03    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 27.63/4.03    inference(ennf_transformation,[],[f13])).
% 27.63/4.03  
% 27.63/4.03  fof(f21,plain,(
% 27.63/4.03    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 27.63/4.03    inference(flattening,[],[f20])).
% 27.63/4.03  
% 27.63/4.03  fof(f40,plain,(
% 27.63/4.03    ( ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 27.63/4.03    inference(cnf_transformation,[],[f21])).
% 27.63/4.03  
% 27.63/4.03  fof(f3,axiom,(
% 27.63/4.03    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 27.63/4.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.63/4.03  
% 27.63/4.03  fof(f16,plain,(
% 27.63/4.03    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 27.63/4.03    inference(ennf_transformation,[],[f3])).
% 27.63/4.03  
% 27.63/4.03  fof(f30,plain,(
% 27.63/4.03    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 27.63/4.03    inference(cnf_transformation,[],[f16])).
% 27.63/4.03  
% 27.63/4.03  fof(f43,plain,(
% 27.63/4.03    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),
% 27.63/4.03    inference(cnf_transformation,[],[f26])).
% 27.63/4.03  
% 27.63/4.03  fof(f2,axiom,(
% 27.63/4.03    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 27.63/4.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.63/4.03  
% 27.63/4.03  fof(f24,plain,(
% 27.63/4.03    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 27.63/4.03    inference(nnf_transformation,[],[f2])).
% 27.63/4.03  
% 27.63/4.03  fof(f29,plain,(
% 27.63/4.03    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 27.63/4.03    inference(cnf_transformation,[],[f24])).
% 27.63/4.03  
% 27.63/4.03  fof(f48,plain,(
% 27.63/4.03    ( ! [X0,X1] : (k1_xboole_0 = k6_subset_1(X0,X1) | ~r1_tarski(X0,X1)) )),
% 27.63/4.03    inference(definition_unfolding,[],[f29,f37])).
% 27.63/4.03  
% 27.63/4.03  fof(f6,axiom,(
% 27.63/4.03    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 27.63/4.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.63/4.03  
% 27.63/4.03  fof(f17,plain,(
% 27.63/4.03    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 27.63/4.03    inference(ennf_transformation,[],[f6])).
% 27.63/4.03  
% 27.63/4.03  fof(f33,plain,(
% 27.63/4.03    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 27.63/4.03    inference(cnf_transformation,[],[f17])).
% 27.63/4.03  
% 27.63/4.03  fof(f51,plain,(
% 27.63/4.03    ( ! [X2,X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 27.63/4.03    inference(definition_unfolding,[],[f33,f37])).
% 27.63/4.03  
% 27.63/4.03  fof(f28,plain,(
% 27.63/4.03    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 27.63/4.03    inference(cnf_transformation,[],[f24])).
% 27.63/4.03  
% 27.63/4.03  fof(f49,plain,(
% 27.63/4.03    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k6_subset_1(X0,X1)) )),
% 27.63/4.03    inference(definition_unfolding,[],[f28,f37])).
% 27.63/4.03  
% 27.63/4.03  fof(f45,plain,(
% 27.63/4.03    ~r1_tarski(sK0,sK1)),
% 27.63/4.03    inference(cnf_transformation,[],[f26])).
% 27.63/4.03  
% 27.63/4.03  fof(f44,plain,(
% 27.63/4.03    r1_tarski(sK0,k2_relat_1(sK2))),
% 27.63/4.03    inference(cnf_transformation,[],[f26])).
% 27.63/4.03  
% 27.63/4.03  cnf(c_148,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 27.63/4.03  
% 27.63/4.03  cnf(c_98811,plain,
% 27.63/4.03      ( k9_relat_1(sK2,X0) != X1
% 27.63/4.03      | k1_xboole_0 != X1
% 27.63/4.03      | k1_xboole_0 = k9_relat_1(sK2,X0) ),
% 27.63/4.03      inference(instantiation,[status(thm)],[c_148]) ).
% 27.63/4.03  
% 27.63/4.03  cnf(c_98812,plain,
% 27.63/4.03      ( k9_relat_1(sK2,k1_xboole_0) != k1_xboole_0
% 27.63/4.03      | k1_xboole_0 = k9_relat_1(sK2,k1_xboole_0)
% 27.63/4.03      | k1_xboole_0 != k1_xboole_0 ),
% 27.63/4.03      inference(instantiation,[status(thm)],[c_98811]) ).
% 27.63/4.03  
% 27.63/4.03  cnf(c_15,negated_conjecture,
% 27.63/4.03      ( v1_relat_1(sK2) ),
% 27.63/4.03      inference(cnf_transformation,[],[f41]) ).
% 27.63/4.03  
% 27.63/4.03  cnf(c_460,plain,
% 27.63/4.03      ( v1_relat_1(sK2) = iProver_top ),
% 27.63/4.03      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 27.63/4.03  
% 27.63/4.03  cnf(c_9,plain,
% 27.63/4.03      ( ~ v1_relat_1(X0)
% 27.63/4.03      | ~ v1_funct_1(X0)
% 27.63/4.03      | k6_subset_1(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k10_relat_1(X0,k6_subset_1(X1,X2)) ),
% 27.63/4.03      inference(cnf_transformation,[],[f39]) ).
% 27.63/4.03  
% 27.63/4.03  cnf(c_466,plain,
% 27.63/4.03      ( k6_subset_1(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k10_relat_1(X0,k6_subset_1(X1,X2))
% 27.63/4.03      | v1_relat_1(X0) != iProver_top
% 27.63/4.03      | v1_funct_1(X0) != iProver_top ),
% 27.63/4.03      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 27.63/4.03  
% 27.63/4.03  cnf(c_1531,plain,
% 27.63/4.03      ( k6_subset_1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) = k10_relat_1(sK2,k6_subset_1(X0,X1))
% 27.63/4.03      | v1_funct_1(sK2) != iProver_top ),
% 27.63/4.03      inference(superposition,[status(thm)],[c_460,c_466]) ).
% 27.63/4.03  
% 27.63/4.03  cnf(c_14,negated_conjecture,
% 27.63/4.03      ( v1_funct_1(sK2) ),
% 27.63/4.03      inference(cnf_transformation,[],[f42]) ).
% 27.63/4.03  
% 27.63/4.03  cnf(c_600,plain,
% 27.63/4.03      ( ~ v1_relat_1(sK2)
% 27.63/4.03      | ~ v1_funct_1(sK2)
% 27.63/4.03      | k6_subset_1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) = k10_relat_1(sK2,k6_subset_1(X0,X1)) ),
% 27.63/4.03      inference(instantiation,[status(thm)],[c_9]) ).
% 27.63/4.03  
% 27.63/4.03  cnf(c_2093,plain,
% 27.63/4.03      ( k6_subset_1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) = k10_relat_1(sK2,k6_subset_1(X0,X1)) ),
% 27.63/4.03      inference(global_propositional_subsumption,
% 27.63/4.03                [status(thm)],
% 27.63/4.03                [c_1531,c_15,c_14,c_600]) ).
% 27.63/4.03  
% 27.63/4.03  cnf(c_0,plain,
% 27.63/4.03      ( k6_subset_1(X0,k6_subset_1(X0,X1)) = k6_subset_1(X1,k6_subset_1(X1,X0)) ),
% 27.63/4.03      inference(cnf_transformation,[],[f47]) ).
% 27.63/4.03  
% 27.63/4.03  cnf(c_7,plain,
% 27.63/4.03      ( k6_subset_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 27.63/4.03      inference(cnf_transformation,[],[f52]) ).
% 27.63/4.03  
% 27.63/4.03  cnf(c_830,plain,
% 27.63/4.03      ( k6_subset_1(X0,k6_subset_1(X0,k1_xboole_0)) = k1_xboole_0 ),
% 27.63/4.03      inference(superposition,[status(thm)],[c_0,c_7]) ).
% 27.63/4.03  
% 27.63/4.03  cnf(c_5,plain,
% 27.63/4.03      ( k6_subset_1(X0,k1_xboole_0) = X0 ),
% 27.63/4.03      inference(cnf_transformation,[],[f50]) ).
% 27.63/4.03  
% 27.63/4.03  cnf(c_833,plain,
% 27.63/4.03      ( k6_subset_1(X0,X0) = k1_xboole_0 ),
% 27.63/4.03      inference(light_normalisation,[status(thm)],[c_830,c_5]) ).
% 27.63/4.03  
% 27.63/4.03  cnf(c_2105,plain,
% 27.63/4.03      ( k10_relat_1(sK2,k6_subset_1(X0,X0)) = k1_xboole_0 ),
% 27.63/4.03      inference(superposition,[status(thm)],[c_2093,c_833]) ).
% 27.63/4.03  
% 27.63/4.03  cnf(c_2110,plain,
% 27.63/4.03      ( k10_relat_1(sK2,k1_xboole_0) = k1_xboole_0 ),
% 27.63/4.03      inference(light_normalisation,[status(thm)],[c_2105,c_833]) ).
% 27.63/4.03  
% 27.63/4.03  cnf(c_4,plain,
% 27.63/4.03      ( r1_tarski(k1_xboole_0,X0) ),
% 27.63/4.03      inference(cnf_transformation,[],[f31]) ).
% 27.63/4.03  
% 27.63/4.03  cnf(c_468,plain,
% 27.63/4.03      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 27.63/4.03      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 27.63/4.03  
% 27.63/4.03  cnf(c_10,plain,
% 27.63/4.03      ( ~ r1_tarski(X0,k2_relat_1(X1))
% 27.63/4.03      | ~ v1_relat_1(X1)
% 27.63/4.03      | ~ v1_funct_1(X1)
% 27.63/4.03      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ),
% 27.63/4.03      inference(cnf_transformation,[],[f40]) ).
% 27.63/4.03  
% 27.63/4.03  cnf(c_465,plain,
% 27.63/4.03      ( k9_relat_1(X0,k10_relat_1(X0,X1)) = X1
% 27.63/4.03      | r1_tarski(X1,k2_relat_1(X0)) != iProver_top
% 27.63/4.03      | v1_relat_1(X0) != iProver_top
% 27.63/4.03      | v1_funct_1(X0) != iProver_top ),
% 27.63/4.03      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 27.63/4.03  
% 27.63/4.03  cnf(c_805,plain,
% 27.63/4.03      ( k9_relat_1(X0,k10_relat_1(X0,k1_xboole_0)) = k1_xboole_0
% 27.63/4.03      | v1_relat_1(X0) != iProver_top
% 27.63/4.03      | v1_funct_1(X0) != iProver_top ),
% 27.63/4.03      inference(superposition,[status(thm)],[c_468,c_465]) ).
% 27.63/4.03  
% 27.63/4.03  cnf(c_3819,plain,
% 27.63/4.03      ( k9_relat_1(sK2,k10_relat_1(sK2,k1_xboole_0)) = k1_xboole_0
% 27.63/4.03      | v1_funct_1(sK2) != iProver_top ),
% 27.63/4.03      inference(superposition,[status(thm)],[c_460,c_805]) ).
% 27.63/4.03  
% 27.63/4.03  cnf(c_590,plain,
% 27.63/4.03      ( ~ r1_tarski(X0,k2_relat_1(sK2))
% 27.63/4.03      | ~ v1_relat_1(sK2)
% 27.63/4.03      | ~ v1_funct_1(sK2)
% 27.63/4.03      | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0 ),
% 27.63/4.03      inference(instantiation,[status(thm)],[c_10]) ).
% 27.63/4.03  
% 27.63/4.03  cnf(c_592,plain,
% 27.63/4.03      ( ~ r1_tarski(k1_xboole_0,k2_relat_1(sK2))
% 27.63/4.03      | ~ v1_relat_1(sK2)
% 27.63/4.03      | ~ v1_funct_1(sK2)
% 27.63/4.03      | k9_relat_1(sK2,k10_relat_1(sK2,k1_xboole_0)) = k1_xboole_0 ),
% 27.63/4.03      inference(instantiation,[status(thm)],[c_590]) ).
% 27.63/4.03  
% 27.63/4.03  cnf(c_680,plain,
% 27.63/4.03      ( r1_tarski(k1_xboole_0,k2_relat_1(sK2)) ),
% 27.63/4.03      inference(instantiation,[status(thm)],[c_4]) ).
% 27.63/4.03  
% 27.63/4.03  cnf(c_4342,plain,
% 27.63/4.03      ( k9_relat_1(sK2,k10_relat_1(sK2,k1_xboole_0)) = k1_xboole_0 ),
% 27.63/4.03      inference(global_propositional_subsumption,
% 27.63/4.03                [status(thm)],
% 27.63/4.03                [c_3819,c_15,c_14,c_592,c_680]) ).
% 27.63/4.03  
% 27.63/4.03  cnf(c_23834,plain,
% 27.63/4.03      ( k9_relat_1(sK2,k1_xboole_0) = k1_xboole_0 ),
% 27.63/4.03      inference(demodulation,[status(thm)],[c_2110,c_4342]) ).
% 27.63/4.03  
% 27.63/4.03  cnf(c_155,plain,
% 27.63/4.03      ( X0 != X1 | k9_relat_1(X2,X0) = k9_relat_1(X2,X1) ),
% 27.63/4.03      theory(equality) ).
% 27.63/4.03  
% 27.63/4.03  cnf(c_19979,plain,
% 27.63/4.03      ( k9_relat_1(sK2,k10_relat_1(sK2,k6_subset_1(sK0,sK1))) = k9_relat_1(sK2,X0)
% 27.63/4.03      | k10_relat_1(sK2,k6_subset_1(sK0,sK1)) != X0 ),
% 27.63/4.03      inference(instantiation,[status(thm)],[c_155]) ).
% 27.63/4.03  
% 27.63/4.03  cnf(c_19981,plain,
% 27.63/4.03      ( k9_relat_1(sK2,k10_relat_1(sK2,k6_subset_1(sK0,sK1))) = k9_relat_1(sK2,k1_xboole_0)
% 27.63/4.03      | k10_relat_1(sK2,k6_subset_1(sK0,sK1)) != k1_xboole_0 ),
% 27.63/4.03      inference(instantiation,[status(thm)],[c_19979]) ).
% 27.63/4.03  
% 27.63/4.03  cnf(c_6371,plain,
% 27.63/4.03      ( k9_relat_1(sK2,k10_relat_1(sK2,k6_subset_1(sK0,sK1))) != X0
% 27.63/4.03      | k1_xboole_0 != X0
% 27.63/4.03      | k1_xboole_0 = k9_relat_1(sK2,k10_relat_1(sK2,k6_subset_1(sK0,sK1))) ),
% 27.63/4.03      inference(instantiation,[status(thm)],[c_148]) ).
% 27.63/4.03  
% 27.63/4.03  cnf(c_19978,plain,
% 27.63/4.03      ( k9_relat_1(sK2,k10_relat_1(sK2,k6_subset_1(sK0,sK1))) != k9_relat_1(sK2,X0)
% 27.63/4.03      | k1_xboole_0 != k9_relat_1(sK2,X0)
% 27.63/4.03      | k1_xboole_0 = k9_relat_1(sK2,k10_relat_1(sK2,k6_subset_1(sK0,sK1))) ),
% 27.63/4.03      inference(instantiation,[status(thm)],[c_6371]) ).
% 27.63/4.03  
% 27.63/4.03  cnf(c_19980,plain,
% 27.63/4.03      ( k9_relat_1(sK2,k10_relat_1(sK2,k6_subset_1(sK0,sK1))) != k9_relat_1(sK2,k1_xboole_0)
% 27.63/4.03      | k1_xboole_0 = k9_relat_1(sK2,k10_relat_1(sK2,k6_subset_1(sK0,sK1)))
% 27.63/4.03      | k1_xboole_0 != k9_relat_1(sK2,k1_xboole_0) ),
% 27.63/4.03      inference(instantiation,[status(thm)],[c_19978]) ).
% 27.63/4.03  
% 27.63/4.03  cnf(c_629,plain,
% 27.63/4.03      ( k6_subset_1(sK0,sK1) != X0
% 27.63/4.03      | k6_subset_1(sK0,sK1) = k1_xboole_0
% 27.63/4.03      | k1_xboole_0 != X0 ),
% 27.63/4.03      inference(instantiation,[status(thm)],[c_148]) ).
% 27.63/4.03  
% 27.63/4.03  cnf(c_5830,plain,
% 27.63/4.03      ( k6_subset_1(sK0,sK1) != k9_relat_1(sK2,k10_relat_1(sK2,k6_subset_1(sK0,sK1)))
% 27.63/4.03      | k6_subset_1(sK0,sK1) = k1_xboole_0
% 27.63/4.03      | k1_xboole_0 != k9_relat_1(sK2,k10_relat_1(sK2,k6_subset_1(sK0,sK1))) ),
% 27.63/4.03      inference(instantiation,[status(thm)],[c_629]) ).
% 27.63/4.03  
% 27.63/4.03  cnf(c_3,plain,
% 27.63/4.03      ( ~ r1_tarski(X0,X1) | r1_tarski(X0,k2_xboole_0(X2,X1)) ),
% 27.63/4.03      inference(cnf_transformation,[],[f30]) ).
% 27.63/4.03  
% 27.63/4.03  cnf(c_867,plain,
% 27.63/4.03      ( r1_tarski(X0,k2_xboole_0(X1,k2_relat_1(sK2)))
% 27.63/4.03      | ~ r1_tarski(X0,k2_relat_1(sK2)) ),
% 27.63/4.03      inference(instantiation,[status(thm)],[c_3]) ).
% 27.63/4.03  
% 27.63/4.03  cnf(c_2263,plain,
% 27.63/4.03      ( r1_tarski(sK0,k2_xboole_0(sK1,k2_relat_1(sK2)))
% 27.63/4.03      | ~ r1_tarski(sK0,k2_relat_1(sK2)) ),
% 27.63/4.03      inference(instantiation,[status(thm)],[c_867]) ).
% 27.63/4.03  
% 27.63/4.03  cnf(c_13,negated_conjecture,
% 27.63/4.03      ( r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
% 27.63/4.03      inference(cnf_transformation,[],[f43]) ).
% 27.63/4.03  
% 27.63/4.03  cnf(c_462,plain,
% 27.63/4.03      ( r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) = iProver_top ),
% 27.63/4.03      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 27.63/4.03  
% 27.63/4.03  cnf(c_1,plain,
% 27.63/4.03      ( ~ r1_tarski(X0,X1) | k6_subset_1(X0,X1) = k1_xboole_0 ),
% 27.63/4.03      inference(cnf_transformation,[],[f48]) ).
% 27.63/4.03  
% 27.63/4.03  cnf(c_471,plain,
% 27.63/4.03      ( k6_subset_1(X0,X1) = k1_xboole_0
% 27.63/4.03      | r1_tarski(X0,X1) != iProver_top ),
% 27.63/4.03      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 27.63/4.03  
% 27.63/4.03  cnf(c_1653,plain,
% 27.63/4.03      ( k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) = k1_xboole_0 ),
% 27.63/4.03      inference(superposition,[status(thm)],[c_462,c_471]) ).
% 27.63/4.03  
% 27.63/4.03  cnf(c_2106,plain,
% 27.63/4.03      ( k10_relat_1(sK2,k6_subset_1(sK0,sK1)) = k1_xboole_0 ),
% 27.63/4.03      inference(superposition,[status(thm)],[c_2093,c_1653]) ).
% 27.63/4.03  
% 27.63/4.03  cnf(c_6,plain,
% 27.63/4.03      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
% 27.63/4.03      | r1_tarski(k6_subset_1(X0,X1),X2) ),
% 27.63/4.03      inference(cnf_transformation,[],[f51]) ).
% 27.63/4.03  
% 27.63/4.03  cnf(c_686,plain,
% 27.63/4.03      ( ~ r1_tarski(X0,k2_xboole_0(X1,k2_relat_1(sK2)))
% 27.63/4.03      | r1_tarski(k6_subset_1(X0,X1),k2_relat_1(sK2)) ),
% 27.63/4.03      inference(instantiation,[status(thm)],[c_6]) ).
% 27.63/4.03  
% 27.63/4.03  cnf(c_2016,plain,
% 27.63/4.03      ( r1_tarski(k6_subset_1(sK0,sK1),k2_relat_1(sK2))
% 27.63/4.03      | ~ r1_tarski(sK0,k2_xboole_0(sK1,k2_relat_1(sK2))) ),
% 27.63/4.03      inference(instantiation,[status(thm)],[c_686]) ).
% 27.63/4.03  
% 27.63/4.03  cnf(c_685,plain,
% 27.63/4.03      ( ~ r1_tarski(k6_subset_1(X0,X1),k2_relat_1(sK2))
% 27.63/4.03      | ~ v1_relat_1(sK2)
% 27.63/4.03      | ~ v1_funct_1(sK2)
% 27.63/4.03      | k9_relat_1(sK2,k10_relat_1(sK2,k6_subset_1(X0,X1))) = k6_subset_1(X0,X1) ),
% 27.63/4.03      inference(instantiation,[status(thm)],[c_590]) ).
% 27.63/4.03  
% 27.63/4.03  cnf(c_1455,plain,
% 27.63/4.03      ( ~ r1_tarski(k6_subset_1(sK0,sK1),k2_relat_1(sK2))
% 27.63/4.03      | ~ v1_relat_1(sK2)
% 27.63/4.03      | ~ v1_funct_1(sK2)
% 27.63/4.03      | k9_relat_1(sK2,k10_relat_1(sK2,k6_subset_1(sK0,sK1))) = k6_subset_1(sK0,sK1) ),
% 27.63/4.03      inference(instantiation,[status(thm)],[c_685]) ).
% 27.63/4.03  
% 27.63/4.03  cnf(c_770,plain,
% 27.63/4.03      ( X0 != X1
% 27.63/4.03      | k6_subset_1(sK0,sK1) != X1
% 27.63/4.03      | k6_subset_1(sK0,sK1) = X0 ),
% 27.63/4.03      inference(instantiation,[status(thm)],[c_148]) ).
% 27.63/4.03  
% 27.63/4.03  cnf(c_966,plain,
% 27.63/4.03      ( X0 != k6_subset_1(sK0,sK1)
% 27.63/4.03      | k6_subset_1(sK0,sK1) = X0
% 27.63/4.03      | k6_subset_1(sK0,sK1) != k6_subset_1(sK0,sK1) ),
% 27.63/4.03      inference(instantiation,[status(thm)],[c_770]) ).
% 27.63/4.03  
% 27.63/4.03  cnf(c_1454,plain,
% 27.63/4.03      ( k9_relat_1(sK2,k10_relat_1(sK2,k6_subset_1(sK0,sK1))) != k6_subset_1(sK0,sK1)
% 27.63/4.03      | k6_subset_1(sK0,sK1) = k9_relat_1(sK2,k10_relat_1(sK2,k6_subset_1(sK0,sK1)))
% 27.63/4.03      | k6_subset_1(sK0,sK1) != k6_subset_1(sK0,sK1) ),
% 27.63/4.03      inference(instantiation,[status(thm)],[c_966]) ).
% 27.63/4.03  
% 27.63/4.03  cnf(c_147,plain,( X0 = X0 ),theory(equality) ).
% 27.63/4.03  
% 27.63/4.03  cnf(c_769,plain,
% 27.63/4.03      ( k6_subset_1(sK0,sK1) = k6_subset_1(sK0,sK1) ),
% 27.63/4.03      inference(instantiation,[status(thm)],[c_147]) ).
% 27.63/4.03  
% 27.63/4.03  cnf(c_2,plain,
% 27.63/4.03      ( r1_tarski(X0,X1) | k6_subset_1(X0,X1) != k1_xboole_0 ),
% 27.63/4.03      inference(cnf_transformation,[],[f49]) ).
% 27.63/4.03  
% 27.63/4.03  cnf(c_561,plain,
% 27.63/4.03      ( r1_tarski(sK0,sK1) | k6_subset_1(sK0,sK1) != k1_xboole_0 ),
% 27.63/4.03      inference(instantiation,[status(thm)],[c_2]) ).
% 27.63/4.03  
% 27.63/4.03  cnf(c_166,plain,
% 27.63/4.03      ( k1_xboole_0 = k1_xboole_0 ),
% 27.63/4.03      inference(instantiation,[status(thm)],[c_147]) ).
% 27.63/4.03  
% 27.63/4.03  cnf(c_11,negated_conjecture,
% 27.63/4.03      ( ~ r1_tarski(sK0,sK1) ),
% 27.63/4.03      inference(cnf_transformation,[],[f45]) ).
% 27.63/4.03  
% 27.63/4.03  cnf(c_12,negated_conjecture,
% 27.63/4.03      ( r1_tarski(sK0,k2_relat_1(sK2)) ),
% 27.63/4.03      inference(cnf_transformation,[],[f44]) ).
% 27.63/4.03  
% 27.63/4.03  cnf(contradiction,plain,
% 27.63/4.03      ( $false ),
% 27.63/4.03      inference(minisat,
% 27.63/4.03                [status(thm)],
% 27.63/4.03                [c_98812,c_23834,c_19981,c_19980,c_5830,c_2263,c_2106,
% 27.63/4.03                 c_2016,c_1455,c_1454,c_769,c_561,c_166,c_11,c_12,c_14,
% 27.63/4.03                 c_15]) ).
% 27.63/4.03  
% 27.63/4.03  
% 27.63/4.03  % SZS output end CNFRefutation for theBenchmark.p
% 27.63/4.03  
% 27.63/4.03  ------                               Statistics
% 27.63/4.03  
% 27.63/4.03  ------ Selected
% 27.63/4.03  
% 27.63/4.03  total_time:                             3.202
% 27.63/4.03  
%------------------------------------------------------------------------------
