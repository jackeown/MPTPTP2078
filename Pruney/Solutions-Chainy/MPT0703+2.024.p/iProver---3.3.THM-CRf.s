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
% DateTime   : Thu Dec  3 11:52:18 EST 2020

% Result     : Theorem 3.46s
% Output     : CNFRefutation 3.46s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 220 expanded)
%              Number of clauses        :   48 (  59 expanded)
%              Number of leaves         :   12 (  48 expanded)
%              Depth                    :   18
%              Number of atoms          :  222 ( 654 expanded)
%              Number of equality atoms :   96 ( 157 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(X0,k2_relat_1(X2))
          & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( r1_tarski(X0,k2_relat_1(X2))
            & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) )
         => r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_tarski(X0,k2_relat_1(X2))
      & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_tarski(X0,k2_relat_1(X2))
      & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f20])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f25])).

fof(f40,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f45,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f36,f35])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k1_setfam_1(k1_enumset1(k10_relat_1(X2,X0),k10_relat_1(X2,X0),k10_relat_1(X2,X1))) = k10_relat_1(X2,k1_setfam_1(k1_enumset1(X0,X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f37,f45,f45])).

fof(f41,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f42,plain,(
    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f26])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f34,f45])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f43,plain,(
    r1_tarski(sK0,k2_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f26])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f49,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f33,f45])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f22])).

fof(f29,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

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

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f46,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1))) ),
    inference(definition_unfolding,[],[f32,f45])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1))) ) ),
    inference(definition_unfolding,[],[f30,f46])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f53,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f27])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f31,f46])).

fof(f44,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_14,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_602,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_setfam_1(k1_enumset1(k10_relat_1(X0,X1),k10_relat_1(X0,X1),k10_relat_1(X0,X2))) = k10_relat_1(X0,k1_setfam_1(k1_enumset1(X1,X1,X2))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_609,plain,
    ( k1_setfam_1(k1_enumset1(k10_relat_1(X0,X1),k10_relat_1(X0,X1),k10_relat_1(X0,X2))) = k10_relat_1(X0,k1_setfam_1(k1_enumset1(X1,X1,X2)))
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1376,plain,
    ( k1_setfam_1(k1_enumset1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X0),k10_relat_1(sK2,X1))) = k10_relat_1(sK2,k1_setfam_1(k1_enumset1(X0,X0,X1)))
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_602,c_609])).

cnf(c_13,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_16,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2291,plain,
    ( k1_setfam_1(k1_enumset1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X0),k10_relat_1(sK2,X1))) = k10_relat_1(sK2,k1_setfam_1(k1_enumset1(X0,X0,X1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1376,c_16])).

cnf(c_12,negated_conjecture,
    ( r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_604,plain,
    ( r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | k1_setfam_1(k1_enumset1(X0,X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_610,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_887,plain,
    ( k1_setfam_1(k1_enumset1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))) = k10_relat_1(sK2,sK0) ),
    inference(superposition,[status(thm)],[c_604,c_610])).

cnf(c_2303,plain,
    ( k10_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,sK1))) = k10_relat_1(sK2,sK0) ),
    inference(superposition,[status(thm)],[c_2291,c_887])).

cnf(c_8,plain,
    ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_608,plain,
    ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3417,plain,
    ( r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,sK0)),k1_setfam_1(k1_enumset1(sK0,sK0,sK1))) = iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2303,c_608])).

cnf(c_11,negated_conjecture,
    ( r1_tarski(sK0,k2_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_605,plain,
    ( r1_tarski(sK0,k2_relat_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_607,plain,
    ( k9_relat_1(X0,k10_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k2_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1186,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,sK0)) = sK0
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_605,c_607])).

cnf(c_765,plain,
    ( ~ r1_tarski(sK0,k2_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k9_relat_1(sK2,k10_relat_1(sK2,sK0)) = sK0 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_2101,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,sK0)) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1186,c_14,c_13,c_11,c_765])).

cnf(c_3445,plain,
    ( r1_tarski(sK0,k1_setfam_1(k1_enumset1(sK0,sK0,sK1))) = iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3417,c_2101])).

cnf(c_15,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3977,plain,
    ( r1_tarski(sK0,k1_setfam_1(k1_enumset1(sK0,sK0,sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3445,c_15,c_16])).

cnf(c_5,plain,
    ( r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_611,plain,
    ( r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_615,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1217,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = X0
    | r1_tarski(X0,k1_setfam_1(k1_enumset1(X0,X0,X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_611,c_615])).

cnf(c_3985,plain,
    ( k1_setfam_1(k1_enumset1(sK0,sK0,sK1)) = sK0 ),
    inference(superposition,[status(thm)],[c_3977,c_1217])).

cnf(c_4,plain,
    ( r1_tarski(X0,X1)
    | k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1))) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_612,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1))) != k1_xboole_0
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_4241,plain,
    ( k5_xboole_0(sK0,sK0) != k1_xboole_0
    | r1_tarski(sK0,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_3985,c_612])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_614,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1))) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_613,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1))) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1026,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_614,c_613])).

cnf(c_884,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_614,c_610])).

cnf(c_1670,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1026,c_884])).

cnf(c_4245,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK0,sK1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4241,c_1670])).

cnf(c_4246,plain,
    ( r1_tarski(sK0,sK1) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_4245])).

cnf(c_10,negated_conjecture,
    ( ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_19,plain,
    ( r1_tarski(sK0,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4246,c_19])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n018.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:10:42 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.46/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.46/0.99  
% 3.46/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.46/0.99  
% 3.46/0.99  ------  iProver source info
% 3.46/0.99  
% 3.46/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.46/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.46/0.99  git: non_committed_changes: false
% 3.46/0.99  git: last_make_outside_of_git: false
% 3.46/0.99  
% 3.46/0.99  ------ 
% 3.46/0.99  
% 3.46/0.99  ------ Input Options
% 3.46/0.99  
% 3.46/0.99  --out_options                           all
% 3.46/0.99  --tptp_safe_out                         true
% 3.46/0.99  --problem_path                          ""
% 3.46/0.99  --include_path                          ""
% 3.46/0.99  --clausifier                            res/vclausify_rel
% 3.46/0.99  --clausifier_options                    --mode clausify
% 3.46/0.99  --stdin                                 false
% 3.46/0.99  --stats_out                             sel
% 3.46/0.99  
% 3.46/0.99  ------ General Options
% 3.46/0.99  
% 3.46/0.99  --fof                                   false
% 3.46/0.99  --time_out_real                         604.99
% 3.46/0.99  --time_out_virtual                      -1.
% 3.46/0.99  --symbol_type_check                     false
% 3.46/0.99  --clausify_out                          false
% 3.46/0.99  --sig_cnt_out                           false
% 3.46/0.99  --trig_cnt_out                          false
% 3.46/0.99  --trig_cnt_out_tolerance                1.
% 3.46/0.99  --trig_cnt_out_sk_spl                   false
% 3.46/0.99  --abstr_cl_out                          false
% 3.46/0.99  
% 3.46/0.99  ------ Global Options
% 3.46/0.99  
% 3.46/0.99  --schedule                              none
% 3.46/0.99  --add_important_lit                     false
% 3.46/0.99  --prop_solver_per_cl                    1000
% 3.46/0.99  --min_unsat_core                        false
% 3.46/0.99  --soft_assumptions                      false
% 3.46/0.99  --soft_lemma_size                       3
% 3.46/0.99  --prop_impl_unit_size                   0
% 3.46/0.99  --prop_impl_unit                        []
% 3.46/0.99  --share_sel_clauses                     true
% 3.46/0.99  --reset_solvers                         false
% 3.46/0.99  --bc_imp_inh                            [conj_cone]
% 3.46/0.99  --conj_cone_tolerance                   3.
% 3.46/0.99  --extra_neg_conj                        none
% 3.46/0.99  --large_theory_mode                     true
% 3.46/0.99  --prolific_symb_bound                   200
% 3.46/0.99  --lt_threshold                          2000
% 3.46/0.99  --clause_weak_htbl                      true
% 3.46/0.99  --gc_record_bc_elim                     false
% 3.46/0.99  
% 3.46/0.99  ------ Preprocessing Options
% 3.46/0.99  
% 3.46/0.99  --preprocessing_flag                    true
% 3.46/0.99  --time_out_prep_mult                    0.1
% 3.46/0.99  --splitting_mode                        input
% 3.46/0.99  --splitting_grd                         true
% 3.46/0.99  --splitting_cvd                         false
% 3.46/0.99  --splitting_cvd_svl                     false
% 3.46/0.99  --splitting_nvd                         32
% 3.46/0.99  --sub_typing                            true
% 3.46/0.99  --prep_gs_sim                           false
% 3.46/0.99  --prep_unflatten                        true
% 3.46/0.99  --prep_res_sim                          true
% 3.46/0.99  --prep_upred                            true
% 3.46/0.99  --prep_sem_filter                       exhaustive
% 3.46/0.99  --prep_sem_filter_out                   false
% 3.46/0.99  --pred_elim                             false
% 3.46/0.99  --res_sim_input                         true
% 3.46/0.99  --eq_ax_congr_red                       true
% 3.46/0.99  --pure_diseq_elim                       true
% 3.46/0.99  --brand_transform                       false
% 3.46/0.99  --non_eq_to_eq                          false
% 3.46/0.99  --prep_def_merge                        true
% 3.46/0.99  --prep_def_merge_prop_impl              false
% 3.46/0.99  --prep_def_merge_mbd                    true
% 3.46/0.99  --prep_def_merge_tr_red                 false
% 3.46/0.99  --prep_def_merge_tr_cl                  false
% 3.46/0.99  --smt_preprocessing                     true
% 3.46/0.99  --smt_ac_axioms                         fast
% 3.46/0.99  --preprocessed_out                      false
% 3.46/0.99  --preprocessed_stats                    false
% 3.46/0.99  
% 3.46/0.99  ------ Abstraction refinement Options
% 3.46/0.99  
% 3.46/0.99  --abstr_ref                             []
% 3.46/0.99  --abstr_ref_prep                        false
% 3.46/0.99  --abstr_ref_until_sat                   false
% 3.46/0.99  --abstr_ref_sig_restrict                funpre
% 3.46/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.46/0.99  --abstr_ref_under                       []
% 3.46/0.99  
% 3.46/0.99  ------ SAT Options
% 3.46/0.99  
% 3.46/0.99  --sat_mode                              false
% 3.46/0.99  --sat_fm_restart_options                ""
% 3.46/0.99  --sat_gr_def                            false
% 3.46/0.99  --sat_epr_types                         true
% 3.46/0.99  --sat_non_cyclic_types                  false
% 3.46/0.99  --sat_finite_models                     false
% 3.46/0.99  --sat_fm_lemmas                         false
% 3.46/0.99  --sat_fm_prep                           false
% 3.46/0.99  --sat_fm_uc_incr                        true
% 3.46/0.99  --sat_out_model                         small
% 3.46/0.99  --sat_out_clauses                       false
% 3.46/0.99  
% 3.46/0.99  ------ QBF Options
% 3.46/0.99  
% 3.46/0.99  --qbf_mode                              false
% 3.46/0.99  --qbf_elim_univ                         false
% 3.46/0.99  --qbf_dom_inst                          none
% 3.46/0.99  --qbf_dom_pre_inst                      false
% 3.46/0.99  --qbf_sk_in                             false
% 3.46/0.99  --qbf_pred_elim                         true
% 3.46/0.99  --qbf_split                             512
% 3.46/0.99  
% 3.46/0.99  ------ BMC1 Options
% 3.46/0.99  
% 3.46/0.99  --bmc1_incremental                      false
% 3.46/0.99  --bmc1_axioms                           reachable_all
% 3.46/0.99  --bmc1_min_bound                        0
% 3.46/0.99  --bmc1_max_bound                        -1
% 3.46/0.99  --bmc1_max_bound_default                -1
% 3.46/0.99  --bmc1_symbol_reachability              true
% 3.46/0.99  --bmc1_property_lemmas                  false
% 3.46/0.99  --bmc1_k_induction                      false
% 3.46/0.99  --bmc1_non_equiv_states                 false
% 3.46/0.99  --bmc1_deadlock                         false
% 3.46/0.99  --bmc1_ucm                              false
% 3.46/0.99  --bmc1_add_unsat_core                   none
% 3.46/0.99  --bmc1_unsat_core_children              false
% 3.46/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.46/0.99  --bmc1_out_stat                         full
% 3.46/0.99  --bmc1_ground_init                      false
% 3.46/0.99  --bmc1_pre_inst_next_state              false
% 3.46/0.99  --bmc1_pre_inst_state                   false
% 3.46/0.99  --bmc1_pre_inst_reach_state             false
% 3.46/0.99  --bmc1_out_unsat_core                   false
% 3.46/0.99  --bmc1_aig_witness_out                  false
% 3.46/0.99  --bmc1_verbose                          false
% 3.46/0.99  --bmc1_dump_clauses_tptp                false
% 3.46/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.46/0.99  --bmc1_dump_file                        -
% 3.46/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.46/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.46/0.99  --bmc1_ucm_extend_mode                  1
% 3.46/0.99  --bmc1_ucm_init_mode                    2
% 3.46/0.99  --bmc1_ucm_cone_mode                    none
% 3.46/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.46/0.99  --bmc1_ucm_relax_model                  4
% 3.46/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.46/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.46/0.99  --bmc1_ucm_layered_model                none
% 3.46/0.99  --bmc1_ucm_max_lemma_size               10
% 3.46/0.99  
% 3.46/0.99  ------ AIG Options
% 3.46/0.99  
% 3.46/0.99  --aig_mode                              false
% 3.46/0.99  
% 3.46/0.99  ------ Instantiation Options
% 3.46/0.99  
% 3.46/0.99  --instantiation_flag                    true
% 3.46/0.99  --inst_sos_flag                         false
% 3.46/0.99  --inst_sos_phase                        true
% 3.46/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.46/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.46/0.99  --inst_lit_sel_side                     num_symb
% 3.46/0.99  --inst_solver_per_active                1400
% 3.46/0.99  --inst_solver_calls_frac                1.
% 3.46/0.99  --inst_passive_queue_type               priority_queues
% 3.46/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.46/0.99  --inst_passive_queues_freq              [25;2]
% 3.46/0.99  --inst_dismatching                      true
% 3.46/0.99  --inst_eager_unprocessed_to_passive     true
% 3.46/0.99  --inst_prop_sim_given                   true
% 3.46/0.99  --inst_prop_sim_new                     false
% 3.46/0.99  --inst_subs_new                         false
% 3.46/0.99  --inst_eq_res_simp                      false
% 3.46/0.99  --inst_subs_given                       false
% 3.46/0.99  --inst_orphan_elimination               true
% 3.46/0.99  --inst_learning_loop_flag               true
% 3.46/0.99  --inst_learning_start                   3000
% 3.46/0.99  --inst_learning_factor                  2
% 3.46/0.99  --inst_start_prop_sim_after_learn       3
% 3.46/0.99  --inst_sel_renew                        solver
% 3.46/0.99  --inst_lit_activity_flag                true
% 3.46/0.99  --inst_restr_to_given                   false
% 3.46/0.99  --inst_activity_threshold               500
% 3.46/0.99  --inst_out_proof                        true
% 3.46/0.99  
% 3.46/0.99  ------ Resolution Options
% 3.46/0.99  
% 3.46/0.99  --resolution_flag                       true
% 3.46/0.99  --res_lit_sel                           adaptive
% 3.46/0.99  --res_lit_sel_side                      none
% 3.46/0.99  --res_ordering                          kbo
% 3.46/0.99  --res_to_prop_solver                    active
% 3.46/0.99  --res_prop_simpl_new                    false
% 3.46/0.99  --res_prop_simpl_given                  true
% 3.46/0.99  --res_passive_queue_type                priority_queues
% 3.46/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.46/0.99  --res_passive_queues_freq               [15;5]
% 3.46/0.99  --res_forward_subs                      full
% 3.46/0.99  --res_backward_subs                     full
% 3.46/0.99  --res_forward_subs_resolution           true
% 3.46/0.99  --res_backward_subs_resolution          true
% 3.46/0.99  --res_orphan_elimination                true
% 3.46/0.99  --res_time_limit                        2.
% 3.46/0.99  --res_out_proof                         true
% 3.46/0.99  
% 3.46/0.99  ------ Superposition Options
% 3.46/0.99  
% 3.46/0.99  --superposition_flag                    true
% 3.46/0.99  --sup_passive_queue_type                priority_queues
% 3.46/0.99  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.46/0.99  --sup_passive_queues_freq               [1;4]
% 3.46/0.99  --demod_completeness_check              fast
% 3.46/0.99  --demod_use_ground                      true
% 3.46/0.99  --sup_to_prop_solver                    passive
% 3.46/0.99  --sup_prop_simpl_new                    true
% 3.46/0.99  --sup_prop_simpl_given                  true
% 3.46/0.99  --sup_fun_splitting                     false
% 3.46/0.99  --sup_smt_interval                      50000
% 3.46/0.99  
% 3.46/0.99  ------ Superposition Simplification Setup
% 3.46/0.99  
% 3.46/0.99  --sup_indices_passive                   []
% 3.46/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.46/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.46/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.46/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.46/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.46/0.99  --sup_full_bw                           [BwDemod]
% 3.46/0.99  --sup_immed_triv                        [TrivRules]
% 3.46/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.46/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.46/0.99  --sup_immed_bw_main                     []
% 3.46/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.46/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.46/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.46/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.46/0.99  
% 3.46/0.99  ------ Combination Options
% 3.46/0.99  
% 3.46/0.99  --comb_res_mult                         3
% 3.46/0.99  --comb_sup_mult                         2
% 3.46/0.99  --comb_inst_mult                        10
% 3.46/0.99  
% 3.46/0.99  ------ Debug Options
% 3.46/0.99  
% 3.46/0.99  --dbg_backtrace                         false
% 3.46/0.99  --dbg_dump_prop_clauses                 false
% 3.46/0.99  --dbg_dump_prop_clauses_file            -
% 3.46/0.99  --dbg_out_stat                          false
% 3.46/0.99  ------ Parsing...
% 3.46/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.46/0.99  
% 3.46/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 3.46/0.99  
% 3.46/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.46/0.99  
% 3.46/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.46/0.99  ------ Proving...
% 3.46/0.99  ------ Problem Properties 
% 3.46/0.99  
% 3.46/0.99  
% 3.46/0.99  clauses                                 14
% 3.46/0.99  conjectures                             5
% 3.46/0.99  EPR                                     5
% 3.46/0.99  Horn                                    14
% 3.46/0.99  unary                                   7
% 3.46/0.99  binary                                  3
% 3.46/0.99  lits                                    26
% 3.46/0.99  lits eq                                 6
% 3.46/0.99  fd_pure                                 0
% 3.46/0.99  fd_pseudo                               0
% 3.46/0.99  fd_cond                                 0
% 3.46/0.99  fd_pseudo_cond                          1
% 3.46/0.99  AC symbols                              0
% 3.46/0.99  
% 3.46/0.99  ------ Input Options Time Limit: Unbounded
% 3.46/0.99  
% 3.46/0.99  
% 3.46/0.99  ------ 
% 3.46/0.99  Current options:
% 3.46/0.99  ------ 
% 3.46/0.99  
% 3.46/0.99  ------ Input Options
% 3.46/0.99  
% 3.46/0.99  --out_options                           all
% 3.46/0.99  --tptp_safe_out                         true
% 3.46/0.99  --problem_path                          ""
% 3.46/0.99  --include_path                          ""
% 3.46/0.99  --clausifier                            res/vclausify_rel
% 3.46/0.99  --clausifier_options                    --mode clausify
% 3.46/0.99  --stdin                                 false
% 3.46/0.99  --stats_out                             sel
% 3.46/0.99  
% 3.46/0.99  ------ General Options
% 3.46/0.99  
% 3.46/0.99  --fof                                   false
% 3.46/0.99  --time_out_real                         604.99
% 3.46/0.99  --time_out_virtual                      -1.
% 3.46/0.99  --symbol_type_check                     false
% 3.46/0.99  --clausify_out                          false
% 3.46/0.99  --sig_cnt_out                           false
% 3.46/0.99  --trig_cnt_out                          false
% 3.46/0.99  --trig_cnt_out_tolerance                1.
% 3.46/0.99  --trig_cnt_out_sk_spl                   false
% 3.46/0.99  --abstr_cl_out                          false
% 3.46/0.99  
% 3.46/0.99  ------ Global Options
% 3.46/0.99  
% 3.46/0.99  --schedule                              none
% 3.46/0.99  --add_important_lit                     false
% 3.46/0.99  --prop_solver_per_cl                    1000
% 3.46/0.99  --min_unsat_core                        false
% 3.46/0.99  --soft_assumptions                      false
% 3.46/0.99  --soft_lemma_size                       3
% 3.46/0.99  --prop_impl_unit_size                   0
% 3.46/0.99  --prop_impl_unit                        []
% 3.46/0.99  --share_sel_clauses                     true
% 3.46/0.99  --reset_solvers                         false
% 3.46/0.99  --bc_imp_inh                            [conj_cone]
% 3.46/0.99  --conj_cone_tolerance                   3.
% 3.46/0.99  --extra_neg_conj                        none
% 3.46/0.99  --large_theory_mode                     true
% 3.46/0.99  --prolific_symb_bound                   200
% 3.46/0.99  --lt_threshold                          2000
% 3.46/0.99  --clause_weak_htbl                      true
% 3.46/0.99  --gc_record_bc_elim                     false
% 3.46/0.99  
% 3.46/0.99  ------ Preprocessing Options
% 3.46/0.99  
% 3.46/0.99  --preprocessing_flag                    true
% 3.46/0.99  --time_out_prep_mult                    0.1
% 3.46/0.99  --splitting_mode                        input
% 3.46/0.99  --splitting_grd                         true
% 3.46/0.99  --splitting_cvd                         false
% 3.46/0.99  --splitting_cvd_svl                     false
% 3.46/0.99  --splitting_nvd                         32
% 3.46/0.99  --sub_typing                            true
% 3.46/0.99  --prep_gs_sim                           false
% 3.46/0.99  --prep_unflatten                        true
% 3.46/0.99  --prep_res_sim                          true
% 3.46/0.99  --prep_upred                            true
% 3.46/0.99  --prep_sem_filter                       exhaustive
% 3.46/0.99  --prep_sem_filter_out                   false
% 3.46/0.99  --pred_elim                             false
% 3.46/0.99  --res_sim_input                         true
% 3.46/0.99  --eq_ax_congr_red                       true
% 3.46/0.99  --pure_diseq_elim                       true
% 3.46/0.99  --brand_transform                       false
% 3.46/0.99  --non_eq_to_eq                          false
% 3.46/0.99  --prep_def_merge                        true
% 3.46/0.99  --prep_def_merge_prop_impl              false
% 3.46/0.99  --prep_def_merge_mbd                    true
% 3.46/0.99  --prep_def_merge_tr_red                 false
% 3.46/0.99  --prep_def_merge_tr_cl                  false
% 3.46/0.99  --smt_preprocessing                     true
% 3.46/0.99  --smt_ac_axioms                         fast
% 3.46/0.99  --preprocessed_out                      false
% 3.46/0.99  --preprocessed_stats                    false
% 3.46/0.99  
% 3.46/0.99  ------ Abstraction refinement Options
% 3.46/0.99  
% 3.46/0.99  --abstr_ref                             []
% 3.46/0.99  --abstr_ref_prep                        false
% 3.46/0.99  --abstr_ref_until_sat                   false
% 3.46/0.99  --abstr_ref_sig_restrict                funpre
% 3.46/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.46/0.99  --abstr_ref_under                       []
% 3.46/0.99  
% 3.46/0.99  ------ SAT Options
% 3.46/0.99  
% 3.46/0.99  --sat_mode                              false
% 3.46/0.99  --sat_fm_restart_options                ""
% 3.46/0.99  --sat_gr_def                            false
% 3.46/0.99  --sat_epr_types                         true
% 3.46/0.99  --sat_non_cyclic_types                  false
% 3.46/0.99  --sat_finite_models                     false
% 3.46/0.99  --sat_fm_lemmas                         false
% 3.46/0.99  --sat_fm_prep                           false
% 3.46/0.99  --sat_fm_uc_incr                        true
% 3.46/0.99  --sat_out_model                         small
% 3.46/0.99  --sat_out_clauses                       false
% 3.46/0.99  
% 3.46/0.99  ------ QBF Options
% 3.46/0.99  
% 3.46/0.99  --qbf_mode                              false
% 3.46/0.99  --qbf_elim_univ                         false
% 3.46/0.99  --qbf_dom_inst                          none
% 3.46/0.99  --qbf_dom_pre_inst                      false
% 3.46/0.99  --qbf_sk_in                             false
% 3.46/0.99  --qbf_pred_elim                         true
% 3.46/0.99  --qbf_split                             512
% 3.46/0.99  
% 3.46/0.99  ------ BMC1 Options
% 3.46/0.99  
% 3.46/0.99  --bmc1_incremental                      false
% 3.46/0.99  --bmc1_axioms                           reachable_all
% 3.46/0.99  --bmc1_min_bound                        0
% 3.46/0.99  --bmc1_max_bound                        -1
% 3.46/0.99  --bmc1_max_bound_default                -1
% 3.46/0.99  --bmc1_symbol_reachability              true
% 3.46/0.99  --bmc1_property_lemmas                  false
% 3.46/0.99  --bmc1_k_induction                      false
% 3.46/0.99  --bmc1_non_equiv_states                 false
% 3.46/0.99  --bmc1_deadlock                         false
% 3.46/0.99  --bmc1_ucm                              false
% 3.46/0.99  --bmc1_add_unsat_core                   none
% 3.46/0.99  --bmc1_unsat_core_children              false
% 3.46/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.46/0.99  --bmc1_out_stat                         full
% 3.46/0.99  --bmc1_ground_init                      false
% 3.46/0.99  --bmc1_pre_inst_next_state              false
% 3.46/0.99  --bmc1_pre_inst_state                   false
% 3.46/0.99  --bmc1_pre_inst_reach_state             false
% 3.46/0.99  --bmc1_out_unsat_core                   false
% 3.46/0.99  --bmc1_aig_witness_out                  false
% 3.46/0.99  --bmc1_verbose                          false
% 3.46/0.99  --bmc1_dump_clauses_tptp                false
% 3.46/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.46/0.99  --bmc1_dump_file                        -
% 3.46/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.46/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.46/0.99  --bmc1_ucm_extend_mode                  1
% 3.46/0.99  --bmc1_ucm_init_mode                    2
% 3.46/0.99  --bmc1_ucm_cone_mode                    none
% 3.46/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.46/0.99  --bmc1_ucm_relax_model                  4
% 3.46/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.46/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.46/0.99  --bmc1_ucm_layered_model                none
% 3.46/0.99  --bmc1_ucm_max_lemma_size               10
% 3.46/0.99  
% 3.46/0.99  ------ AIG Options
% 3.46/0.99  
% 3.46/0.99  --aig_mode                              false
% 3.46/0.99  
% 3.46/0.99  ------ Instantiation Options
% 3.46/0.99  
% 3.46/0.99  --instantiation_flag                    true
% 3.46/0.99  --inst_sos_flag                         false
% 3.46/0.99  --inst_sos_phase                        true
% 3.46/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.46/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.46/0.99  --inst_lit_sel_side                     num_symb
% 3.46/0.99  --inst_solver_per_active                1400
% 3.46/0.99  --inst_solver_calls_frac                1.
% 3.46/0.99  --inst_passive_queue_type               priority_queues
% 3.46/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.46/0.99  --inst_passive_queues_freq              [25;2]
% 3.46/0.99  --inst_dismatching                      true
% 3.46/0.99  --inst_eager_unprocessed_to_passive     true
% 3.46/0.99  --inst_prop_sim_given                   true
% 3.46/0.99  --inst_prop_sim_new                     false
% 3.46/0.99  --inst_subs_new                         false
% 3.46/0.99  --inst_eq_res_simp                      false
% 3.46/0.99  --inst_subs_given                       false
% 3.46/0.99  --inst_orphan_elimination               true
% 3.46/0.99  --inst_learning_loop_flag               true
% 3.46/0.99  --inst_learning_start                   3000
% 3.46/0.99  --inst_learning_factor                  2
% 3.46/0.99  --inst_start_prop_sim_after_learn       3
% 3.46/0.99  --inst_sel_renew                        solver
% 3.46/0.99  --inst_lit_activity_flag                true
% 3.46/0.99  --inst_restr_to_given                   false
% 3.46/0.99  --inst_activity_threshold               500
% 3.46/0.99  --inst_out_proof                        true
% 3.46/0.99  
% 3.46/0.99  ------ Resolution Options
% 3.46/0.99  
% 3.46/0.99  --resolution_flag                       true
% 3.46/0.99  --res_lit_sel                           adaptive
% 3.46/0.99  --res_lit_sel_side                      none
% 3.46/0.99  --res_ordering                          kbo
% 3.46/0.99  --res_to_prop_solver                    active
% 3.46/0.99  --res_prop_simpl_new                    false
% 3.46/0.99  --res_prop_simpl_given                  true
% 3.46/0.99  --res_passive_queue_type                priority_queues
% 3.46/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.46/0.99  --res_passive_queues_freq               [15;5]
% 3.46/0.99  --res_forward_subs                      full
% 3.46/0.99  --res_backward_subs                     full
% 3.46/0.99  --res_forward_subs_resolution           true
% 3.46/0.99  --res_backward_subs_resolution          true
% 3.46/0.99  --res_orphan_elimination                true
% 3.46/0.99  --res_time_limit                        2.
% 3.46/0.99  --res_out_proof                         true
% 3.46/0.99  
% 3.46/0.99  ------ Superposition Options
% 3.46/0.99  
% 3.46/0.99  --superposition_flag                    true
% 3.46/0.99  --sup_passive_queue_type                priority_queues
% 3.46/0.99  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.46/0.99  --sup_passive_queues_freq               [1;4]
% 3.46/0.99  --demod_completeness_check              fast
% 3.46/0.99  --demod_use_ground                      true
% 3.46/0.99  --sup_to_prop_solver                    passive
% 3.46/0.99  --sup_prop_simpl_new                    true
% 3.46/0.99  --sup_prop_simpl_given                  true
% 3.46/0.99  --sup_fun_splitting                     false
% 3.46/0.99  --sup_smt_interval                      50000
% 3.46/0.99  
% 3.46/0.99  ------ Superposition Simplification Setup
% 3.46/0.99  
% 3.46/0.99  --sup_indices_passive                   []
% 3.46/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.46/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.46/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.46/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.46/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.46/0.99  --sup_full_bw                           [BwDemod]
% 3.46/0.99  --sup_immed_triv                        [TrivRules]
% 3.46/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.46/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.46/0.99  --sup_immed_bw_main                     []
% 3.46/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.46/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.46/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.46/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.46/0.99  
% 3.46/0.99  ------ Combination Options
% 3.46/0.99  
% 3.46/0.99  --comb_res_mult                         3
% 3.46/0.99  --comb_sup_mult                         2
% 3.46/0.99  --comb_inst_mult                        10
% 3.46/0.99  
% 3.46/0.99  ------ Debug Options
% 3.46/0.99  
% 3.46/0.99  --dbg_backtrace                         false
% 3.46/0.99  --dbg_dump_prop_clauses                 false
% 3.46/0.99  --dbg_dump_prop_clauses_file            -
% 3.46/0.99  --dbg_out_stat                          false
% 3.46/0.99  
% 3.46/0.99  
% 3.46/0.99  
% 3.46/0.99  
% 3.46/0.99  ------ Proving...
% 3.46/0.99  
% 3.46/0.99  
% 3.46/0.99  % SZS status Theorem for theBenchmark.p
% 3.46/0.99  
% 3.46/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.46/0.99  
% 3.46/0.99  fof(f11,conjecture,(
% 3.46/0.99    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 3.46/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.46/0.99  
% 3.46/0.99  fof(f12,negated_conjecture,(
% 3.46/0.99    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 3.46/0.99    inference(negated_conjecture,[],[f11])).
% 3.46/0.99  
% 3.46/0.99  fof(f20,plain,(
% 3.46/0.99    ? [X0,X1,X2] : ((~r1_tarski(X0,X1) & (r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 3.46/0.99    inference(ennf_transformation,[],[f12])).
% 3.46/0.99  
% 3.46/0.99  fof(f21,plain,(
% 3.46/0.99    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 3.46/0.99    inference(flattening,[],[f20])).
% 3.46/0.99  
% 3.46/0.99  fof(f25,plain,(
% 3.46/0.99    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_tarski(sK0,sK1) & r1_tarski(sK0,k2_relat_1(sK2)) & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 3.46/0.99    introduced(choice_axiom,[])).
% 3.46/0.99  
% 3.46/0.99  fof(f26,plain,(
% 3.46/0.99    ~r1_tarski(sK0,sK1) & r1_tarski(sK0,k2_relat_1(sK2)) & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 3.46/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f25])).
% 3.46/0.99  
% 3.46/0.99  fof(f40,plain,(
% 3.46/0.99    v1_relat_1(sK2)),
% 3.46/0.99    inference(cnf_transformation,[],[f26])).
% 3.46/0.99  
% 3.46/0.99  fof(f8,axiom,(
% 3.46/0.99    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k3_xboole_0(X0,X1)))),
% 3.46/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.46/0.99  
% 3.46/0.99  fof(f14,plain,(
% 3.46/0.99    ! [X0,X1,X2] : (k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k3_xboole_0(X0,X1)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 3.46/0.99    inference(ennf_transformation,[],[f8])).
% 3.46/0.99  
% 3.46/0.99  fof(f15,plain,(
% 3.46/0.99    ! [X0,X1,X2] : (k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.46/0.99    inference(flattening,[],[f14])).
% 3.46/0.99  
% 3.46/0.99  fof(f37,plain,(
% 3.46/0.99    ( ! [X2,X0,X1] : (k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.46/0.99    inference(cnf_transformation,[],[f15])).
% 3.46/0.99  
% 3.46/0.99  fof(f7,axiom,(
% 3.46/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.46/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.46/0.99  
% 3.46/0.99  fof(f36,plain,(
% 3.46/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.46/0.99    inference(cnf_transformation,[],[f7])).
% 3.46/0.99  
% 3.46/0.99  fof(f6,axiom,(
% 3.46/0.99    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.46/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.46/0.99  
% 3.46/0.99  fof(f35,plain,(
% 3.46/0.99    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.46/0.99    inference(cnf_transformation,[],[f6])).
% 3.46/0.99  
% 3.46/0.99  fof(f45,plain,(
% 3.46/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 3.46/0.99    inference(definition_unfolding,[],[f36,f35])).
% 3.46/0.99  
% 3.46/0.99  fof(f51,plain,(
% 3.46/0.99    ( ! [X2,X0,X1] : (k1_setfam_1(k1_enumset1(k10_relat_1(X2,X0),k10_relat_1(X2,X0),k10_relat_1(X2,X1))) = k10_relat_1(X2,k1_setfam_1(k1_enumset1(X0,X0,X1))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.46/0.99    inference(definition_unfolding,[],[f37,f45,f45])).
% 3.46/0.99  
% 3.46/0.99  fof(f41,plain,(
% 3.46/0.99    v1_funct_1(sK2)),
% 3.46/0.99    inference(cnf_transformation,[],[f26])).
% 3.46/0.99  
% 3.46/0.99  fof(f42,plain,(
% 3.46/0.99    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),
% 3.46/0.99    inference(cnf_transformation,[],[f26])).
% 3.46/0.99  
% 3.46/0.99  fof(f5,axiom,(
% 3.46/0.99    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.46/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.46/0.99  
% 3.46/0.99  fof(f13,plain,(
% 3.46/0.99    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.46/0.99    inference(ennf_transformation,[],[f5])).
% 3.46/0.99  
% 3.46/0.99  fof(f34,plain,(
% 3.46/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 3.46/0.99    inference(cnf_transformation,[],[f13])).
% 3.46/0.99  
% 3.46/0.99  fof(f50,plain,(
% 3.46/0.99    ( ! [X0,X1] : (k1_setfam_1(k1_enumset1(X0,X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 3.46/0.99    inference(definition_unfolding,[],[f34,f45])).
% 3.46/0.99  
% 3.46/0.99  fof(f9,axiom,(
% 3.46/0.99    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 3.46/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.46/0.99  
% 3.46/0.99  fof(f16,plain,(
% 3.46/0.99    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.46/0.99    inference(ennf_transformation,[],[f9])).
% 3.46/0.99  
% 3.46/0.99  fof(f17,plain,(
% 3.46/0.99    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.46/0.99    inference(flattening,[],[f16])).
% 3.46/0.99  
% 3.46/0.99  fof(f38,plain,(
% 3.46/0.99    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.46/0.99    inference(cnf_transformation,[],[f17])).
% 3.46/0.99  
% 3.46/0.99  fof(f43,plain,(
% 3.46/0.99    r1_tarski(sK0,k2_relat_1(sK2))),
% 3.46/0.99    inference(cnf_transformation,[],[f26])).
% 3.46/0.99  
% 3.46/0.99  fof(f10,axiom,(
% 3.46/0.99    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 3.46/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.46/0.99  
% 3.46/0.99  fof(f18,plain,(
% 3.46/0.99    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.46/0.99    inference(ennf_transformation,[],[f10])).
% 3.46/0.99  
% 3.46/0.99  fof(f19,plain,(
% 3.46/0.99    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.46/0.99    inference(flattening,[],[f18])).
% 3.46/0.99  
% 3.46/0.99  fof(f39,plain,(
% 3.46/0.99    ( ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.46/0.99    inference(cnf_transformation,[],[f19])).
% 3.46/0.99  
% 3.46/0.99  fof(f4,axiom,(
% 3.46/0.99    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 3.46/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.46/0.99  
% 3.46/0.99  fof(f33,plain,(
% 3.46/0.99    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 3.46/0.99    inference(cnf_transformation,[],[f4])).
% 3.46/0.99  
% 3.46/0.99  fof(f49,plain,(
% 3.46/0.99    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X0)) )),
% 3.46/0.99    inference(definition_unfolding,[],[f33,f45])).
% 3.46/0.99  
% 3.46/0.99  fof(f1,axiom,(
% 3.46/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.46/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.46/0.99  
% 3.46/0.99  fof(f22,plain,(
% 3.46/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.46/0.99    inference(nnf_transformation,[],[f1])).
% 3.46/0.99  
% 3.46/0.99  fof(f23,plain,(
% 3.46/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.46/0.99    inference(flattening,[],[f22])).
% 3.46/0.99  
% 3.46/0.99  fof(f29,plain,(
% 3.46/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.46/0.99    inference(cnf_transformation,[],[f23])).
% 3.46/0.99  
% 3.46/0.99  fof(f2,axiom,(
% 3.46/0.99    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 3.46/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.46/0.99  
% 3.46/0.99  fof(f24,plain,(
% 3.46/0.99    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 3.46/0.99    inference(nnf_transformation,[],[f2])).
% 3.46/0.99  
% 3.46/0.99  fof(f30,plain,(
% 3.46/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 3.46/0.99    inference(cnf_transformation,[],[f24])).
% 3.46/0.99  
% 3.46/0.99  fof(f3,axiom,(
% 3.46/0.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.46/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.46/0.99  
% 3.46/0.99  fof(f32,plain,(
% 3.46/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.46/0.99    inference(cnf_transformation,[],[f3])).
% 3.46/0.99  
% 3.46/0.99  fof(f46,plain,(
% 3.46/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1)))) )),
% 3.46/0.99    inference(definition_unfolding,[],[f32,f45])).
% 3.46/0.99  
% 3.46/0.99  fof(f48,plain,(
% 3.46/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1)))) )),
% 3.46/0.99    inference(definition_unfolding,[],[f30,f46])).
% 3.46/0.99  
% 3.46/0.99  fof(f27,plain,(
% 3.46/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.46/0.99    inference(cnf_transformation,[],[f23])).
% 3.46/0.99  
% 3.46/0.99  fof(f53,plain,(
% 3.46/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.46/0.99    inference(equality_resolution,[],[f27])).
% 3.46/0.99  
% 3.46/0.99  fof(f31,plain,(
% 3.46/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 3.46/0.99    inference(cnf_transformation,[],[f24])).
% 3.46/0.99  
% 3.46/0.99  fof(f47,plain,(
% 3.46/0.99    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1))) | ~r1_tarski(X0,X1)) )),
% 3.46/0.99    inference(definition_unfolding,[],[f31,f46])).
% 3.46/0.99  
% 3.46/0.99  fof(f44,plain,(
% 3.46/0.99    ~r1_tarski(sK0,sK1)),
% 3.46/0.99    inference(cnf_transformation,[],[f26])).
% 3.46/0.99  
% 3.46/0.99  cnf(c_14,negated_conjecture,
% 3.46/0.99      ( v1_relat_1(sK2) ),
% 3.46/0.99      inference(cnf_transformation,[],[f40]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_602,plain,
% 3.46/0.99      ( v1_relat_1(sK2) = iProver_top ),
% 3.46/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_7,plain,
% 3.46/0.99      ( ~ v1_relat_1(X0)
% 3.46/0.99      | ~ v1_funct_1(X0)
% 3.46/0.99      | k1_setfam_1(k1_enumset1(k10_relat_1(X0,X1),k10_relat_1(X0,X1),k10_relat_1(X0,X2))) = k10_relat_1(X0,k1_setfam_1(k1_enumset1(X1,X1,X2))) ),
% 3.46/0.99      inference(cnf_transformation,[],[f51]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_609,plain,
% 3.46/0.99      ( k1_setfam_1(k1_enumset1(k10_relat_1(X0,X1),k10_relat_1(X0,X1),k10_relat_1(X0,X2))) = k10_relat_1(X0,k1_setfam_1(k1_enumset1(X1,X1,X2)))
% 3.46/0.99      | v1_relat_1(X0) != iProver_top
% 3.46/0.99      | v1_funct_1(X0) != iProver_top ),
% 3.46/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_1376,plain,
% 3.46/0.99      ( k1_setfam_1(k1_enumset1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X0),k10_relat_1(sK2,X1))) = k10_relat_1(sK2,k1_setfam_1(k1_enumset1(X0,X0,X1)))
% 3.46/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.46/0.99      inference(superposition,[status(thm)],[c_602,c_609]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_13,negated_conjecture,
% 3.46/0.99      ( v1_funct_1(sK2) ),
% 3.46/0.99      inference(cnf_transformation,[],[f41]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_16,plain,
% 3.46/0.99      ( v1_funct_1(sK2) = iProver_top ),
% 3.46/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_2291,plain,
% 3.46/0.99      ( k1_setfam_1(k1_enumset1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X0),k10_relat_1(sK2,X1))) = k10_relat_1(sK2,k1_setfam_1(k1_enumset1(X0,X0,X1))) ),
% 3.46/0.99      inference(global_propositional_subsumption,
% 3.46/0.99                [status(thm)],
% 3.46/0.99                [c_1376,c_16]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_12,negated_conjecture,
% 3.46/0.99      ( r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
% 3.46/0.99      inference(cnf_transformation,[],[f42]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_604,plain,
% 3.46/0.99      ( r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) = iProver_top ),
% 3.46/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_6,plain,
% 3.46/0.99      ( ~ r1_tarski(X0,X1) | k1_setfam_1(k1_enumset1(X0,X0,X1)) = X0 ),
% 3.46/0.99      inference(cnf_transformation,[],[f50]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_610,plain,
% 3.46/0.99      ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = X0
% 3.46/0.99      | r1_tarski(X0,X1) != iProver_top ),
% 3.46/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_887,plain,
% 3.46/0.99      ( k1_setfam_1(k1_enumset1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))) = k10_relat_1(sK2,sK0) ),
% 3.46/0.99      inference(superposition,[status(thm)],[c_604,c_610]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_2303,plain,
% 3.46/0.99      ( k10_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,sK1))) = k10_relat_1(sK2,sK0) ),
% 3.46/0.99      inference(superposition,[status(thm)],[c_2291,c_887]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_8,plain,
% 3.46/0.99      ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
% 3.46/0.99      | ~ v1_relat_1(X0)
% 3.46/0.99      | ~ v1_funct_1(X0) ),
% 3.46/0.99      inference(cnf_transformation,[],[f38]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_608,plain,
% 3.46/0.99      ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1) = iProver_top
% 3.46/0.99      | v1_relat_1(X0) != iProver_top
% 3.46/0.99      | v1_funct_1(X0) != iProver_top ),
% 3.46/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_3417,plain,
% 3.46/0.99      ( r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,sK0)),k1_setfam_1(k1_enumset1(sK0,sK0,sK1))) = iProver_top
% 3.46/0.99      | v1_relat_1(sK2) != iProver_top
% 3.46/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.46/0.99      inference(superposition,[status(thm)],[c_2303,c_608]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_11,negated_conjecture,
% 3.46/0.99      ( r1_tarski(sK0,k2_relat_1(sK2)) ),
% 3.46/0.99      inference(cnf_transformation,[],[f43]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_605,plain,
% 3.46/0.99      ( r1_tarski(sK0,k2_relat_1(sK2)) = iProver_top ),
% 3.46/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_9,plain,
% 3.46/0.99      ( ~ r1_tarski(X0,k2_relat_1(X1))
% 3.46/0.99      | ~ v1_relat_1(X1)
% 3.46/0.99      | ~ v1_funct_1(X1)
% 3.46/0.99      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ),
% 3.46/0.99      inference(cnf_transformation,[],[f39]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_607,plain,
% 3.46/0.99      ( k9_relat_1(X0,k10_relat_1(X0,X1)) = X1
% 3.46/0.99      | r1_tarski(X1,k2_relat_1(X0)) != iProver_top
% 3.46/0.99      | v1_relat_1(X0) != iProver_top
% 3.46/0.99      | v1_funct_1(X0) != iProver_top ),
% 3.46/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_1186,plain,
% 3.46/0.99      ( k9_relat_1(sK2,k10_relat_1(sK2,sK0)) = sK0
% 3.46/0.99      | v1_relat_1(sK2) != iProver_top
% 3.46/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.46/0.99      inference(superposition,[status(thm)],[c_605,c_607]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_765,plain,
% 3.46/0.99      ( ~ r1_tarski(sK0,k2_relat_1(sK2))
% 3.46/0.99      | ~ v1_relat_1(sK2)
% 3.46/0.99      | ~ v1_funct_1(sK2)
% 3.46/0.99      | k9_relat_1(sK2,k10_relat_1(sK2,sK0)) = sK0 ),
% 3.46/0.99      inference(instantiation,[status(thm)],[c_9]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_2101,plain,
% 3.46/0.99      ( k9_relat_1(sK2,k10_relat_1(sK2,sK0)) = sK0 ),
% 3.46/0.99      inference(global_propositional_subsumption,
% 3.46/0.99                [status(thm)],
% 3.46/0.99                [c_1186,c_14,c_13,c_11,c_765]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_3445,plain,
% 3.46/0.99      ( r1_tarski(sK0,k1_setfam_1(k1_enumset1(sK0,sK0,sK1))) = iProver_top
% 3.46/0.99      | v1_relat_1(sK2) != iProver_top
% 3.46/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.46/0.99      inference(light_normalisation,[status(thm)],[c_3417,c_2101]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_15,plain,
% 3.46/0.99      ( v1_relat_1(sK2) = iProver_top ),
% 3.46/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_3977,plain,
% 3.46/0.99      ( r1_tarski(sK0,k1_setfam_1(k1_enumset1(sK0,sK0,sK1))) = iProver_top ),
% 3.46/0.99      inference(global_propositional_subsumption,
% 3.46/0.99                [status(thm)],
% 3.46/0.99                [c_3445,c_15,c_16]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_5,plain,
% 3.46/0.99      ( r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X0) ),
% 3.46/0.99      inference(cnf_transformation,[],[f49]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_611,plain,
% 3.46/0.99      ( r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X0) = iProver_top ),
% 3.46/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_0,plain,
% 3.46/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.46/0.99      inference(cnf_transformation,[],[f29]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_615,plain,
% 3.46/0.99      ( X0 = X1
% 3.46/0.99      | r1_tarski(X0,X1) != iProver_top
% 3.46/0.99      | r1_tarski(X1,X0) != iProver_top ),
% 3.46/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_1217,plain,
% 3.46/0.99      ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = X0
% 3.46/0.99      | r1_tarski(X0,k1_setfam_1(k1_enumset1(X0,X0,X1))) != iProver_top ),
% 3.46/0.99      inference(superposition,[status(thm)],[c_611,c_615]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_3985,plain,
% 3.46/0.99      ( k1_setfam_1(k1_enumset1(sK0,sK0,sK1)) = sK0 ),
% 3.46/0.99      inference(superposition,[status(thm)],[c_3977,c_1217]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_4,plain,
% 3.46/0.99      ( r1_tarski(X0,X1)
% 3.46/0.99      | k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1))) != k1_xboole_0 ),
% 3.46/0.99      inference(cnf_transformation,[],[f48]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_612,plain,
% 3.46/0.99      ( k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1))) != k1_xboole_0
% 3.46/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 3.46/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_4241,plain,
% 3.46/0.99      ( k5_xboole_0(sK0,sK0) != k1_xboole_0
% 3.46/0.99      | r1_tarski(sK0,sK1) = iProver_top ),
% 3.46/0.99      inference(superposition,[status(thm)],[c_3985,c_612]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_2,plain,
% 3.46/0.99      ( r1_tarski(X0,X0) ),
% 3.46/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_614,plain,
% 3.46/0.99      ( r1_tarski(X0,X0) = iProver_top ),
% 3.46/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_3,plain,
% 3.46/0.99      ( ~ r1_tarski(X0,X1)
% 3.46/0.99      | k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1))) = k1_xboole_0 ),
% 3.46/0.99      inference(cnf_transformation,[],[f47]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_613,plain,
% 3.46/0.99      ( k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1))) = k1_xboole_0
% 3.46/0.99      | r1_tarski(X0,X1) != iProver_top ),
% 3.46/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_1026,plain,
% 3.46/0.99      ( k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X0))) = k1_xboole_0 ),
% 3.46/0.99      inference(superposition,[status(thm)],[c_614,c_613]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_884,plain,
% 3.46/0.99      ( k1_setfam_1(k1_enumset1(X0,X0,X0)) = X0 ),
% 3.46/0.99      inference(superposition,[status(thm)],[c_614,c_610]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_1670,plain,
% 3.46/0.99      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.46/0.99      inference(light_normalisation,[status(thm)],[c_1026,c_884]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_4245,plain,
% 3.46/0.99      ( k1_xboole_0 != k1_xboole_0 | r1_tarski(sK0,sK1) = iProver_top ),
% 3.46/0.99      inference(demodulation,[status(thm)],[c_4241,c_1670]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_4246,plain,
% 3.46/0.99      ( r1_tarski(sK0,sK1) = iProver_top ),
% 3.46/0.99      inference(equality_resolution_simp,[status(thm)],[c_4245]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_10,negated_conjecture,
% 3.46/0.99      ( ~ r1_tarski(sK0,sK1) ),
% 3.46/0.99      inference(cnf_transformation,[],[f44]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_19,plain,
% 3.46/0.99      ( r1_tarski(sK0,sK1) != iProver_top ),
% 3.46/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(contradiction,plain,
% 3.46/0.99      ( $false ),
% 3.46/0.99      inference(minisat,[status(thm)],[c_4246,c_19]) ).
% 3.46/0.99  
% 3.46/0.99  
% 3.46/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.46/0.99  
% 3.46/0.99  ------                               Statistics
% 3.46/0.99  
% 3.46/0.99  ------ Selected
% 3.46/0.99  
% 3.46/0.99  total_time:                             0.167
% 3.46/0.99  
%------------------------------------------------------------------------------
