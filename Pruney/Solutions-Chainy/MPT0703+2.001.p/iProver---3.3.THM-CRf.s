%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:52:15 EST 2020

% Result     : Theorem 51.50s
% Output     : CNFRefutation 51.50s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 429 expanded)
%              Number of clauses        :   59 ( 128 expanded)
%              Number of leaves         :   12 ( 100 expanded)
%              Depth                    :   18
%              Number of atoms          :  216 (1007 expanded)
%              Number of equality atoms :  102 ( 335 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(X0,k2_relat_1(X2))
          & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f24,plain,
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

fof(f25,plain,
    ( ~ r1_tarski(sK0,sK1)
    & r1_tarski(sK0,k2_relat_1(sK2))
    & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f24])).

fof(f38,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f43,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f35,f34])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k1_setfam_1(k1_enumset1(k10_relat_1(X2,X0),k10_relat_1(X2,X0),k10_relat_1(X2,X1))) = k10_relat_1(X2,k1_setfam_1(k1_enumset1(X0,X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f36,f43,f43])).

fof(f39,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f40,plain,(
    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f25])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f32,f43])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f46,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(definition_unfolding,[],[f33,f34,f34])).

fof(f41,plain,(
    r1_tarski(sK0,k2_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f25])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f44,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f31,f43])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f49,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f26])).

fof(f28,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f37,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f42,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_14,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_424,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_setfam_1(k1_enumset1(k10_relat_1(X0,X1),k10_relat_1(X0,X1),k10_relat_1(X0,X2))) = k10_relat_1(X0,k1_setfam_1(k1_enumset1(X1,X1,X2))) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_430,plain,
    ( k1_setfam_1(k1_enumset1(k10_relat_1(X0,X1),k10_relat_1(X0,X1),k10_relat_1(X0,X2))) = k10_relat_1(X0,k1_setfam_1(k1_enumset1(X1,X1,X2)))
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1428,plain,
    ( k1_setfam_1(k1_enumset1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X0),k10_relat_1(sK2,X1))) = k10_relat_1(sK2,k1_setfam_1(k1_enumset1(X0,X0,X1)))
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_424,c_430])).

cnf(c_13,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_16,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_6982,plain,
    ( k1_setfam_1(k1_enumset1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X0),k10_relat_1(sK2,X1))) = k10_relat_1(sK2,k1_setfam_1(k1_enumset1(X0,X0,X1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1428,c_16])).

cnf(c_12,negated_conjecture,
    ( r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_426,plain,
    ( r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | k1_setfam_1(k1_enumset1(X0,X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_431,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1072,plain,
    ( k1_setfam_1(k1_enumset1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))) = k10_relat_1(sK2,sK0) ),
    inference(superposition,[status(thm)],[c_426,c_431])).

cnf(c_6998,plain,
    ( k10_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,sK1))) = k10_relat_1(sK2,sK0) ),
    inference(superposition,[status(thm)],[c_6982,c_1072])).

cnf(c_7,plain,
    ( k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_11,negated_conjecture,
    ( r1_tarski(sK0,k2_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_427,plain,
    ( r1_tarski(sK0,k2_relat_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_5,plain,
    ( r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_432,plain,
    ( r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_433,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_861,plain,
    ( k2_xboole_0(k1_setfam_1(k1_enumset1(X0,X0,X1)),X0) = X0 ),
    inference(superposition,[status(thm)],[c_432,c_433])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_434,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(k2_xboole_0(X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1965,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X2)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_861,c_434])).

cnf(c_4593,plain,
    ( k2_xboole_0(k1_setfam_1(k1_enumset1(X0,X0,X1)),X2) = X2
    | r1_tarski(X0,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1965,c_433])).

cnf(c_5101,plain,
    ( k2_xboole_0(k1_setfam_1(k1_enumset1(sK0,sK0,X0)),k2_relat_1(sK2)) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_427,c_4593])).

cnf(c_5307,plain,
    ( k2_xboole_0(k1_setfam_1(k1_enumset1(X0,X0,sK0)),k2_relat_1(sK2)) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_7,c_5101])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_435,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1246,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_435,c_434])).

cnf(c_1703,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,k2_xboole_0(X0,X1))) = X0 ),
    inference(superposition,[status(thm)],[c_1246,c_431])).

cnf(c_710,plain,
    ( r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_432])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_436,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1256,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = X1
    | r1_tarski(X1,k1_setfam_1(k1_enumset1(X0,X0,X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_710,c_436])).

cnf(c_6314,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = X1
    | r1_tarski(X1,k1_setfam_1(k1_enumset1(X1,X1,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_1256])).

cnf(c_6356,plain,
    ( k1_setfam_1(k1_enumset1(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1),X0)) = X0
    | r1_tarski(X0,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1703,c_6314])).

cnf(c_39,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_13067,plain,
    ( k1_setfam_1(k1_enumset1(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1),X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6356,c_39])).

cnf(c_13103,plain,
    ( k1_setfam_1(k1_enumset1(k2_relat_1(sK2),k2_relat_1(sK2),k1_setfam_1(k1_enumset1(X0,X0,sK0)))) = k1_setfam_1(k1_enumset1(X0,X0,sK0)) ),
    inference(superposition,[status(thm)],[c_5307,c_13067])).

cnf(c_13377,plain,
    ( k1_setfam_1(k1_enumset1(k2_relat_1(sK2),k2_relat_1(sK2),k1_setfam_1(k1_enumset1(sK0,sK0,X0)))) = k1_setfam_1(k1_enumset1(X0,X0,sK0)) ),
    inference(superposition,[status(thm)],[c_7,c_13103])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_429,plain,
    ( k9_relat_1(X0,k10_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k2_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1029,plain,
    ( k9_relat_1(X0,k10_relat_1(X0,k1_setfam_1(k1_enumset1(k2_relat_1(X0),k2_relat_1(X0),X1)))) = k1_setfam_1(k1_enumset1(k2_relat_1(X0),k2_relat_1(X0),X1))
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_432,c_429])).

cnf(c_3041,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,k1_setfam_1(k1_enumset1(k2_relat_1(sK2),k2_relat_1(sK2),X0)))) = k1_setfam_1(k1_enumset1(k2_relat_1(sK2),k2_relat_1(sK2),X0))
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_424,c_1029])).

cnf(c_22196,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,k1_setfam_1(k1_enumset1(k2_relat_1(sK2),k2_relat_1(sK2),X0)))) = k1_setfam_1(k1_enumset1(k2_relat_1(sK2),k2_relat_1(sK2),X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3041,c_16])).

cnf(c_22209,plain,
    ( k1_setfam_1(k1_enumset1(k2_relat_1(sK2),k2_relat_1(sK2),k1_setfam_1(k1_enumset1(sK0,sK0,X0)))) = k9_relat_1(sK2,k10_relat_1(sK2,k1_setfam_1(k1_enumset1(X0,X0,sK0)))) ),
    inference(superposition,[status(thm)],[c_13377,c_22196])).

cnf(c_99209,plain,
    ( k1_setfam_1(k1_enumset1(k2_relat_1(sK2),k2_relat_1(sK2),k1_setfam_1(k1_enumset1(sK0,sK0,X0)))) = k9_relat_1(sK2,k10_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,X0)))) ),
    inference(superposition,[status(thm)],[c_7,c_22209])).

cnf(c_13490,plain,
    ( r1_tarski(k1_setfam_1(k1_enumset1(k2_relat_1(sK2),k2_relat_1(sK2),k1_setfam_1(k1_enumset1(sK0,sK0,X0)))),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_13377,c_432])).

cnf(c_101292,plain,
    ( r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,X0)))),X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_99209,c_13490])).

cnf(c_201999,plain,
    ( r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,sK0)),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_6998,c_101292])).

cnf(c_1030,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,sK0)) = sK0
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_427,c_429])).

cnf(c_571,plain,
    ( ~ r1_tarski(sK0,k2_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k9_relat_1(sK2,k10_relat_1(sK2,sK0)) = sK0 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_3480,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,sK0)) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1030,c_14,c_13,c_11,c_571])).

cnf(c_202649,plain,
    ( r1_tarski(sK0,sK1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_201999,c_3480])).

cnf(c_10,negated_conjecture,
    ( ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_19,plain,
    ( r1_tarski(sK0,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_202649,c_19])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 17:19:29 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running in FOF mode
% 51.50/6.94  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 51.50/6.94  
% 51.50/6.94  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 51.50/6.94  
% 51.50/6.94  ------  iProver source info
% 51.50/6.94  
% 51.50/6.94  git: date: 2020-06-30 10:37:57 +0100
% 51.50/6.94  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 51.50/6.94  git: non_committed_changes: false
% 51.50/6.94  git: last_make_outside_of_git: false
% 51.50/6.94  
% 51.50/6.94  ------ 
% 51.50/6.94  
% 51.50/6.94  ------ Input Options
% 51.50/6.94  
% 51.50/6.94  --out_options                           all
% 51.50/6.94  --tptp_safe_out                         true
% 51.50/6.94  --problem_path                          ""
% 51.50/6.94  --include_path                          ""
% 51.50/6.94  --clausifier                            res/vclausify_rel
% 51.50/6.94  --clausifier_options                    --mode clausify
% 51.50/6.94  --stdin                                 false
% 51.50/6.94  --stats_out                             sel
% 51.50/6.94  
% 51.50/6.94  ------ General Options
% 51.50/6.94  
% 51.50/6.94  --fof                                   false
% 51.50/6.94  --time_out_real                         604.99
% 51.50/6.94  --time_out_virtual                      -1.
% 51.50/6.94  --symbol_type_check                     false
% 51.50/6.94  --clausify_out                          false
% 51.50/6.94  --sig_cnt_out                           false
% 51.50/6.94  --trig_cnt_out                          false
% 51.50/6.94  --trig_cnt_out_tolerance                1.
% 51.50/6.94  --trig_cnt_out_sk_spl                   false
% 51.50/6.94  --abstr_cl_out                          false
% 51.50/6.94  
% 51.50/6.94  ------ Global Options
% 51.50/6.94  
% 51.50/6.94  --schedule                              none
% 51.50/6.94  --add_important_lit                     false
% 51.50/6.94  --prop_solver_per_cl                    1000
% 51.50/6.94  --min_unsat_core                        false
% 51.50/6.94  --soft_assumptions                      false
% 51.50/6.94  --soft_lemma_size                       3
% 51.50/6.94  --prop_impl_unit_size                   0
% 51.50/6.94  --prop_impl_unit                        []
% 51.50/6.94  --share_sel_clauses                     true
% 51.50/6.94  --reset_solvers                         false
% 51.50/6.94  --bc_imp_inh                            [conj_cone]
% 51.50/6.94  --conj_cone_tolerance                   3.
% 51.50/6.94  --extra_neg_conj                        none
% 51.50/6.94  --large_theory_mode                     true
% 51.50/6.94  --prolific_symb_bound                   200
% 51.50/6.94  --lt_threshold                          2000
% 51.50/6.94  --clause_weak_htbl                      true
% 51.50/6.94  --gc_record_bc_elim                     false
% 51.50/6.94  
% 51.50/6.94  ------ Preprocessing Options
% 51.50/6.94  
% 51.50/6.94  --preprocessing_flag                    true
% 51.50/6.94  --time_out_prep_mult                    0.1
% 51.50/6.94  --splitting_mode                        input
% 51.50/6.94  --splitting_grd                         true
% 51.50/6.94  --splitting_cvd                         false
% 51.50/6.94  --splitting_cvd_svl                     false
% 51.50/6.94  --splitting_nvd                         32
% 51.50/6.94  --sub_typing                            true
% 51.50/6.94  --prep_gs_sim                           false
% 51.50/6.94  --prep_unflatten                        true
% 51.50/6.94  --prep_res_sim                          true
% 51.50/6.94  --prep_upred                            true
% 51.50/6.94  --prep_sem_filter                       exhaustive
% 51.50/6.94  --prep_sem_filter_out                   false
% 51.50/6.94  --pred_elim                             false
% 51.50/6.94  --res_sim_input                         true
% 51.50/6.94  --eq_ax_congr_red                       true
% 51.50/6.94  --pure_diseq_elim                       true
% 51.50/6.94  --brand_transform                       false
% 51.50/6.94  --non_eq_to_eq                          false
% 51.50/6.94  --prep_def_merge                        true
% 51.50/6.94  --prep_def_merge_prop_impl              false
% 51.50/6.94  --prep_def_merge_mbd                    true
% 51.50/6.94  --prep_def_merge_tr_red                 false
% 51.50/6.94  --prep_def_merge_tr_cl                  false
% 51.50/6.94  --smt_preprocessing                     true
% 51.50/6.94  --smt_ac_axioms                         fast
% 51.50/6.94  --preprocessed_out                      false
% 51.50/6.94  --preprocessed_stats                    false
% 51.50/6.94  
% 51.50/6.94  ------ Abstraction refinement Options
% 51.50/6.94  
% 51.50/6.94  --abstr_ref                             []
% 51.50/6.94  --abstr_ref_prep                        false
% 51.50/6.94  --abstr_ref_until_sat                   false
% 51.50/6.94  --abstr_ref_sig_restrict                funpre
% 51.50/6.94  --abstr_ref_af_restrict_to_split_sk     false
% 51.50/6.94  --abstr_ref_under                       []
% 51.50/6.94  
% 51.50/6.94  ------ SAT Options
% 51.50/6.94  
% 51.50/6.94  --sat_mode                              false
% 51.50/6.94  --sat_fm_restart_options                ""
% 51.50/6.94  --sat_gr_def                            false
% 51.50/6.94  --sat_epr_types                         true
% 51.50/6.94  --sat_non_cyclic_types                  false
% 51.50/6.94  --sat_finite_models                     false
% 51.50/6.94  --sat_fm_lemmas                         false
% 51.50/6.94  --sat_fm_prep                           false
% 51.50/6.94  --sat_fm_uc_incr                        true
% 51.50/6.94  --sat_out_model                         small
% 51.50/6.94  --sat_out_clauses                       false
% 51.50/6.94  
% 51.50/6.94  ------ QBF Options
% 51.50/6.94  
% 51.50/6.94  --qbf_mode                              false
% 51.50/6.94  --qbf_elim_univ                         false
% 51.50/6.94  --qbf_dom_inst                          none
% 51.50/6.94  --qbf_dom_pre_inst                      false
% 51.50/6.94  --qbf_sk_in                             false
% 51.50/6.94  --qbf_pred_elim                         true
% 51.50/6.94  --qbf_split                             512
% 51.50/6.94  
% 51.50/6.94  ------ BMC1 Options
% 51.50/6.94  
% 51.50/6.94  --bmc1_incremental                      false
% 51.50/6.94  --bmc1_axioms                           reachable_all
% 51.50/6.94  --bmc1_min_bound                        0
% 51.50/6.94  --bmc1_max_bound                        -1
% 51.50/6.94  --bmc1_max_bound_default                -1
% 51.50/6.94  --bmc1_symbol_reachability              true
% 51.50/6.94  --bmc1_property_lemmas                  false
% 51.50/6.94  --bmc1_k_induction                      false
% 51.50/6.94  --bmc1_non_equiv_states                 false
% 51.50/6.94  --bmc1_deadlock                         false
% 51.50/6.94  --bmc1_ucm                              false
% 51.50/6.94  --bmc1_add_unsat_core                   none
% 51.50/6.94  --bmc1_unsat_core_children              false
% 51.50/6.94  --bmc1_unsat_core_extrapolate_axioms    false
% 51.50/6.94  --bmc1_out_stat                         full
% 51.50/6.94  --bmc1_ground_init                      false
% 51.50/6.94  --bmc1_pre_inst_next_state              false
% 51.50/6.94  --bmc1_pre_inst_state                   false
% 51.50/6.94  --bmc1_pre_inst_reach_state             false
% 51.50/6.94  --bmc1_out_unsat_core                   false
% 51.50/6.94  --bmc1_aig_witness_out                  false
% 51.50/6.94  --bmc1_verbose                          false
% 51.50/6.94  --bmc1_dump_clauses_tptp                false
% 51.50/6.94  --bmc1_dump_unsat_core_tptp             false
% 51.50/6.94  --bmc1_dump_file                        -
% 51.50/6.94  --bmc1_ucm_expand_uc_limit              128
% 51.50/6.94  --bmc1_ucm_n_expand_iterations          6
% 51.50/6.94  --bmc1_ucm_extend_mode                  1
% 51.50/6.94  --bmc1_ucm_init_mode                    2
% 51.50/6.94  --bmc1_ucm_cone_mode                    none
% 51.50/6.94  --bmc1_ucm_reduced_relation_type        0
% 51.50/6.94  --bmc1_ucm_relax_model                  4
% 51.50/6.94  --bmc1_ucm_full_tr_after_sat            true
% 51.50/6.94  --bmc1_ucm_expand_neg_assumptions       false
% 51.50/6.94  --bmc1_ucm_layered_model                none
% 51.50/6.94  --bmc1_ucm_max_lemma_size               10
% 51.50/6.94  
% 51.50/6.94  ------ AIG Options
% 51.50/6.94  
% 51.50/6.94  --aig_mode                              false
% 51.50/6.94  
% 51.50/6.94  ------ Instantiation Options
% 51.50/6.94  
% 51.50/6.94  --instantiation_flag                    true
% 51.50/6.94  --inst_sos_flag                         false
% 51.50/6.94  --inst_sos_phase                        true
% 51.50/6.94  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 51.50/6.94  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 51.50/6.94  --inst_lit_sel_side                     num_symb
% 51.50/6.94  --inst_solver_per_active                1400
% 51.50/6.94  --inst_solver_calls_frac                1.
% 51.50/6.94  --inst_passive_queue_type               priority_queues
% 51.50/6.94  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 51.50/6.94  --inst_passive_queues_freq              [25;2]
% 51.50/6.94  --inst_dismatching                      true
% 51.50/6.94  --inst_eager_unprocessed_to_passive     true
% 51.50/6.94  --inst_prop_sim_given                   true
% 51.50/6.94  --inst_prop_sim_new                     false
% 51.50/6.94  --inst_subs_new                         false
% 51.50/6.94  --inst_eq_res_simp                      false
% 51.50/6.94  --inst_subs_given                       false
% 51.50/6.94  --inst_orphan_elimination               true
% 51.50/6.94  --inst_learning_loop_flag               true
% 51.50/6.94  --inst_learning_start                   3000
% 51.50/6.94  --inst_learning_factor                  2
% 51.50/6.94  --inst_start_prop_sim_after_learn       3
% 51.50/6.94  --inst_sel_renew                        solver
% 51.50/6.94  --inst_lit_activity_flag                true
% 51.50/6.94  --inst_restr_to_given                   false
% 51.50/6.94  --inst_activity_threshold               500
% 51.50/6.94  --inst_out_proof                        true
% 51.50/6.94  
% 51.50/6.94  ------ Resolution Options
% 51.50/6.94  
% 51.50/6.94  --resolution_flag                       true
% 51.50/6.94  --res_lit_sel                           adaptive
% 51.50/6.94  --res_lit_sel_side                      none
% 51.50/6.94  --res_ordering                          kbo
% 51.50/6.94  --res_to_prop_solver                    active
% 51.50/6.94  --res_prop_simpl_new                    false
% 51.50/6.94  --res_prop_simpl_given                  true
% 51.50/6.94  --res_passive_queue_type                priority_queues
% 51.50/6.94  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 51.50/6.94  --res_passive_queues_freq               [15;5]
% 51.50/6.94  --res_forward_subs                      full
% 51.50/6.94  --res_backward_subs                     full
% 51.50/6.94  --res_forward_subs_resolution           true
% 51.50/6.94  --res_backward_subs_resolution          true
% 51.50/6.94  --res_orphan_elimination                true
% 51.50/6.94  --res_time_limit                        2.
% 51.50/6.94  --res_out_proof                         true
% 51.50/6.94  
% 51.50/6.94  ------ Superposition Options
% 51.50/6.94  
% 51.50/6.94  --superposition_flag                    true
% 51.50/6.94  --sup_passive_queue_type                priority_queues
% 51.50/6.94  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 51.50/6.94  --sup_passive_queues_freq               [1;4]
% 51.50/6.94  --demod_completeness_check              fast
% 51.50/6.94  --demod_use_ground                      true
% 51.50/6.94  --sup_to_prop_solver                    passive
% 51.50/6.94  --sup_prop_simpl_new                    true
% 51.50/6.94  --sup_prop_simpl_given                  true
% 51.50/6.94  --sup_fun_splitting                     false
% 51.50/6.94  --sup_smt_interval                      50000
% 51.50/6.94  
% 51.50/6.94  ------ Superposition Simplification Setup
% 51.50/6.94  
% 51.50/6.94  --sup_indices_passive                   []
% 51.50/6.94  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 51.50/6.94  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 51.50/6.94  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 51.50/6.94  --sup_full_triv                         [TrivRules;PropSubs]
% 51.50/6.94  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 51.50/6.94  --sup_full_bw                           [BwDemod]
% 51.50/6.94  --sup_immed_triv                        [TrivRules]
% 51.50/6.94  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 51.50/6.94  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 51.50/6.94  --sup_immed_bw_main                     []
% 51.50/6.94  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 51.50/6.94  --sup_input_triv                        [Unflattening;TrivRules]
% 51.50/6.94  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 51.50/6.94  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 51.50/6.94  
% 51.50/6.94  ------ Combination Options
% 51.50/6.94  
% 51.50/6.94  --comb_res_mult                         3
% 51.50/6.94  --comb_sup_mult                         2
% 51.50/6.94  --comb_inst_mult                        10
% 51.50/6.94  
% 51.50/6.94  ------ Debug Options
% 51.50/6.94  
% 51.50/6.94  --dbg_backtrace                         false
% 51.50/6.94  --dbg_dump_prop_clauses                 false
% 51.50/6.94  --dbg_dump_prop_clauses_file            -
% 51.50/6.94  --dbg_out_stat                          false
% 51.50/6.94  ------ Parsing...
% 51.50/6.94  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 51.50/6.94  
% 51.50/6.94  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 51.50/6.94  
% 51.50/6.94  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 51.50/6.94  
% 51.50/6.94  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 51.50/6.94  ------ Proving...
% 51.50/6.94  ------ Problem Properties 
% 51.50/6.94  
% 51.50/6.94  
% 51.50/6.94  clauses                                 14
% 51.50/6.94  conjectures                             5
% 51.50/6.94  EPR                                     5
% 51.50/6.94  Horn                                    14
% 51.50/6.94  unary                                   8
% 51.50/6.94  binary                                  3
% 51.50/6.94  lits                                    24
% 51.50/6.94  lits eq                                 6
% 51.50/6.94  fd_pure                                 0
% 51.50/6.94  fd_pseudo                               0
% 51.50/6.94  fd_cond                                 0
% 51.50/6.94  fd_pseudo_cond                          1
% 51.50/6.94  AC symbols                              0
% 51.50/6.94  
% 51.50/6.94  ------ Input Options Time Limit: Unbounded
% 51.50/6.94  
% 51.50/6.94  
% 51.50/6.94  ------ 
% 51.50/6.94  Current options:
% 51.50/6.94  ------ 
% 51.50/6.94  
% 51.50/6.94  ------ Input Options
% 51.50/6.94  
% 51.50/6.94  --out_options                           all
% 51.50/6.94  --tptp_safe_out                         true
% 51.50/6.94  --problem_path                          ""
% 51.50/6.94  --include_path                          ""
% 51.50/6.94  --clausifier                            res/vclausify_rel
% 51.50/6.94  --clausifier_options                    --mode clausify
% 51.50/6.94  --stdin                                 false
% 51.50/6.94  --stats_out                             sel
% 51.50/6.94  
% 51.50/6.94  ------ General Options
% 51.50/6.94  
% 51.50/6.94  --fof                                   false
% 51.50/6.94  --time_out_real                         604.99
% 51.50/6.94  --time_out_virtual                      -1.
% 51.50/6.94  --symbol_type_check                     false
% 51.50/6.94  --clausify_out                          false
% 51.50/6.94  --sig_cnt_out                           false
% 51.50/6.94  --trig_cnt_out                          false
% 51.50/6.94  --trig_cnt_out_tolerance                1.
% 51.50/6.94  --trig_cnt_out_sk_spl                   false
% 51.50/6.94  --abstr_cl_out                          false
% 51.50/6.94  
% 51.50/6.94  ------ Global Options
% 51.50/6.94  
% 51.50/6.94  --schedule                              none
% 51.50/6.94  --add_important_lit                     false
% 51.50/6.94  --prop_solver_per_cl                    1000
% 51.50/6.94  --min_unsat_core                        false
% 51.50/6.94  --soft_assumptions                      false
% 51.50/6.94  --soft_lemma_size                       3
% 51.50/6.94  --prop_impl_unit_size                   0
% 51.50/6.94  --prop_impl_unit                        []
% 51.50/6.94  --share_sel_clauses                     true
% 51.50/6.94  --reset_solvers                         false
% 51.50/6.94  --bc_imp_inh                            [conj_cone]
% 51.50/6.94  --conj_cone_tolerance                   3.
% 51.50/6.94  --extra_neg_conj                        none
% 51.50/6.94  --large_theory_mode                     true
% 51.50/6.94  --prolific_symb_bound                   200
% 51.50/6.94  --lt_threshold                          2000
% 51.50/6.94  --clause_weak_htbl                      true
% 51.50/6.94  --gc_record_bc_elim                     false
% 51.50/6.94  
% 51.50/6.94  ------ Preprocessing Options
% 51.50/6.94  
% 51.50/6.94  --preprocessing_flag                    true
% 51.50/6.94  --time_out_prep_mult                    0.1
% 51.50/6.94  --splitting_mode                        input
% 51.50/6.94  --splitting_grd                         true
% 51.50/6.94  --splitting_cvd                         false
% 51.50/6.94  --splitting_cvd_svl                     false
% 51.50/6.94  --splitting_nvd                         32
% 51.50/6.94  --sub_typing                            true
% 51.50/6.94  --prep_gs_sim                           false
% 51.50/6.94  --prep_unflatten                        true
% 51.50/6.94  --prep_res_sim                          true
% 51.50/6.94  --prep_upred                            true
% 51.50/6.94  --prep_sem_filter                       exhaustive
% 51.50/6.94  --prep_sem_filter_out                   false
% 51.50/6.94  --pred_elim                             false
% 51.50/6.94  --res_sim_input                         true
% 51.50/6.94  --eq_ax_congr_red                       true
% 51.50/6.94  --pure_diseq_elim                       true
% 51.50/6.94  --brand_transform                       false
% 51.50/6.94  --non_eq_to_eq                          false
% 51.50/6.94  --prep_def_merge                        true
% 51.50/6.94  --prep_def_merge_prop_impl              false
% 51.50/6.94  --prep_def_merge_mbd                    true
% 51.50/6.94  --prep_def_merge_tr_red                 false
% 51.50/6.94  --prep_def_merge_tr_cl                  false
% 51.50/6.94  --smt_preprocessing                     true
% 51.50/6.94  --smt_ac_axioms                         fast
% 51.50/6.94  --preprocessed_out                      false
% 51.50/6.94  --preprocessed_stats                    false
% 51.50/6.94  
% 51.50/6.94  ------ Abstraction refinement Options
% 51.50/6.94  
% 51.50/6.94  --abstr_ref                             []
% 51.50/6.94  --abstr_ref_prep                        false
% 51.50/6.94  --abstr_ref_until_sat                   false
% 51.50/6.94  --abstr_ref_sig_restrict                funpre
% 51.50/6.94  --abstr_ref_af_restrict_to_split_sk     false
% 51.50/6.94  --abstr_ref_under                       []
% 51.50/6.94  
% 51.50/6.94  ------ SAT Options
% 51.50/6.94  
% 51.50/6.94  --sat_mode                              false
% 51.50/6.94  --sat_fm_restart_options                ""
% 51.50/6.94  --sat_gr_def                            false
% 51.50/6.94  --sat_epr_types                         true
% 51.50/6.94  --sat_non_cyclic_types                  false
% 51.50/6.94  --sat_finite_models                     false
% 51.50/6.94  --sat_fm_lemmas                         false
% 51.50/6.94  --sat_fm_prep                           false
% 51.50/6.94  --sat_fm_uc_incr                        true
% 51.50/6.94  --sat_out_model                         small
% 51.50/6.94  --sat_out_clauses                       false
% 51.50/6.94  
% 51.50/6.94  ------ QBF Options
% 51.50/6.94  
% 51.50/6.94  --qbf_mode                              false
% 51.50/6.94  --qbf_elim_univ                         false
% 51.50/6.94  --qbf_dom_inst                          none
% 51.50/6.94  --qbf_dom_pre_inst                      false
% 51.50/6.94  --qbf_sk_in                             false
% 51.50/6.94  --qbf_pred_elim                         true
% 51.50/6.94  --qbf_split                             512
% 51.50/6.94  
% 51.50/6.94  ------ BMC1 Options
% 51.50/6.94  
% 51.50/6.94  --bmc1_incremental                      false
% 51.50/6.94  --bmc1_axioms                           reachable_all
% 51.50/6.94  --bmc1_min_bound                        0
% 51.50/6.94  --bmc1_max_bound                        -1
% 51.50/6.94  --bmc1_max_bound_default                -1
% 51.50/6.94  --bmc1_symbol_reachability              true
% 51.50/6.94  --bmc1_property_lemmas                  false
% 51.50/6.94  --bmc1_k_induction                      false
% 51.50/6.94  --bmc1_non_equiv_states                 false
% 51.50/6.94  --bmc1_deadlock                         false
% 51.50/6.94  --bmc1_ucm                              false
% 51.50/6.94  --bmc1_add_unsat_core                   none
% 51.50/6.94  --bmc1_unsat_core_children              false
% 51.50/6.94  --bmc1_unsat_core_extrapolate_axioms    false
% 51.50/6.94  --bmc1_out_stat                         full
% 51.50/6.94  --bmc1_ground_init                      false
% 51.50/6.94  --bmc1_pre_inst_next_state              false
% 51.50/6.94  --bmc1_pre_inst_state                   false
% 51.50/6.94  --bmc1_pre_inst_reach_state             false
% 51.50/6.94  --bmc1_out_unsat_core                   false
% 51.50/6.94  --bmc1_aig_witness_out                  false
% 51.50/6.94  --bmc1_verbose                          false
% 51.50/6.94  --bmc1_dump_clauses_tptp                false
% 51.50/6.94  --bmc1_dump_unsat_core_tptp             false
% 51.50/6.94  --bmc1_dump_file                        -
% 51.50/6.94  --bmc1_ucm_expand_uc_limit              128
% 51.50/6.94  --bmc1_ucm_n_expand_iterations          6
% 51.50/6.94  --bmc1_ucm_extend_mode                  1
% 51.50/6.94  --bmc1_ucm_init_mode                    2
% 51.50/6.94  --bmc1_ucm_cone_mode                    none
% 51.50/6.94  --bmc1_ucm_reduced_relation_type        0
% 51.50/6.94  --bmc1_ucm_relax_model                  4
% 51.50/6.94  --bmc1_ucm_full_tr_after_sat            true
% 51.50/6.94  --bmc1_ucm_expand_neg_assumptions       false
% 51.50/6.94  --bmc1_ucm_layered_model                none
% 51.50/6.94  --bmc1_ucm_max_lemma_size               10
% 51.50/6.94  
% 51.50/6.94  ------ AIG Options
% 51.50/6.94  
% 51.50/6.94  --aig_mode                              false
% 51.50/6.94  
% 51.50/6.94  ------ Instantiation Options
% 51.50/6.94  
% 51.50/6.94  --instantiation_flag                    true
% 51.50/6.94  --inst_sos_flag                         false
% 51.50/6.94  --inst_sos_phase                        true
% 51.50/6.94  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 51.50/6.94  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 51.50/6.94  --inst_lit_sel_side                     num_symb
% 51.50/6.94  --inst_solver_per_active                1400
% 51.50/6.94  --inst_solver_calls_frac                1.
% 51.50/6.94  --inst_passive_queue_type               priority_queues
% 51.50/6.94  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 51.50/6.94  --inst_passive_queues_freq              [25;2]
% 51.50/6.94  --inst_dismatching                      true
% 51.50/6.94  --inst_eager_unprocessed_to_passive     true
% 51.50/6.94  --inst_prop_sim_given                   true
% 51.50/6.94  --inst_prop_sim_new                     false
% 51.50/6.94  --inst_subs_new                         false
% 51.50/6.94  --inst_eq_res_simp                      false
% 51.50/6.94  --inst_subs_given                       false
% 51.50/6.94  --inst_orphan_elimination               true
% 51.50/6.94  --inst_learning_loop_flag               true
% 51.50/6.94  --inst_learning_start                   3000
% 51.50/6.94  --inst_learning_factor                  2
% 51.50/6.94  --inst_start_prop_sim_after_learn       3
% 51.50/6.94  --inst_sel_renew                        solver
% 51.50/6.94  --inst_lit_activity_flag                true
% 51.50/6.94  --inst_restr_to_given                   false
% 51.50/6.94  --inst_activity_threshold               500
% 51.50/6.94  --inst_out_proof                        true
% 51.50/6.94  
% 51.50/6.94  ------ Resolution Options
% 51.50/6.94  
% 51.50/6.94  --resolution_flag                       true
% 51.50/6.94  --res_lit_sel                           adaptive
% 51.50/6.94  --res_lit_sel_side                      none
% 51.50/6.94  --res_ordering                          kbo
% 51.50/6.94  --res_to_prop_solver                    active
% 51.50/6.94  --res_prop_simpl_new                    false
% 51.50/6.94  --res_prop_simpl_given                  true
% 51.50/6.94  --res_passive_queue_type                priority_queues
% 51.50/6.94  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 51.50/6.94  --res_passive_queues_freq               [15;5]
% 51.50/6.94  --res_forward_subs                      full
% 51.50/6.94  --res_backward_subs                     full
% 51.50/6.94  --res_forward_subs_resolution           true
% 51.50/6.94  --res_backward_subs_resolution          true
% 51.50/6.94  --res_orphan_elimination                true
% 51.50/6.94  --res_time_limit                        2.
% 51.50/6.94  --res_out_proof                         true
% 51.50/6.94  
% 51.50/6.94  ------ Superposition Options
% 51.50/6.94  
% 51.50/6.94  --superposition_flag                    true
% 51.50/6.94  --sup_passive_queue_type                priority_queues
% 51.50/6.94  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 51.50/6.94  --sup_passive_queues_freq               [1;4]
% 51.50/6.94  --demod_completeness_check              fast
% 51.50/6.94  --demod_use_ground                      true
% 51.50/6.94  --sup_to_prop_solver                    passive
% 51.50/6.94  --sup_prop_simpl_new                    true
% 51.50/6.94  --sup_prop_simpl_given                  true
% 51.50/6.94  --sup_fun_splitting                     false
% 51.50/6.94  --sup_smt_interval                      50000
% 51.50/6.94  
% 51.50/6.94  ------ Superposition Simplification Setup
% 51.50/6.94  
% 51.50/6.94  --sup_indices_passive                   []
% 51.50/6.94  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 51.50/6.94  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 51.50/6.94  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 51.50/6.94  --sup_full_triv                         [TrivRules;PropSubs]
% 51.50/6.94  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 51.50/6.94  --sup_full_bw                           [BwDemod]
% 51.50/6.94  --sup_immed_triv                        [TrivRules]
% 51.50/6.94  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 51.50/6.94  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 51.50/6.94  --sup_immed_bw_main                     []
% 51.50/6.94  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 51.50/6.94  --sup_input_triv                        [Unflattening;TrivRules]
% 51.50/6.94  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 51.50/6.94  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 51.50/6.94  
% 51.50/6.94  ------ Combination Options
% 51.50/6.94  
% 51.50/6.94  --comb_res_mult                         3
% 51.50/6.94  --comb_sup_mult                         2
% 51.50/6.94  --comb_inst_mult                        10
% 51.50/6.94  
% 51.50/6.94  ------ Debug Options
% 51.50/6.94  
% 51.50/6.94  --dbg_backtrace                         false
% 51.50/6.94  --dbg_dump_prop_clauses                 false
% 51.50/6.94  --dbg_dump_prop_clauses_file            -
% 51.50/6.94  --dbg_out_stat                          false
% 51.50/6.94  
% 51.50/6.94  
% 51.50/6.94  
% 51.50/6.94  
% 51.50/6.94  ------ Proving...
% 51.50/6.94  
% 51.50/6.94  
% 51.50/6.94  % SZS status Theorem for theBenchmark.p
% 51.50/6.94  
% 51.50/6.94  % SZS output start CNFRefutation for theBenchmark.p
% 51.50/6.94  
% 51.50/6.94  fof(f11,conjecture,(
% 51.50/6.94    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 51.50/6.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.50/6.94  
% 51.50/6.94  fof(f12,negated_conjecture,(
% 51.50/6.94    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 51.50/6.94    inference(negated_conjecture,[],[f11])).
% 51.50/6.94  
% 51.50/6.94  fof(f20,plain,(
% 51.50/6.94    ? [X0,X1,X2] : ((~r1_tarski(X0,X1) & (r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 51.50/6.94    inference(ennf_transformation,[],[f12])).
% 51.50/6.94  
% 51.50/6.94  fof(f21,plain,(
% 51.50/6.94    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 51.50/6.94    inference(flattening,[],[f20])).
% 51.50/6.94  
% 51.50/6.94  fof(f24,plain,(
% 51.50/6.94    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_tarski(sK0,sK1) & r1_tarski(sK0,k2_relat_1(sK2)) & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 51.50/6.94    introduced(choice_axiom,[])).
% 51.50/6.94  
% 51.50/6.94  fof(f25,plain,(
% 51.50/6.94    ~r1_tarski(sK0,sK1) & r1_tarski(sK0,k2_relat_1(sK2)) & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 51.50/6.94    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f24])).
% 51.50/6.94  
% 51.50/6.94  fof(f38,plain,(
% 51.50/6.94    v1_relat_1(sK2)),
% 51.50/6.94    inference(cnf_transformation,[],[f25])).
% 51.50/6.94  
% 51.50/6.94  fof(f9,axiom,(
% 51.50/6.94    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k3_xboole_0(X0,X1)))),
% 51.50/6.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.50/6.94  
% 51.50/6.94  fof(f16,plain,(
% 51.50/6.94    ! [X0,X1,X2] : (k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k3_xboole_0(X0,X1)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 51.50/6.94    inference(ennf_transformation,[],[f9])).
% 51.50/6.94  
% 51.50/6.94  fof(f17,plain,(
% 51.50/6.94    ! [X0,X1,X2] : (k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 51.50/6.94    inference(flattening,[],[f16])).
% 51.50/6.94  
% 51.50/6.94  fof(f36,plain,(
% 51.50/6.94    ( ! [X2,X0,X1] : (k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 51.50/6.94    inference(cnf_transformation,[],[f17])).
% 51.50/6.94  
% 51.50/6.94  fof(f8,axiom,(
% 51.50/6.94    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 51.50/6.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.50/6.94  
% 51.50/6.94  fof(f35,plain,(
% 51.50/6.94    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 51.50/6.94    inference(cnf_transformation,[],[f8])).
% 51.50/6.94  
% 51.50/6.94  fof(f7,axiom,(
% 51.50/6.94    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 51.50/6.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.50/6.94  
% 51.50/6.94  fof(f34,plain,(
% 51.50/6.94    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 51.50/6.94    inference(cnf_transformation,[],[f7])).
% 51.50/6.94  
% 51.50/6.94  fof(f43,plain,(
% 51.50/6.94    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 51.50/6.94    inference(definition_unfolding,[],[f35,f34])).
% 51.50/6.94  
% 51.50/6.94  fof(f47,plain,(
% 51.50/6.94    ( ! [X2,X0,X1] : (k1_setfam_1(k1_enumset1(k10_relat_1(X2,X0),k10_relat_1(X2,X0),k10_relat_1(X2,X1))) = k10_relat_1(X2,k1_setfam_1(k1_enumset1(X0,X0,X1))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 51.50/6.94    inference(definition_unfolding,[],[f36,f43,f43])).
% 51.50/6.94  
% 51.50/6.94  fof(f39,plain,(
% 51.50/6.94    v1_funct_1(sK2)),
% 51.50/6.94    inference(cnf_transformation,[],[f25])).
% 51.50/6.94  
% 51.50/6.94  fof(f40,plain,(
% 51.50/6.94    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),
% 51.50/6.94    inference(cnf_transformation,[],[f25])).
% 51.50/6.94  
% 51.50/6.94  fof(f5,axiom,(
% 51.50/6.94    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 51.50/6.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.50/6.94  
% 51.50/6.94  fof(f15,plain,(
% 51.50/6.94    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 51.50/6.94    inference(ennf_transformation,[],[f5])).
% 51.50/6.94  
% 51.50/6.94  fof(f32,plain,(
% 51.50/6.94    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 51.50/6.94    inference(cnf_transformation,[],[f15])).
% 51.50/6.94  
% 51.50/6.94  fof(f45,plain,(
% 51.50/6.94    ( ! [X0,X1] : (k1_setfam_1(k1_enumset1(X0,X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 51.50/6.94    inference(definition_unfolding,[],[f32,f43])).
% 51.50/6.94  
% 51.50/6.94  fof(f6,axiom,(
% 51.50/6.94    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 51.50/6.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.50/6.94  
% 51.50/6.94  fof(f33,plain,(
% 51.50/6.94    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 51.50/6.94    inference(cnf_transformation,[],[f6])).
% 51.50/6.94  
% 51.50/6.94  fof(f46,plain,(
% 51.50/6.94    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 51.50/6.94    inference(definition_unfolding,[],[f33,f34,f34])).
% 51.50/6.94  
% 51.50/6.94  fof(f41,plain,(
% 51.50/6.94    r1_tarski(sK0,k2_relat_1(sK2))),
% 51.50/6.94    inference(cnf_transformation,[],[f25])).
% 51.50/6.94  
% 51.50/6.94  fof(f4,axiom,(
% 51.50/6.94    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 51.50/6.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.50/6.94  
% 51.50/6.94  fof(f31,plain,(
% 51.50/6.94    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 51.50/6.94    inference(cnf_transformation,[],[f4])).
% 51.50/6.94  
% 51.50/6.94  fof(f44,plain,(
% 51.50/6.94    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X0)) )),
% 51.50/6.94    inference(definition_unfolding,[],[f31,f43])).
% 51.50/6.94  
% 51.50/6.94  fof(f3,axiom,(
% 51.50/6.94    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 51.50/6.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.50/6.94  
% 51.50/6.94  fof(f14,plain,(
% 51.50/6.94    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 51.50/6.94    inference(ennf_transformation,[],[f3])).
% 51.50/6.94  
% 51.50/6.94  fof(f30,plain,(
% 51.50/6.94    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 51.50/6.94    inference(cnf_transformation,[],[f14])).
% 51.50/6.94  
% 51.50/6.94  fof(f2,axiom,(
% 51.50/6.94    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 51.50/6.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.50/6.94  
% 51.50/6.94  fof(f13,plain,(
% 51.50/6.94    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 51.50/6.94    inference(ennf_transformation,[],[f2])).
% 51.50/6.94  
% 51.50/6.94  fof(f29,plain,(
% 51.50/6.94    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 51.50/6.94    inference(cnf_transformation,[],[f13])).
% 51.50/6.94  
% 51.50/6.94  fof(f1,axiom,(
% 51.50/6.94    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 51.50/6.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.50/6.94  
% 51.50/6.94  fof(f22,plain,(
% 51.50/6.94    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 51.50/6.94    inference(nnf_transformation,[],[f1])).
% 51.50/6.94  
% 51.50/6.94  fof(f23,plain,(
% 51.50/6.94    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 51.50/6.94    inference(flattening,[],[f22])).
% 51.50/6.94  
% 51.50/6.94  fof(f26,plain,(
% 51.50/6.94    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 51.50/6.94    inference(cnf_transformation,[],[f23])).
% 51.50/6.94  
% 51.50/6.94  fof(f49,plain,(
% 51.50/6.94    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 51.50/6.94    inference(equality_resolution,[],[f26])).
% 51.50/6.94  
% 51.50/6.94  fof(f28,plain,(
% 51.50/6.94    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 51.50/6.94    inference(cnf_transformation,[],[f23])).
% 51.50/6.94  
% 51.50/6.94  fof(f10,axiom,(
% 51.50/6.94    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 51.50/6.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.50/6.94  
% 51.50/6.94  fof(f18,plain,(
% 51.50/6.94    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 51.50/6.94    inference(ennf_transformation,[],[f10])).
% 51.50/6.94  
% 51.50/6.94  fof(f19,plain,(
% 51.50/6.94    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 51.50/6.94    inference(flattening,[],[f18])).
% 51.50/6.94  
% 51.50/6.94  fof(f37,plain,(
% 51.50/6.94    ( ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 51.50/6.94    inference(cnf_transformation,[],[f19])).
% 51.50/6.94  
% 51.50/6.94  fof(f42,plain,(
% 51.50/6.94    ~r1_tarski(sK0,sK1)),
% 51.50/6.94    inference(cnf_transformation,[],[f25])).
% 51.50/6.94  
% 51.50/6.94  cnf(c_14,negated_conjecture,
% 51.50/6.94      ( v1_relat_1(sK2) ),
% 51.50/6.94      inference(cnf_transformation,[],[f38]) ).
% 51.50/6.94  
% 51.50/6.94  cnf(c_424,plain,
% 51.50/6.94      ( v1_relat_1(sK2) = iProver_top ),
% 51.50/6.94      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 51.50/6.94  
% 51.50/6.94  cnf(c_8,plain,
% 51.50/6.94      ( ~ v1_relat_1(X0)
% 51.50/6.94      | ~ v1_funct_1(X0)
% 51.50/6.94      | k1_setfam_1(k1_enumset1(k10_relat_1(X0,X1),k10_relat_1(X0,X1),k10_relat_1(X0,X2))) = k10_relat_1(X0,k1_setfam_1(k1_enumset1(X1,X1,X2))) ),
% 51.50/6.94      inference(cnf_transformation,[],[f47]) ).
% 51.50/6.94  
% 51.50/6.94  cnf(c_430,plain,
% 51.50/6.94      ( k1_setfam_1(k1_enumset1(k10_relat_1(X0,X1),k10_relat_1(X0,X1),k10_relat_1(X0,X2))) = k10_relat_1(X0,k1_setfam_1(k1_enumset1(X1,X1,X2)))
% 51.50/6.94      | v1_relat_1(X0) != iProver_top
% 51.50/6.94      | v1_funct_1(X0) != iProver_top ),
% 51.50/6.94      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 51.50/6.94  
% 51.50/6.94  cnf(c_1428,plain,
% 51.50/6.94      ( k1_setfam_1(k1_enumset1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X0),k10_relat_1(sK2,X1))) = k10_relat_1(sK2,k1_setfam_1(k1_enumset1(X0,X0,X1)))
% 51.50/6.94      | v1_funct_1(sK2) != iProver_top ),
% 51.50/6.94      inference(superposition,[status(thm)],[c_424,c_430]) ).
% 51.50/6.94  
% 51.50/6.94  cnf(c_13,negated_conjecture,
% 51.50/6.94      ( v1_funct_1(sK2) ),
% 51.50/6.94      inference(cnf_transformation,[],[f39]) ).
% 51.50/6.94  
% 51.50/6.94  cnf(c_16,plain,
% 51.50/6.94      ( v1_funct_1(sK2) = iProver_top ),
% 51.50/6.94      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 51.50/6.94  
% 51.50/6.94  cnf(c_6982,plain,
% 51.50/6.94      ( k1_setfam_1(k1_enumset1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X0),k10_relat_1(sK2,X1))) = k10_relat_1(sK2,k1_setfam_1(k1_enumset1(X0,X0,X1))) ),
% 51.50/6.94      inference(global_propositional_subsumption,
% 51.50/6.94                [status(thm)],
% 51.50/6.94                [c_1428,c_16]) ).
% 51.50/6.94  
% 51.50/6.94  cnf(c_12,negated_conjecture,
% 51.50/6.94      ( r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
% 51.50/6.94      inference(cnf_transformation,[],[f40]) ).
% 51.50/6.94  
% 51.50/6.94  cnf(c_426,plain,
% 51.50/6.94      ( r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) = iProver_top ),
% 51.50/6.94      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 51.50/6.94  
% 51.50/6.94  cnf(c_6,plain,
% 51.50/6.94      ( ~ r1_tarski(X0,X1) | k1_setfam_1(k1_enumset1(X0,X0,X1)) = X0 ),
% 51.50/6.94      inference(cnf_transformation,[],[f45]) ).
% 51.50/6.94  
% 51.50/6.94  cnf(c_431,plain,
% 51.50/6.94      ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = X0
% 51.50/6.94      | r1_tarski(X0,X1) != iProver_top ),
% 51.50/6.94      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 51.50/6.94  
% 51.50/6.94  cnf(c_1072,plain,
% 51.50/6.94      ( k1_setfam_1(k1_enumset1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))) = k10_relat_1(sK2,sK0) ),
% 51.50/6.94      inference(superposition,[status(thm)],[c_426,c_431]) ).
% 51.50/6.94  
% 51.50/6.94  cnf(c_6998,plain,
% 51.50/6.94      ( k10_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,sK1))) = k10_relat_1(sK2,sK0) ),
% 51.50/6.94      inference(superposition,[status(thm)],[c_6982,c_1072]) ).
% 51.50/6.94  
% 51.50/6.94  cnf(c_7,plain,
% 51.50/6.94      ( k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
% 51.50/6.94      inference(cnf_transformation,[],[f46]) ).
% 51.50/6.94  
% 51.50/6.94  cnf(c_11,negated_conjecture,
% 51.50/6.94      ( r1_tarski(sK0,k2_relat_1(sK2)) ),
% 51.50/6.94      inference(cnf_transformation,[],[f41]) ).
% 51.50/6.94  
% 51.50/6.94  cnf(c_427,plain,
% 51.50/6.94      ( r1_tarski(sK0,k2_relat_1(sK2)) = iProver_top ),
% 51.50/6.94      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 51.50/6.94  
% 51.50/6.94  cnf(c_5,plain,
% 51.50/6.94      ( r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X0) ),
% 51.50/6.94      inference(cnf_transformation,[],[f44]) ).
% 51.50/6.94  
% 51.50/6.94  cnf(c_432,plain,
% 51.50/6.94      ( r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X0) = iProver_top ),
% 51.50/6.94      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 51.50/6.94  
% 51.50/6.94  cnf(c_4,plain,
% 51.50/6.94      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 51.50/6.94      inference(cnf_transformation,[],[f30]) ).
% 51.50/6.94  
% 51.50/6.94  cnf(c_433,plain,
% 51.50/6.94      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 51.50/6.94      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 51.50/6.94  
% 51.50/6.94  cnf(c_861,plain,
% 51.50/6.94      ( k2_xboole_0(k1_setfam_1(k1_enumset1(X0,X0,X1)),X0) = X0 ),
% 51.50/6.94      inference(superposition,[status(thm)],[c_432,c_433]) ).
% 51.50/6.94  
% 51.50/6.94  cnf(c_3,plain,
% 51.50/6.94      ( r1_tarski(X0,X1) | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
% 51.50/6.94      inference(cnf_transformation,[],[f29]) ).
% 51.50/6.94  
% 51.50/6.94  cnf(c_434,plain,
% 51.50/6.94      ( r1_tarski(X0,X1) = iProver_top
% 51.50/6.94      | r1_tarski(k2_xboole_0(X0,X2),X1) != iProver_top ),
% 51.50/6.94      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 51.50/6.94  
% 51.50/6.94  cnf(c_1965,plain,
% 51.50/6.94      ( r1_tarski(X0,X1) != iProver_top
% 51.50/6.94      | r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X2)),X1) = iProver_top ),
% 51.50/6.94      inference(superposition,[status(thm)],[c_861,c_434]) ).
% 51.50/6.94  
% 51.50/6.94  cnf(c_4593,plain,
% 51.50/6.94      ( k2_xboole_0(k1_setfam_1(k1_enumset1(X0,X0,X1)),X2) = X2
% 51.50/6.94      | r1_tarski(X0,X2) != iProver_top ),
% 51.50/6.94      inference(superposition,[status(thm)],[c_1965,c_433]) ).
% 51.50/6.94  
% 51.50/6.94  cnf(c_5101,plain,
% 51.50/6.94      ( k2_xboole_0(k1_setfam_1(k1_enumset1(sK0,sK0,X0)),k2_relat_1(sK2)) = k2_relat_1(sK2) ),
% 51.50/6.94      inference(superposition,[status(thm)],[c_427,c_4593]) ).
% 51.50/6.94  
% 51.50/6.94  cnf(c_5307,plain,
% 51.50/6.94      ( k2_xboole_0(k1_setfam_1(k1_enumset1(X0,X0,sK0)),k2_relat_1(sK2)) = k2_relat_1(sK2) ),
% 51.50/6.94      inference(superposition,[status(thm)],[c_7,c_5101]) ).
% 51.50/6.94  
% 51.50/6.94  cnf(c_2,plain,
% 51.50/6.94      ( r1_tarski(X0,X0) ),
% 51.50/6.94      inference(cnf_transformation,[],[f49]) ).
% 51.50/6.94  
% 51.50/6.94  cnf(c_435,plain,
% 51.50/6.94      ( r1_tarski(X0,X0) = iProver_top ),
% 51.50/6.94      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 51.50/6.94  
% 51.50/6.94  cnf(c_1246,plain,
% 51.50/6.94      ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
% 51.50/6.94      inference(superposition,[status(thm)],[c_435,c_434]) ).
% 51.50/6.94  
% 51.50/6.94  cnf(c_1703,plain,
% 51.50/6.94      ( k1_setfam_1(k1_enumset1(X0,X0,k2_xboole_0(X0,X1))) = X0 ),
% 51.50/6.94      inference(superposition,[status(thm)],[c_1246,c_431]) ).
% 51.50/6.94  
% 51.50/6.94  cnf(c_710,plain,
% 51.50/6.94      ( r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X1) = iProver_top ),
% 51.50/6.94      inference(superposition,[status(thm)],[c_7,c_432]) ).
% 51.50/6.94  
% 51.50/6.94  cnf(c_0,plain,
% 51.50/6.94      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 51.50/6.94      inference(cnf_transformation,[],[f28]) ).
% 51.50/6.94  
% 51.50/6.94  cnf(c_436,plain,
% 51.50/6.94      ( X0 = X1
% 51.50/6.94      | r1_tarski(X0,X1) != iProver_top
% 51.50/6.94      | r1_tarski(X1,X0) != iProver_top ),
% 51.50/6.94      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 51.50/6.94  
% 51.50/6.94  cnf(c_1256,plain,
% 51.50/6.94      ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = X1
% 51.50/6.94      | r1_tarski(X1,k1_setfam_1(k1_enumset1(X0,X0,X1))) != iProver_top ),
% 51.50/6.94      inference(superposition,[status(thm)],[c_710,c_436]) ).
% 51.50/6.94  
% 51.50/6.94  cnf(c_6314,plain,
% 51.50/6.94      ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = X1
% 51.50/6.94      | r1_tarski(X1,k1_setfam_1(k1_enumset1(X1,X1,X0))) != iProver_top ),
% 51.50/6.94      inference(superposition,[status(thm)],[c_7,c_1256]) ).
% 51.50/6.94  
% 51.50/6.94  cnf(c_6356,plain,
% 51.50/6.94      ( k1_setfam_1(k1_enumset1(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1),X0)) = X0
% 51.50/6.94      | r1_tarski(X0,X0) != iProver_top ),
% 51.50/6.94      inference(superposition,[status(thm)],[c_1703,c_6314]) ).
% 51.50/6.94  
% 51.50/6.94  cnf(c_39,plain,
% 51.50/6.94      ( r1_tarski(X0,X0) = iProver_top ),
% 51.50/6.94      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 51.50/6.94  
% 51.50/6.94  cnf(c_13067,plain,
% 51.50/6.94      ( k1_setfam_1(k1_enumset1(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1),X0)) = X0 ),
% 51.50/6.94      inference(global_propositional_subsumption,
% 51.50/6.94                [status(thm)],
% 51.50/6.94                [c_6356,c_39]) ).
% 51.50/6.94  
% 51.50/6.94  cnf(c_13103,plain,
% 51.50/6.94      ( k1_setfam_1(k1_enumset1(k2_relat_1(sK2),k2_relat_1(sK2),k1_setfam_1(k1_enumset1(X0,X0,sK0)))) = k1_setfam_1(k1_enumset1(X0,X0,sK0)) ),
% 51.50/6.94      inference(superposition,[status(thm)],[c_5307,c_13067]) ).
% 51.50/6.94  
% 51.50/6.94  cnf(c_13377,plain,
% 51.50/6.94      ( k1_setfam_1(k1_enumset1(k2_relat_1(sK2),k2_relat_1(sK2),k1_setfam_1(k1_enumset1(sK0,sK0,X0)))) = k1_setfam_1(k1_enumset1(X0,X0,sK0)) ),
% 51.50/6.94      inference(superposition,[status(thm)],[c_7,c_13103]) ).
% 51.50/6.94  
% 51.50/6.94  cnf(c_9,plain,
% 51.50/6.94      ( ~ r1_tarski(X0,k2_relat_1(X1))
% 51.50/6.94      | ~ v1_relat_1(X1)
% 51.50/6.94      | ~ v1_funct_1(X1)
% 51.50/6.94      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ),
% 51.50/6.94      inference(cnf_transformation,[],[f37]) ).
% 51.50/6.94  
% 51.50/6.94  cnf(c_429,plain,
% 51.50/6.94      ( k9_relat_1(X0,k10_relat_1(X0,X1)) = X1
% 51.50/6.94      | r1_tarski(X1,k2_relat_1(X0)) != iProver_top
% 51.50/6.94      | v1_relat_1(X0) != iProver_top
% 51.50/6.94      | v1_funct_1(X0) != iProver_top ),
% 51.50/6.94      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 51.50/6.94  
% 51.50/6.94  cnf(c_1029,plain,
% 51.50/6.94      ( k9_relat_1(X0,k10_relat_1(X0,k1_setfam_1(k1_enumset1(k2_relat_1(X0),k2_relat_1(X0),X1)))) = k1_setfam_1(k1_enumset1(k2_relat_1(X0),k2_relat_1(X0),X1))
% 51.50/6.94      | v1_relat_1(X0) != iProver_top
% 51.50/6.94      | v1_funct_1(X0) != iProver_top ),
% 51.50/6.94      inference(superposition,[status(thm)],[c_432,c_429]) ).
% 51.50/6.94  
% 51.50/6.94  cnf(c_3041,plain,
% 51.50/6.94      ( k9_relat_1(sK2,k10_relat_1(sK2,k1_setfam_1(k1_enumset1(k2_relat_1(sK2),k2_relat_1(sK2),X0)))) = k1_setfam_1(k1_enumset1(k2_relat_1(sK2),k2_relat_1(sK2),X0))
% 51.50/6.94      | v1_funct_1(sK2) != iProver_top ),
% 51.50/6.94      inference(superposition,[status(thm)],[c_424,c_1029]) ).
% 51.50/6.94  
% 51.50/6.94  cnf(c_22196,plain,
% 51.50/6.94      ( k9_relat_1(sK2,k10_relat_1(sK2,k1_setfam_1(k1_enumset1(k2_relat_1(sK2),k2_relat_1(sK2),X0)))) = k1_setfam_1(k1_enumset1(k2_relat_1(sK2),k2_relat_1(sK2),X0)) ),
% 51.50/6.94      inference(global_propositional_subsumption,
% 51.50/6.94                [status(thm)],
% 51.50/6.94                [c_3041,c_16]) ).
% 51.50/6.94  
% 51.50/6.94  cnf(c_22209,plain,
% 51.50/6.94      ( k1_setfam_1(k1_enumset1(k2_relat_1(sK2),k2_relat_1(sK2),k1_setfam_1(k1_enumset1(sK0,sK0,X0)))) = k9_relat_1(sK2,k10_relat_1(sK2,k1_setfam_1(k1_enumset1(X0,X0,sK0)))) ),
% 51.50/6.94      inference(superposition,[status(thm)],[c_13377,c_22196]) ).
% 51.50/6.94  
% 51.50/6.94  cnf(c_99209,plain,
% 51.50/6.94      ( k1_setfam_1(k1_enumset1(k2_relat_1(sK2),k2_relat_1(sK2),k1_setfam_1(k1_enumset1(sK0,sK0,X0)))) = k9_relat_1(sK2,k10_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,X0)))) ),
% 51.50/6.94      inference(superposition,[status(thm)],[c_7,c_22209]) ).
% 51.50/6.94  
% 51.50/6.94  cnf(c_13490,plain,
% 51.50/6.94      ( r1_tarski(k1_setfam_1(k1_enumset1(k2_relat_1(sK2),k2_relat_1(sK2),k1_setfam_1(k1_enumset1(sK0,sK0,X0)))),X0) = iProver_top ),
% 51.50/6.94      inference(superposition,[status(thm)],[c_13377,c_432]) ).
% 51.50/6.94  
% 51.50/6.94  cnf(c_101292,plain,
% 51.50/6.94      ( r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,X0)))),X0) = iProver_top ),
% 51.50/6.94      inference(demodulation,[status(thm)],[c_99209,c_13490]) ).
% 51.50/6.94  
% 51.50/6.94  cnf(c_201999,plain,
% 51.50/6.94      ( r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,sK0)),sK1) = iProver_top ),
% 51.50/6.94      inference(superposition,[status(thm)],[c_6998,c_101292]) ).
% 51.50/6.94  
% 51.50/6.94  cnf(c_1030,plain,
% 51.50/6.94      ( k9_relat_1(sK2,k10_relat_1(sK2,sK0)) = sK0
% 51.50/6.94      | v1_relat_1(sK2) != iProver_top
% 51.50/6.94      | v1_funct_1(sK2) != iProver_top ),
% 51.50/6.94      inference(superposition,[status(thm)],[c_427,c_429]) ).
% 51.50/6.94  
% 51.50/6.94  cnf(c_571,plain,
% 51.50/6.94      ( ~ r1_tarski(sK0,k2_relat_1(sK2))
% 51.50/6.94      | ~ v1_relat_1(sK2)
% 51.50/6.94      | ~ v1_funct_1(sK2)
% 51.50/6.94      | k9_relat_1(sK2,k10_relat_1(sK2,sK0)) = sK0 ),
% 51.50/6.94      inference(instantiation,[status(thm)],[c_9]) ).
% 51.50/6.94  
% 51.50/6.94  cnf(c_3480,plain,
% 51.50/6.94      ( k9_relat_1(sK2,k10_relat_1(sK2,sK0)) = sK0 ),
% 51.50/6.94      inference(global_propositional_subsumption,
% 51.50/6.94                [status(thm)],
% 51.50/6.94                [c_1030,c_14,c_13,c_11,c_571]) ).
% 51.50/6.94  
% 51.50/6.94  cnf(c_202649,plain,
% 51.50/6.94      ( r1_tarski(sK0,sK1) = iProver_top ),
% 51.50/6.94      inference(light_normalisation,[status(thm)],[c_201999,c_3480]) ).
% 51.50/6.94  
% 51.50/6.94  cnf(c_10,negated_conjecture,
% 51.50/6.94      ( ~ r1_tarski(sK0,sK1) ),
% 51.50/6.94      inference(cnf_transformation,[],[f42]) ).
% 51.50/6.94  
% 51.50/6.94  cnf(c_19,plain,
% 51.50/6.94      ( r1_tarski(sK0,sK1) != iProver_top ),
% 51.50/6.94      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 51.50/6.94  
% 51.50/6.94  cnf(contradiction,plain,
% 51.50/6.94      ( $false ),
% 51.50/6.94      inference(minisat,[status(thm)],[c_202649,c_19]) ).
% 51.50/6.94  
% 51.50/6.94  
% 51.50/6.94  % SZS output end CNFRefutation for theBenchmark.p
% 51.50/6.94  
% 51.50/6.94  ------                               Statistics
% 51.50/6.94  
% 51.50/6.94  ------ Selected
% 51.50/6.94  
% 51.50/6.94  total_time:                             6.295
% 51.50/6.94  
%------------------------------------------------------------------------------
