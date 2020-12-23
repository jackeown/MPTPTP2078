%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:52:18 EST 2020

% Result     : Theorem 11.92s
% Output     : CNFRefutation 11.92s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 259 expanded)
%              Number of clauses        :   53 (  74 expanded)
%              Number of leaves         :   13 (  56 expanded)
%              Depth                    :   18
%              Number of atoms          :  219 ( 774 expanded)
%              Number of equality atoms :  100 ( 169 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(X0,k2_relat_1(X2))
          & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( r1_tarski(X0,k2_relat_1(X2))
            & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) )
         => r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_tarski(X0,k2_relat_1(X2))
      & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_tarski(X0,k2_relat_1(X2))
      & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f26,plain,
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

fof(f27,plain,
    ( ~ r1_tarski(sK0,sK1)
    & r1_tarski(sK0,k2_relat_1(sK2))
    & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f26])).

fof(f42,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f8,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f47,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f39,f38])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k1_setfam_1(k1_enumset1(k10_relat_1(X2,X0),k10_relat_1(X2,X0),k10_relat_1(X2,X1))) = k10_relat_1(X2,k1_setfam_1(k1_enumset1(X0,X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f40,f47,f47])).

fof(f43,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f44,plain,(
    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f27])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f37,f47])).

fof(f45,plain,(
    r1_tarski(sK0,k2_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f27])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f51,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f36,f47])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f23])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f55,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f28])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f48,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1))) ),
    inference(definition_unfolding,[],[f33,f47])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1))) ) ),
    inference(definition_unfolding,[],[f31,f48])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f32,f48])).

fof(f46,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_15,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_640,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_setfam_1(k1_enumset1(k10_relat_1(X0,X1),k10_relat_1(X0,X1),k10_relat_1(X0,X2))) = k10_relat_1(X0,k1_setfam_1(k1_enumset1(X1,X1,X2))) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_646,plain,
    ( k1_setfam_1(k1_enumset1(k10_relat_1(X0,X1),k10_relat_1(X0,X1),k10_relat_1(X0,X2))) = k10_relat_1(X0,k1_setfam_1(k1_enumset1(X1,X1,X2)))
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2124,plain,
    ( k1_setfam_1(k1_enumset1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X0),k10_relat_1(sK2,X1))) = k10_relat_1(sK2,k1_setfam_1(k1_enumset1(X0,X0,X1)))
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_640,c_646])).

cnf(c_14,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_17,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2871,plain,
    ( k1_setfam_1(k1_enumset1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X0),k10_relat_1(sK2,X1))) = k10_relat_1(sK2,k1_setfam_1(k1_enumset1(X0,X0,X1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2124,c_17])).

cnf(c_13,negated_conjecture,
    ( r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_642,plain,
    ( r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | k1_setfam_1(k1_enumset1(X0,X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_647,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1159,plain,
    ( k1_setfam_1(k1_enumset1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))) = k10_relat_1(sK2,sK0) ),
    inference(superposition,[status(thm)],[c_642,c_647])).

cnf(c_2880,plain,
    ( k10_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,sK1))) = k10_relat_1(sK2,sK0) ),
    inference(superposition,[status(thm)],[c_2871,c_1159])).

cnf(c_12,negated_conjecture,
    ( r1_tarski(sK0,k2_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_643,plain,
    ( r1_tarski(sK0,k2_relat_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_7,plain,
    ( r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_648,plain,
    ( r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_649,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_972,plain,
    ( k2_xboole_0(k1_setfam_1(k1_enumset1(X0,X0,X1)),X0) = X0 ),
    inference(superposition,[status(thm)],[c_648,c_649])).

cnf(c_5,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_650,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(k2_xboole_0(X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3581,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X2)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_972,c_650])).

cnf(c_9206,plain,
    ( k2_xboole_0(k1_setfam_1(k1_enumset1(X0,X0,X1)),X2) = X2
    | r1_tarski(X0,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3581,c_649])).

cnf(c_11121,plain,
    ( k2_xboole_0(k1_setfam_1(k1_enumset1(sK0,sK0,X0)),k2_relat_1(sK2)) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_643,c_9206])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_653,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1333,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_653,c_650])).

cnf(c_11918,plain,
    ( r1_tarski(k1_setfam_1(k1_enumset1(sK0,sK0,X0)),k2_relat_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_11121,c_1333])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_645,plain,
    ( k9_relat_1(X0,k10_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k2_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_12462,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,X0)))) = k1_setfam_1(k1_enumset1(sK0,sK0,X0))
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_11918,c_645])).

cnf(c_16,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_45253,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,X0)))) = k1_setfam_1(k1_enumset1(sK0,sK0,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12462,c_16,c_17])).

cnf(c_45257,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,sK0)) = k1_setfam_1(k1_enumset1(sK0,sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_2880,c_45253])).

cnf(c_1127,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,sK0)) = sK0
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_643,c_645])).

cnf(c_813,plain,
    ( ~ r1_tarski(sK0,k2_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k9_relat_1(sK2,k10_relat_1(sK2,sK0)) = sK0 ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1969,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,sK0)) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1127,c_15,c_14,c_12,c_813])).

cnf(c_45316,plain,
    ( k1_setfam_1(k1_enumset1(sK0,sK0,sK1)) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_45257,c_1969])).

cnf(c_4,plain,
    ( r1_tarski(X0,X1)
    | k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1))) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_651,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1))) != k1_xboole_0
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_46383,plain,
    ( k5_xboole_0(sK0,sK0) != k1_xboole_0
    | r1_tarski(sK0,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_45316,c_651])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1))) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_652,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1))) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1507,plain,
    ( k5_xboole_0(sK0,k1_setfam_1(k1_enumset1(sK0,sK0,k2_relat_1(sK2)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_643,c_652])).

cnf(c_1158,plain,
    ( k1_setfam_1(k1_enumset1(sK0,sK0,k2_relat_1(sK2))) = sK0 ),
    inference(superposition,[status(thm)],[c_643,c_647])).

cnf(c_1674,plain,
    ( k5_xboole_0(sK0,sK0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1507,c_1158])).

cnf(c_46482,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK0,sK1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_46383,c_1674])).

cnf(c_46483,plain,
    ( r1_tarski(sK0,sK1) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_46482])).

cnf(c_11,negated_conjecture,
    ( ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_20,plain,
    ( r1_tarski(sK0,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_46483,c_20])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:51:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 11.92/1.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.92/1.98  
% 11.92/1.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.92/1.98  
% 11.92/1.98  ------  iProver source info
% 11.92/1.98  
% 11.92/1.98  git: date: 2020-06-30 10:37:57 +0100
% 11.92/1.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.92/1.98  git: non_committed_changes: false
% 11.92/1.98  git: last_make_outside_of_git: false
% 11.92/1.98  
% 11.92/1.98  ------ 
% 11.92/1.98  ------ Parsing...
% 11.92/1.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.92/1.98  
% 11.92/1.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 11.92/1.98  
% 11.92/1.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.92/1.98  
% 11.92/1.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.92/1.98  ------ Proving...
% 11.92/1.98  ------ Problem Properties 
% 11.92/1.98  
% 11.92/1.98  
% 11.92/1.98  clauses                                 15
% 11.92/1.98  conjectures                             5
% 11.92/1.98  EPR                                     5
% 11.92/1.98  Horn                                    15
% 11.92/1.98  unary                                   7
% 11.92/1.98  binary                                  5
% 11.92/1.98  lits                                    27
% 11.92/1.98  lits eq                                 7
% 11.92/1.98  fd_pure                                 0
% 11.92/1.98  fd_pseudo                               0
% 11.92/1.98  fd_cond                                 0
% 11.92/1.98  fd_pseudo_cond                          1
% 11.92/1.98  AC symbols                              0
% 11.92/1.98  
% 11.92/1.98  ------ Input Options Time Limit: Unbounded
% 11.92/1.98  
% 11.92/1.98  
% 11.92/1.98  ------ 
% 11.92/1.98  Current options:
% 11.92/1.98  ------ 
% 11.92/1.98  
% 11.92/1.98  
% 11.92/1.98  
% 11.92/1.98  
% 11.92/1.98  ------ Proving...
% 11.92/1.98  
% 11.92/1.98  
% 11.92/1.98  % SZS status Theorem for theBenchmark.p
% 11.92/1.98  
% 11.92/1.98  % SZS output start CNFRefutation for theBenchmark.p
% 11.92/1.98  
% 11.92/1.98  fof(f12,conjecture,(
% 11.92/1.98    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 11.92/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.92/1.98  
% 11.92/1.98  fof(f13,negated_conjecture,(
% 11.92/1.98    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 11.92/1.98    inference(negated_conjecture,[],[f12])).
% 11.92/1.98  
% 11.92/1.98  fof(f21,plain,(
% 11.92/1.98    ? [X0,X1,X2] : ((~r1_tarski(X0,X1) & (r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 11.92/1.98    inference(ennf_transformation,[],[f13])).
% 11.92/1.98  
% 11.92/1.98  fof(f22,plain,(
% 11.92/1.98    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 11.92/1.98    inference(flattening,[],[f21])).
% 11.92/1.98  
% 11.92/1.98  fof(f26,plain,(
% 11.92/1.98    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_tarski(sK0,sK1) & r1_tarski(sK0,k2_relat_1(sK2)) & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 11.92/1.98    introduced(choice_axiom,[])).
% 11.92/1.98  
% 11.92/1.98  fof(f27,plain,(
% 11.92/1.98    ~r1_tarski(sK0,sK1) & r1_tarski(sK0,k2_relat_1(sK2)) & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 11.92/1.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f26])).
% 11.92/1.98  
% 11.92/1.98  fof(f42,plain,(
% 11.92/1.98    v1_relat_1(sK2)),
% 11.92/1.98    inference(cnf_transformation,[],[f27])).
% 11.92/1.98  
% 11.92/1.98  fof(f10,axiom,(
% 11.92/1.98    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k3_xboole_0(X0,X1)))),
% 11.92/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.92/1.98  
% 11.92/1.98  fof(f17,plain,(
% 11.92/1.98    ! [X0,X1,X2] : (k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k3_xboole_0(X0,X1)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 11.92/1.98    inference(ennf_transformation,[],[f10])).
% 11.92/1.98  
% 11.92/1.98  fof(f18,plain,(
% 11.92/1.98    ! [X0,X1,X2] : (k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 11.92/1.98    inference(flattening,[],[f17])).
% 11.92/1.98  
% 11.92/1.98  fof(f40,plain,(
% 11.92/1.98    ( ! [X2,X0,X1] : (k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 11.92/1.98    inference(cnf_transformation,[],[f18])).
% 11.92/1.98  
% 11.92/1.98  fof(f9,axiom,(
% 11.92/1.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 11.92/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.92/1.98  
% 11.92/1.98  fof(f39,plain,(
% 11.92/1.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 11.92/1.98    inference(cnf_transformation,[],[f9])).
% 11.92/1.98  
% 11.92/1.98  fof(f8,axiom,(
% 11.92/1.98    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 11.92/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.92/1.98  
% 11.92/1.98  fof(f38,plain,(
% 11.92/1.98    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 11.92/1.98    inference(cnf_transformation,[],[f8])).
% 11.92/1.98  
% 11.92/1.98  fof(f47,plain,(
% 11.92/1.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 11.92/1.98    inference(definition_unfolding,[],[f39,f38])).
% 11.92/1.98  
% 11.92/1.98  fof(f53,plain,(
% 11.92/1.98    ( ! [X2,X0,X1] : (k1_setfam_1(k1_enumset1(k10_relat_1(X2,X0),k10_relat_1(X2,X0),k10_relat_1(X2,X1))) = k10_relat_1(X2,k1_setfam_1(k1_enumset1(X0,X0,X1))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 11.92/1.98    inference(definition_unfolding,[],[f40,f47,f47])).
% 11.92/1.98  
% 11.92/1.98  fof(f43,plain,(
% 11.92/1.98    v1_funct_1(sK2)),
% 11.92/1.98    inference(cnf_transformation,[],[f27])).
% 11.92/1.98  
% 11.92/1.98  fof(f44,plain,(
% 11.92/1.98    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),
% 11.92/1.98    inference(cnf_transformation,[],[f27])).
% 11.92/1.98  
% 11.92/1.98  fof(f7,axiom,(
% 11.92/1.98    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 11.92/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.92/1.98  
% 11.92/1.98  fof(f16,plain,(
% 11.92/1.98    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 11.92/1.98    inference(ennf_transformation,[],[f7])).
% 11.92/1.98  
% 11.92/1.98  fof(f37,plain,(
% 11.92/1.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 11.92/1.98    inference(cnf_transformation,[],[f16])).
% 11.92/1.98  
% 11.92/1.98  fof(f52,plain,(
% 11.92/1.98    ( ! [X0,X1] : (k1_setfam_1(k1_enumset1(X0,X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 11.92/1.98    inference(definition_unfolding,[],[f37,f47])).
% 11.92/1.98  
% 11.92/1.98  fof(f45,plain,(
% 11.92/1.98    r1_tarski(sK0,k2_relat_1(sK2))),
% 11.92/1.98    inference(cnf_transformation,[],[f27])).
% 11.92/1.98  
% 11.92/1.98  fof(f6,axiom,(
% 11.92/1.98    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 11.92/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.92/1.98  
% 11.92/1.98  fof(f36,plain,(
% 11.92/1.98    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 11.92/1.98    inference(cnf_transformation,[],[f6])).
% 11.92/1.98  
% 11.92/1.98  fof(f51,plain,(
% 11.92/1.98    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X0)) )),
% 11.92/1.98    inference(definition_unfolding,[],[f36,f47])).
% 11.92/1.98  
% 11.92/1.98  fof(f5,axiom,(
% 11.92/1.98    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 11.92/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.92/1.98  
% 11.92/1.98  fof(f15,plain,(
% 11.92/1.98    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 11.92/1.98    inference(ennf_transformation,[],[f5])).
% 11.92/1.98  
% 11.92/1.98  fof(f35,plain,(
% 11.92/1.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 11.92/1.98    inference(cnf_transformation,[],[f15])).
% 11.92/1.98  
% 11.92/1.98  fof(f4,axiom,(
% 11.92/1.98    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 11.92/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.92/1.98  
% 11.92/1.98  fof(f14,plain,(
% 11.92/1.98    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 11.92/1.98    inference(ennf_transformation,[],[f4])).
% 11.92/1.98  
% 11.92/1.98  fof(f34,plain,(
% 11.92/1.98    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 11.92/1.98    inference(cnf_transformation,[],[f14])).
% 11.92/1.98  
% 11.92/1.98  fof(f1,axiom,(
% 11.92/1.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 11.92/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.92/1.98  
% 11.92/1.98  fof(f23,plain,(
% 11.92/1.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.92/1.98    inference(nnf_transformation,[],[f1])).
% 11.92/1.98  
% 11.92/1.98  fof(f24,plain,(
% 11.92/1.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.92/1.98    inference(flattening,[],[f23])).
% 11.92/1.98  
% 11.92/1.98  fof(f28,plain,(
% 11.92/1.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 11.92/1.98    inference(cnf_transformation,[],[f24])).
% 11.92/1.98  
% 11.92/1.98  fof(f55,plain,(
% 11.92/1.98    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 11.92/1.98    inference(equality_resolution,[],[f28])).
% 11.92/1.98  
% 11.92/1.98  fof(f11,axiom,(
% 11.92/1.98    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 11.92/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.92/1.98  
% 11.92/1.98  fof(f19,plain,(
% 11.92/1.98    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 11.92/1.98    inference(ennf_transformation,[],[f11])).
% 11.92/1.98  
% 11.92/1.98  fof(f20,plain,(
% 11.92/1.98    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 11.92/1.98    inference(flattening,[],[f19])).
% 11.92/1.98  
% 11.92/1.98  fof(f41,plain,(
% 11.92/1.98    ( ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 11.92/1.98    inference(cnf_transformation,[],[f20])).
% 11.92/1.98  
% 11.92/1.98  fof(f2,axiom,(
% 11.92/1.98    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 11.92/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.92/1.98  
% 11.92/1.98  fof(f25,plain,(
% 11.92/1.98    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 11.92/1.98    inference(nnf_transformation,[],[f2])).
% 11.92/1.98  
% 11.92/1.98  fof(f31,plain,(
% 11.92/1.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 11.92/1.98    inference(cnf_transformation,[],[f25])).
% 11.92/1.98  
% 11.92/1.98  fof(f3,axiom,(
% 11.92/1.98    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 11.92/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.92/1.98  
% 11.92/1.98  fof(f33,plain,(
% 11.92/1.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 11.92/1.98    inference(cnf_transformation,[],[f3])).
% 11.92/1.98  
% 11.92/1.98  fof(f48,plain,(
% 11.92/1.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1)))) )),
% 11.92/1.98    inference(definition_unfolding,[],[f33,f47])).
% 11.92/1.98  
% 11.92/1.98  fof(f50,plain,(
% 11.92/1.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1)))) )),
% 11.92/1.98    inference(definition_unfolding,[],[f31,f48])).
% 11.92/1.98  
% 11.92/1.98  fof(f32,plain,(
% 11.92/1.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 11.92/1.98    inference(cnf_transformation,[],[f25])).
% 11.92/1.98  
% 11.92/1.98  fof(f49,plain,(
% 11.92/1.98    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1))) | ~r1_tarski(X0,X1)) )),
% 11.92/1.98    inference(definition_unfolding,[],[f32,f48])).
% 11.92/1.98  
% 11.92/1.98  fof(f46,plain,(
% 11.92/1.98    ~r1_tarski(sK0,sK1)),
% 11.92/1.98    inference(cnf_transformation,[],[f27])).
% 11.92/1.98  
% 11.92/1.98  cnf(c_15,negated_conjecture,
% 11.92/1.98      ( v1_relat_1(sK2) ),
% 11.92/1.98      inference(cnf_transformation,[],[f42]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_640,plain,
% 11.92/1.98      ( v1_relat_1(sK2) = iProver_top ),
% 11.92/1.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_9,plain,
% 11.92/1.98      ( ~ v1_relat_1(X0)
% 11.92/1.98      | ~ v1_funct_1(X0)
% 11.92/1.98      | k1_setfam_1(k1_enumset1(k10_relat_1(X0,X1),k10_relat_1(X0,X1),k10_relat_1(X0,X2))) = k10_relat_1(X0,k1_setfam_1(k1_enumset1(X1,X1,X2))) ),
% 11.92/1.98      inference(cnf_transformation,[],[f53]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_646,plain,
% 11.92/1.98      ( k1_setfam_1(k1_enumset1(k10_relat_1(X0,X1),k10_relat_1(X0,X1),k10_relat_1(X0,X2))) = k10_relat_1(X0,k1_setfam_1(k1_enumset1(X1,X1,X2)))
% 11.92/1.98      | v1_relat_1(X0) != iProver_top
% 11.92/1.98      | v1_funct_1(X0) != iProver_top ),
% 11.92/1.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_2124,plain,
% 11.92/1.98      ( k1_setfam_1(k1_enumset1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X0),k10_relat_1(sK2,X1))) = k10_relat_1(sK2,k1_setfam_1(k1_enumset1(X0,X0,X1)))
% 11.92/1.98      | v1_funct_1(sK2) != iProver_top ),
% 11.92/1.98      inference(superposition,[status(thm)],[c_640,c_646]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_14,negated_conjecture,
% 11.92/1.98      ( v1_funct_1(sK2) ),
% 11.92/1.98      inference(cnf_transformation,[],[f43]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_17,plain,
% 11.92/1.98      ( v1_funct_1(sK2) = iProver_top ),
% 11.92/1.98      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_2871,plain,
% 11.92/1.98      ( k1_setfam_1(k1_enumset1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X0),k10_relat_1(sK2,X1))) = k10_relat_1(sK2,k1_setfam_1(k1_enumset1(X0,X0,X1))) ),
% 11.92/1.98      inference(global_propositional_subsumption,
% 11.92/1.98                [status(thm)],
% 11.92/1.98                [c_2124,c_17]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_13,negated_conjecture,
% 11.92/1.98      ( r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
% 11.92/1.98      inference(cnf_transformation,[],[f44]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_642,plain,
% 11.92/1.98      ( r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) = iProver_top ),
% 11.92/1.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_8,plain,
% 11.92/1.98      ( ~ r1_tarski(X0,X1) | k1_setfam_1(k1_enumset1(X0,X0,X1)) = X0 ),
% 11.92/1.98      inference(cnf_transformation,[],[f52]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_647,plain,
% 11.92/1.98      ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = X0
% 11.92/1.98      | r1_tarski(X0,X1) != iProver_top ),
% 11.92/1.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_1159,plain,
% 11.92/1.98      ( k1_setfam_1(k1_enumset1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))) = k10_relat_1(sK2,sK0) ),
% 11.92/1.98      inference(superposition,[status(thm)],[c_642,c_647]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_2880,plain,
% 11.92/1.98      ( k10_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,sK1))) = k10_relat_1(sK2,sK0) ),
% 11.92/1.98      inference(superposition,[status(thm)],[c_2871,c_1159]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_12,negated_conjecture,
% 11.92/1.98      ( r1_tarski(sK0,k2_relat_1(sK2)) ),
% 11.92/1.98      inference(cnf_transformation,[],[f45]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_643,plain,
% 11.92/1.98      ( r1_tarski(sK0,k2_relat_1(sK2)) = iProver_top ),
% 11.92/1.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_7,plain,
% 11.92/1.98      ( r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X0) ),
% 11.92/1.98      inference(cnf_transformation,[],[f51]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_648,plain,
% 11.92/1.98      ( r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X0) = iProver_top ),
% 11.92/1.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_6,plain,
% 11.92/1.98      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 11.92/1.98      inference(cnf_transformation,[],[f35]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_649,plain,
% 11.92/1.98      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 11.92/1.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_972,plain,
% 11.92/1.98      ( k2_xboole_0(k1_setfam_1(k1_enumset1(X0,X0,X1)),X0) = X0 ),
% 11.92/1.98      inference(superposition,[status(thm)],[c_648,c_649]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_5,plain,
% 11.92/1.98      ( r1_tarski(X0,X1) | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
% 11.92/1.98      inference(cnf_transformation,[],[f34]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_650,plain,
% 11.92/1.98      ( r1_tarski(X0,X1) = iProver_top
% 11.92/1.98      | r1_tarski(k2_xboole_0(X0,X2),X1) != iProver_top ),
% 11.92/1.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_3581,plain,
% 11.92/1.98      ( r1_tarski(X0,X1) != iProver_top
% 11.92/1.98      | r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X2)),X1) = iProver_top ),
% 11.92/1.98      inference(superposition,[status(thm)],[c_972,c_650]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_9206,plain,
% 11.92/1.98      ( k2_xboole_0(k1_setfam_1(k1_enumset1(X0,X0,X1)),X2) = X2
% 11.92/1.98      | r1_tarski(X0,X2) != iProver_top ),
% 11.92/1.98      inference(superposition,[status(thm)],[c_3581,c_649]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_11121,plain,
% 11.92/1.98      ( k2_xboole_0(k1_setfam_1(k1_enumset1(sK0,sK0,X0)),k2_relat_1(sK2)) = k2_relat_1(sK2) ),
% 11.92/1.98      inference(superposition,[status(thm)],[c_643,c_9206]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_2,plain,
% 11.92/1.98      ( r1_tarski(X0,X0) ),
% 11.92/1.98      inference(cnf_transformation,[],[f55]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_653,plain,
% 11.92/1.98      ( r1_tarski(X0,X0) = iProver_top ),
% 11.92/1.98      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_1333,plain,
% 11.92/1.98      ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
% 11.92/1.98      inference(superposition,[status(thm)],[c_653,c_650]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_11918,plain,
% 11.92/1.98      ( r1_tarski(k1_setfam_1(k1_enumset1(sK0,sK0,X0)),k2_relat_1(sK2)) = iProver_top ),
% 11.92/1.98      inference(superposition,[status(thm)],[c_11121,c_1333]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_10,plain,
% 11.92/1.98      ( ~ r1_tarski(X0,k2_relat_1(X1))
% 11.92/1.98      | ~ v1_relat_1(X1)
% 11.92/1.98      | ~ v1_funct_1(X1)
% 11.92/1.98      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ),
% 11.92/1.98      inference(cnf_transformation,[],[f41]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_645,plain,
% 11.92/1.98      ( k9_relat_1(X0,k10_relat_1(X0,X1)) = X1
% 11.92/1.98      | r1_tarski(X1,k2_relat_1(X0)) != iProver_top
% 11.92/1.98      | v1_relat_1(X0) != iProver_top
% 11.92/1.98      | v1_funct_1(X0) != iProver_top ),
% 11.92/1.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_12462,plain,
% 11.92/1.98      ( k9_relat_1(sK2,k10_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,X0)))) = k1_setfam_1(k1_enumset1(sK0,sK0,X0))
% 11.92/1.98      | v1_relat_1(sK2) != iProver_top
% 11.92/1.98      | v1_funct_1(sK2) != iProver_top ),
% 11.92/1.98      inference(superposition,[status(thm)],[c_11918,c_645]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_16,plain,
% 11.92/1.98      ( v1_relat_1(sK2) = iProver_top ),
% 11.92/1.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_45253,plain,
% 11.92/1.98      ( k9_relat_1(sK2,k10_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,X0)))) = k1_setfam_1(k1_enumset1(sK0,sK0,X0)) ),
% 11.92/1.98      inference(global_propositional_subsumption,
% 11.92/1.98                [status(thm)],
% 11.92/1.98                [c_12462,c_16,c_17]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_45257,plain,
% 11.92/1.98      ( k9_relat_1(sK2,k10_relat_1(sK2,sK0)) = k1_setfam_1(k1_enumset1(sK0,sK0,sK1)) ),
% 11.92/1.98      inference(superposition,[status(thm)],[c_2880,c_45253]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_1127,plain,
% 11.92/1.98      ( k9_relat_1(sK2,k10_relat_1(sK2,sK0)) = sK0
% 11.92/1.98      | v1_relat_1(sK2) != iProver_top
% 11.92/1.98      | v1_funct_1(sK2) != iProver_top ),
% 11.92/1.98      inference(superposition,[status(thm)],[c_643,c_645]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_813,plain,
% 11.92/1.98      ( ~ r1_tarski(sK0,k2_relat_1(sK2))
% 11.92/1.98      | ~ v1_relat_1(sK2)
% 11.92/1.98      | ~ v1_funct_1(sK2)
% 11.92/1.98      | k9_relat_1(sK2,k10_relat_1(sK2,sK0)) = sK0 ),
% 11.92/1.98      inference(instantiation,[status(thm)],[c_10]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_1969,plain,
% 11.92/1.98      ( k9_relat_1(sK2,k10_relat_1(sK2,sK0)) = sK0 ),
% 11.92/1.98      inference(global_propositional_subsumption,
% 11.92/1.98                [status(thm)],
% 11.92/1.98                [c_1127,c_15,c_14,c_12,c_813]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_45316,plain,
% 11.92/1.98      ( k1_setfam_1(k1_enumset1(sK0,sK0,sK1)) = sK0 ),
% 11.92/1.98      inference(light_normalisation,[status(thm)],[c_45257,c_1969]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_4,plain,
% 11.92/1.98      ( r1_tarski(X0,X1)
% 11.92/1.98      | k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1))) != k1_xboole_0 ),
% 11.92/1.98      inference(cnf_transformation,[],[f50]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_651,plain,
% 11.92/1.98      ( k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1))) != k1_xboole_0
% 11.92/1.98      | r1_tarski(X0,X1) = iProver_top ),
% 11.92/1.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_46383,plain,
% 11.92/1.98      ( k5_xboole_0(sK0,sK0) != k1_xboole_0
% 11.92/1.98      | r1_tarski(sK0,sK1) = iProver_top ),
% 11.92/1.98      inference(superposition,[status(thm)],[c_45316,c_651]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_3,plain,
% 11.92/1.98      ( ~ r1_tarski(X0,X1)
% 11.92/1.98      | k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1))) = k1_xboole_0 ),
% 11.92/1.98      inference(cnf_transformation,[],[f49]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_652,plain,
% 11.92/1.98      ( k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1))) = k1_xboole_0
% 11.92/1.98      | r1_tarski(X0,X1) != iProver_top ),
% 11.92/1.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_1507,plain,
% 11.92/1.98      ( k5_xboole_0(sK0,k1_setfam_1(k1_enumset1(sK0,sK0,k2_relat_1(sK2)))) = k1_xboole_0 ),
% 11.92/1.98      inference(superposition,[status(thm)],[c_643,c_652]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_1158,plain,
% 11.92/1.98      ( k1_setfam_1(k1_enumset1(sK0,sK0,k2_relat_1(sK2))) = sK0 ),
% 11.92/1.98      inference(superposition,[status(thm)],[c_643,c_647]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_1674,plain,
% 11.92/1.98      ( k5_xboole_0(sK0,sK0) = k1_xboole_0 ),
% 11.92/1.98      inference(light_normalisation,[status(thm)],[c_1507,c_1158]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_46482,plain,
% 11.92/1.98      ( k1_xboole_0 != k1_xboole_0 | r1_tarski(sK0,sK1) = iProver_top ),
% 11.92/1.98      inference(light_normalisation,[status(thm)],[c_46383,c_1674]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_46483,plain,
% 11.92/1.98      ( r1_tarski(sK0,sK1) = iProver_top ),
% 11.92/1.98      inference(equality_resolution_simp,[status(thm)],[c_46482]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_11,negated_conjecture,
% 11.92/1.98      ( ~ r1_tarski(sK0,sK1) ),
% 11.92/1.98      inference(cnf_transformation,[],[f46]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_20,plain,
% 11.92/1.98      ( r1_tarski(sK0,sK1) != iProver_top ),
% 11.92/1.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(contradiction,plain,
% 11.92/1.98      ( $false ),
% 11.92/1.98      inference(minisat,[status(thm)],[c_46483,c_20]) ).
% 11.92/1.98  
% 11.92/1.98  
% 11.92/1.98  % SZS output end CNFRefutation for theBenchmark.p
% 11.92/1.98  
% 11.92/1.98  ------                               Statistics
% 11.92/1.98  
% 11.92/1.98  ------ Selected
% 11.92/1.98  
% 11.92/1.98  total_time:                             1.328
% 11.92/1.98  
%------------------------------------------------------------------------------
