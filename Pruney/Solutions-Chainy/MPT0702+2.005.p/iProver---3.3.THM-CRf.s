%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:52:07 EST 2020

% Result     : Theorem 23.62s
% Output     : CNFRefutation 23.62s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 588 expanded)
%              Number of clauses        :   58 ( 159 expanded)
%              Number of leaves         :   11 ( 138 expanded)
%              Depth                    :   18
%              Number of atoms          :  233 (1751 expanded)
%              Number of equality atoms :   93 ( 406 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f45,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f30,f31,f31])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( v2_funct_1(X2)
          & r1_tarski(X0,k1_relat_1(X2))
          & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( v2_funct_1(X2)
            & r1_tarski(X0,k1_relat_1(X2))
            & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) )
         => r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & v2_funct_1(X2)
      & r1_tarski(X0,k1_relat_1(X2))
      & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & v2_funct_1(X2)
      & r1_tarski(X0,k1_relat_1(X2))
      & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f23,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,X1)
        & v2_funct_1(X2)
        & r1_tarski(X0,k1_relat_1(X2))
        & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(sK0,sK1)
      & v2_funct_1(sK2)
      & r1_tarski(sK0,k1_relat_1(sK2))
      & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ~ r1_tarski(sK0,sK1)
    & v2_funct_1(sK2)
    & r1_tarski(sK0,k1_relat_1(sK2))
    & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f23])).

fof(f36,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( v2_funct_1(X2)
       => k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k3_xboole_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f13])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f42,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f32,f31])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k1_setfam_1(k2_enumset1(k9_relat_1(X2,X0),k9_relat_1(X2,X0),k9_relat_1(X2,X0),k9_relat_1(X2,X1))) = k9_relat_1(X2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f33,f42,f42])).

fof(f37,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f40,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f38,plain,(
    r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f24])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f29,f42])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f39,plain,(
    r1_tarski(sK0,k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f24])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f43,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f28,f42])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f21])).

fof(f27,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f48,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f25])).

fof(f41,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_5,plain,
    ( k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_14,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_430,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k1_setfam_1(k2_enumset1(k9_relat_1(X0,X1),k9_relat_1(X0,X1),k9_relat_1(X0,X1),k9_relat_1(X0,X2))) = k9_relat_1(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_438,plain,
    ( k1_setfam_1(k2_enumset1(k9_relat_1(X0,X1),k9_relat_1(X0,X1),k9_relat_1(X0,X1),k9_relat_1(X0,X2))) = k9_relat_1(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1265,plain,
    ( k1_setfam_1(k2_enumset1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X0),k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) = k9_relat_1(sK2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_430,c_438])).

cnf(c_13,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_16,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_10,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_19,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3083,plain,
    ( k1_setfam_1(k2_enumset1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X0),k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) = k9_relat_1(sK2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1265,c_16,c_19])).

cnf(c_3089,plain,
    ( k1_setfam_1(k2_enumset1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X0),k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) = k9_relat_1(sK2,k1_setfam_1(k2_enumset1(X1,X1,X1,X0))) ),
    inference(superposition,[status(thm)],[c_5,c_3083])).

cnf(c_12,negated_conjecture,
    ( r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_432,plain,
    ( r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_439,plain,
    ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_944,plain,
    ( k1_setfam_1(k2_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) = k9_relat_1(sK2,sK0) ),
    inference(superposition,[status(thm)],[c_432,c_439])).

cnf(c_3410,plain,
    ( k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK0))) = k9_relat_1(sK2,sK0) ),
    inference(superposition,[status(thm)],[c_3089,c_944])).

cnf(c_8,plain,
    ( r1_tarski(k10_relat_1(X0,k9_relat_1(X0,X1)),X1)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_436,plain,
    ( r1_tarski(k10_relat_1(X0,k9_relat_1(X0,X1)),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_942,plain,
    ( k1_setfam_1(k2_enumset1(k10_relat_1(X0,k9_relat_1(X0,X1)),k10_relat_1(X0,k9_relat_1(X0,X1)),k10_relat_1(X0,k9_relat_1(X0,X1)),X1)) = k10_relat_1(X0,k9_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_436,c_439])).

cnf(c_1274,plain,
    ( k1_setfam_1(k2_enumset1(k10_relat_1(sK2,k9_relat_1(sK2,X0)),k10_relat_1(sK2,k9_relat_1(sK2,X0)),k10_relat_1(sK2,k9_relat_1(sK2,X0)),X0)) = k10_relat_1(sK2,k9_relat_1(sK2,X0))
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_430,c_942])).

cnf(c_4192,plain,
    ( k1_setfam_1(k2_enumset1(k10_relat_1(sK2,k9_relat_1(sK2,X0)),k10_relat_1(sK2,k9_relat_1(sK2,X0)),k10_relat_1(sK2,k9_relat_1(sK2,X0)),X0)) = k10_relat_1(sK2,k9_relat_1(sK2,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1274,c_16,c_19])).

cnf(c_4204,plain,
    ( k1_setfam_1(k2_enumset1(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),k10_relat_1(sK2,k9_relat_1(sK2,sK0)),k10_relat_1(sK2,k9_relat_1(sK2,sK0)),k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK0)))) = k10_relat_1(sK2,k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK0)))) ),
    inference(superposition,[status(thm)],[c_3410,c_4192])).

cnf(c_11,negated_conjecture,
    ( r1_tarski(sK0,k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_433,plain,
    ( r1_tarski(sK0,k1_relat_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_7,plain,
    ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
    | ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_437,plain,
    ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) = iProver_top
    | r1_tarski(X0,k1_relat_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1118,plain,
    ( k1_setfam_1(k2_enumset1(X0,X0,X0,k10_relat_1(X1,k9_relat_1(X1,X0)))) = X0
    | r1_tarski(X0,k1_relat_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_437,c_439])).

cnf(c_2272,plain,
    ( k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK0)))) = sK0
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_433,c_1118])).

cnf(c_570,plain,
    ( r1_tarski(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK0)))
    | ~ r1_tarski(sK0,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_757,plain,
    ( ~ r1_tarski(sK0,X0)
    | k1_setfam_1(k2_enumset1(sK0,sK0,sK0,X0)) = sK0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1030,plain,
    ( ~ r1_tarski(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK0)))
    | k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK0)))) = sK0 ),
    inference(instantiation,[status(thm)],[c_757])).

cnf(c_2465,plain,
    ( k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK0)))) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2272,c_14,c_11,c_570,c_1030])).

cnf(c_3,plain,
    ( r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_440,plain,
    ( r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_809,plain,
    ( r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_5,c_440])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f27])).

cnf(c_442,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1079,plain,
    ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = X1
    | r1_tarski(X1,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_809,c_442])).

cnf(c_1975,plain,
    ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = X1
    | r1_tarski(X1,k1_setfam_1(k2_enumset1(X1,X1,X1,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5,c_1079])).

cnf(c_2472,plain,
    ( k1_setfam_1(k2_enumset1(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),k10_relat_1(sK2,k9_relat_1(sK2,sK0)),k10_relat_1(sK2,k9_relat_1(sK2,sK0)),sK0)) = sK0
    | r1_tarski(sK0,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2465,c_1975])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_998,plain,
    ( r1_tarski(sK0,sK0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1003,plain,
    ( r1_tarski(sK0,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_998])).

cnf(c_3071,plain,
    ( k1_setfam_1(k2_enumset1(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),k10_relat_1(sK2,k9_relat_1(sK2,sK0)),k10_relat_1(sK2,k9_relat_1(sK2,sK0)),sK0)) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2472,c_1003])).

cnf(c_4214,plain,
    ( k10_relat_1(sK2,k9_relat_1(sK2,sK0)) = sK0 ),
    inference(superposition,[status(thm)],[c_4192,c_3071])).

cnf(c_4236,plain,
    ( k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK0)))) = k10_relat_1(sK2,k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK0)))) ),
    inference(light_normalisation,[status(thm)],[c_4204,c_4214])).

cnf(c_4238,plain,
    ( k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK0)))) = k10_relat_1(sK2,k9_relat_1(sK2,sK0)) ),
    inference(light_normalisation,[status(thm)],[c_4236,c_3410])).

cnf(c_79684,plain,
    ( k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK0)))) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_4238,c_4214])).

cnf(c_941,plain,
    ( k1_setfam_1(k2_enumset1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0)) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(superposition,[status(thm)],[c_440,c_439])).

cnf(c_6069,plain,
    ( k1_setfam_1(k2_enumset1(X0,X0,X0,k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(superposition,[status(thm)],[c_5,c_941])).

cnf(c_6377,plain,
    ( k1_setfam_1(k2_enumset1(X0,X0,X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X0)))) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(superposition,[status(thm)],[c_5,c_6069])).

cnf(c_79884,plain,
    ( k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)) = sK0 ),
    inference(superposition,[status(thm)],[c_79684,c_6377])).

cnf(c_81807,plain,
    ( r1_tarski(sK0,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_79884,c_809])).

cnf(c_9,negated_conjecture,
    ( ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_20,plain,
    ( r1_tarski(sK0,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_81807,c_20])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n013.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.18/0.33  % CPULimit   : 60
% 0.18/0.33  % WCLimit    : 600
% 0.18/0.33  % DateTime   : Tue Dec  1 10:11:24 EST 2020
% 0.18/0.33  % CPUTime    : 
% 0.18/0.34  % Running in FOF mode
% 23.62/3.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 23.62/3.49  
% 23.62/3.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 23.62/3.49  
% 23.62/3.49  ------  iProver source info
% 23.62/3.49  
% 23.62/3.49  git: date: 2020-06-30 10:37:57 +0100
% 23.62/3.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 23.62/3.49  git: non_committed_changes: false
% 23.62/3.49  git: last_make_outside_of_git: false
% 23.62/3.49  
% 23.62/3.49  ------ 
% 23.62/3.49  
% 23.62/3.49  ------ Input Options
% 23.62/3.49  
% 23.62/3.49  --out_options                           all
% 23.62/3.49  --tptp_safe_out                         true
% 23.62/3.49  --problem_path                          ""
% 23.62/3.49  --include_path                          ""
% 23.62/3.49  --clausifier                            res/vclausify_rel
% 23.62/3.49  --clausifier_options                    --mode clausify
% 23.62/3.49  --stdin                                 false
% 23.62/3.49  --stats_out                             sel
% 23.62/3.49  
% 23.62/3.49  ------ General Options
% 23.62/3.49  
% 23.62/3.49  --fof                                   false
% 23.62/3.49  --time_out_real                         604.99
% 23.62/3.49  --time_out_virtual                      -1.
% 23.62/3.49  --symbol_type_check                     false
% 23.62/3.49  --clausify_out                          false
% 23.62/3.49  --sig_cnt_out                           false
% 23.62/3.49  --trig_cnt_out                          false
% 23.62/3.49  --trig_cnt_out_tolerance                1.
% 23.62/3.49  --trig_cnt_out_sk_spl                   false
% 23.62/3.49  --abstr_cl_out                          false
% 23.62/3.49  
% 23.62/3.49  ------ Global Options
% 23.62/3.49  
% 23.62/3.49  --schedule                              none
% 23.62/3.49  --add_important_lit                     false
% 23.62/3.49  --prop_solver_per_cl                    1000
% 23.62/3.49  --min_unsat_core                        false
% 23.62/3.49  --soft_assumptions                      false
% 23.62/3.49  --soft_lemma_size                       3
% 23.62/3.49  --prop_impl_unit_size                   0
% 23.62/3.49  --prop_impl_unit                        []
% 23.62/3.49  --share_sel_clauses                     true
% 23.62/3.49  --reset_solvers                         false
% 23.62/3.49  --bc_imp_inh                            [conj_cone]
% 23.62/3.49  --conj_cone_tolerance                   3.
% 23.62/3.49  --extra_neg_conj                        none
% 23.62/3.49  --large_theory_mode                     true
% 23.62/3.49  --prolific_symb_bound                   200
% 23.62/3.49  --lt_threshold                          2000
% 23.62/3.49  --clause_weak_htbl                      true
% 23.62/3.49  --gc_record_bc_elim                     false
% 23.62/3.49  
% 23.62/3.49  ------ Preprocessing Options
% 23.62/3.49  
% 23.62/3.49  --preprocessing_flag                    true
% 23.62/3.49  --time_out_prep_mult                    0.1
% 23.62/3.49  --splitting_mode                        input
% 23.62/3.49  --splitting_grd                         true
% 23.62/3.49  --splitting_cvd                         false
% 23.62/3.49  --splitting_cvd_svl                     false
% 23.62/3.49  --splitting_nvd                         32
% 23.62/3.49  --sub_typing                            true
% 23.62/3.49  --prep_gs_sim                           false
% 23.62/3.49  --prep_unflatten                        true
% 23.62/3.49  --prep_res_sim                          true
% 23.62/3.49  --prep_upred                            true
% 23.62/3.49  --prep_sem_filter                       exhaustive
% 23.62/3.49  --prep_sem_filter_out                   false
% 23.62/3.49  --pred_elim                             false
% 23.62/3.49  --res_sim_input                         true
% 23.62/3.49  --eq_ax_congr_red                       true
% 23.62/3.49  --pure_diseq_elim                       true
% 23.62/3.49  --brand_transform                       false
% 23.62/3.49  --non_eq_to_eq                          false
% 23.62/3.49  --prep_def_merge                        true
% 23.62/3.49  --prep_def_merge_prop_impl              false
% 23.62/3.49  --prep_def_merge_mbd                    true
% 23.62/3.49  --prep_def_merge_tr_red                 false
% 23.62/3.49  --prep_def_merge_tr_cl                  false
% 23.62/3.49  --smt_preprocessing                     true
% 23.62/3.49  --smt_ac_axioms                         fast
% 23.62/3.49  --preprocessed_out                      false
% 23.62/3.49  --preprocessed_stats                    false
% 23.62/3.49  
% 23.62/3.49  ------ Abstraction refinement Options
% 23.62/3.49  
% 23.62/3.49  --abstr_ref                             []
% 23.62/3.49  --abstr_ref_prep                        false
% 23.62/3.49  --abstr_ref_until_sat                   false
% 23.62/3.49  --abstr_ref_sig_restrict                funpre
% 23.62/3.49  --abstr_ref_af_restrict_to_split_sk     false
% 23.62/3.49  --abstr_ref_under                       []
% 23.62/3.49  
% 23.62/3.49  ------ SAT Options
% 23.62/3.49  
% 23.62/3.49  --sat_mode                              false
% 23.62/3.49  --sat_fm_restart_options                ""
% 23.62/3.49  --sat_gr_def                            false
% 23.62/3.49  --sat_epr_types                         true
% 23.62/3.49  --sat_non_cyclic_types                  false
% 23.62/3.49  --sat_finite_models                     false
% 23.62/3.49  --sat_fm_lemmas                         false
% 23.62/3.49  --sat_fm_prep                           false
% 23.62/3.49  --sat_fm_uc_incr                        true
% 23.62/3.49  --sat_out_model                         small
% 23.62/3.49  --sat_out_clauses                       false
% 23.62/3.49  
% 23.62/3.49  ------ QBF Options
% 23.62/3.49  
% 23.62/3.49  --qbf_mode                              false
% 23.62/3.49  --qbf_elim_univ                         false
% 23.62/3.49  --qbf_dom_inst                          none
% 23.62/3.49  --qbf_dom_pre_inst                      false
% 23.62/3.49  --qbf_sk_in                             false
% 23.62/3.49  --qbf_pred_elim                         true
% 23.62/3.49  --qbf_split                             512
% 23.62/3.49  
% 23.62/3.49  ------ BMC1 Options
% 23.62/3.49  
% 23.62/3.49  --bmc1_incremental                      false
% 23.62/3.49  --bmc1_axioms                           reachable_all
% 23.62/3.49  --bmc1_min_bound                        0
% 23.62/3.49  --bmc1_max_bound                        -1
% 23.62/3.49  --bmc1_max_bound_default                -1
% 23.62/3.49  --bmc1_symbol_reachability              true
% 23.62/3.49  --bmc1_property_lemmas                  false
% 23.62/3.49  --bmc1_k_induction                      false
% 23.62/3.49  --bmc1_non_equiv_states                 false
% 23.62/3.49  --bmc1_deadlock                         false
% 23.62/3.49  --bmc1_ucm                              false
% 23.62/3.49  --bmc1_add_unsat_core                   none
% 23.62/3.49  --bmc1_unsat_core_children              false
% 23.62/3.49  --bmc1_unsat_core_extrapolate_axioms    false
% 23.62/3.49  --bmc1_out_stat                         full
% 23.62/3.49  --bmc1_ground_init                      false
% 23.62/3.49  --bmc1_pre_inst_next_state              false
% 23.62/3.49  --bmc1_pre_inst_state                   false
% 23.62/3.49  --bmc1_pre_inst_reach_state             false
% 23.62/3.49  --bmc1_out_unsat_core                   false
% 23.62/3.49  --bmc1_aig_witness_out                  false
% 23.62/3.49  --bmc1_verbose                          false
% 23.62/3.49  --bmc1_dump_clauses_tptp                false
% 23.62/3.49  --bmc1_dump_unsat_core_tptp             false
% 23.62/3.49  --bmc1_dump_file                        -
% 23.62/3.49  --bmc1_ucm_expand_uc_limit              128
% 23.62/3.49  --bmc1_ucm_n_expand_iterations          6
% 23.62/3.49  --bmc1_ucm_extend_mode                  1
% 23.62/3.49  --bmc1_ucm_init_mode                    2
% 23.62/3.49  --bmc1_ucm_cone_mode                    none
% 23.62/3.49  --bmc1_ucm_reduced_relation_type        0
% 23.62/3.49  --bmc1_ucm_relax_model                  4
% 23.62/3.49  --bmc1_ucm_full_tr_after_sat            true
% 23.62/3.49  --bmc1_ucm_expand_neg_assumptions       false
% 23.62/3.49  --bmc1_ucm_layered_model                none
% 23.62/3.49  --bmc1_ucm_max_lemma_size               10
% 23.62/3.49  
% 23.62/3.49  ------ AIG Options
% 23.62/3.49  
% 23.62/3.49  --aig_mode                              false
% 23.62/3.49  
% 23.62/3.49  ------ Instantiation Options
% 23.62/3.49  
% 23.62/3.49  --instantiation_flag                    true
% 23.62/3.49  --inst_sos_flag                         false
% 23.62/3.49  --inst_sos_phase                        true
% 23.62/3.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 23.62/3.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 23.62/3.49  --inst_lit_sel_side                     num_symb
% 23.62/3.49  --inst_solver_per_active                1400
% 23.62/3.49  --inst_solver_calls_frac                1.
% 23.62/3.49  --inst_passive_queue_type               priority_queues
% 23.62/3.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 23.62/3.49  --inst_passive_queues_freq              [25;2]
% 23.62/3.49  --inst_dismatching                      true
% 23.62/3.49  --inst_eager_unprocessed_to_passive     true
% 23.62/3.49  --inst_prop_sim_given                   true
% 23.62/3.49  --inst_prop_sim_new                     false
% 23.62/3.49  --inst_subs_new                         false
% 23.62/3.50  --inst_eq_res_simp                      false
% 23.62/3.50  --inst_subs_given                       false
% 23.62/3.50  --inst_orphan_elimination               true
% 23.62/3.50  --inst_learning_loop_flag               true
% 23.62/3.50  --inst_learning_start                   3000
% 23.62/3.50  --inst_learning_factor                  2
% 23.62/3.50  --inst_start_prop_sim_after_learn       3
% 23.62/3.50  --inst_sel_renew                        solver
% 23.62/3.50  --inst_lit_activity_flag                true
% 23.62/3.50  --inst_restr_to_given                   false
% 23.62/3.50  --inst_activity_threshold               500
% 23.62/3.50  --inst_out_proof                        true
% 23.62/3.50  
% 23.62/3.50  ------ Resolution Options
% 23.62/3.50  
% 23.62/3.50  --resolution_flag                       true
% 23.62/3.50  --res_lit_sel                           adaptive
% 23.62/3.50  --res_lit_sel_side                      none
% 23.62/3.50  --res_ordering                          kbo
% 23.62/3.50  --res_to_prop_solver                    active
% 23.62/3.50  --res_prop_simpl_new                    false
% 23.62/3.50  --res_prop_simpl_given                  true
% 23.62/3.50  --res_passive_queue_type                priority_queues
% 23.62/3.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 23.62/3.50  --res_passive_queues_freq               [15;5]
% 23.62/3.50  --res_forward_subs                      full
% 23.62/3.50  --res_backward_subs                     full
% 23.62/3.50  --res_forward_subs_resolution           true
% 23.62/3.50  --res_backward_subs_resolution          true
% 23.62/3.50  --res_orphan_elimination                true
% 23.62/3.50  --res_time_limit                        2.
% 23.62/3.50  --res_out_proof                         true
% 23.62/3.50  
% 23.62/3.50  ------ Superposition Options
% 23.62/3.50  
% 23.62/3.50  --superposition_flag                    true
% 23.62/3.50  --sup_passive_queue_type                priority_queues
% 23.62/3.50  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 23.62/3.50  --sup_passive_queues_freq               [1;4]
% 23.62/3.50  --demod_completeness_check              fast
% 23.62/3.50  --demod_use_ground                      true
% 23.62/3.50  --sup_to_prop_solver                    passive
% 23.62/3.50  --sup_prop_simpl_new                    true
% 23.62/3.50  --sup_prop_simpl_given                  true
% 23.62/3.50  --sup_fun_splitting                     false
% 23.62/3.50  --sup_smt_interval                      50000
% 23.62/3.50  
% 23.62/3.50  ------ Superposition Simplification Setup
% 23.62/3.50  
% 23.62/3.50  --sup_indices_passive                   []
% 23.62/3.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.62/3.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.62/3.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.62/3.50  --sup_full_triv                         [TrivRules;PropSubs]
% 23.62/3.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.62/3.50  --sup_full_bw                           [BwDemod]
% 23.62/3.50  --sup_immed_triv                        [TrivRules]
% 23.62/3.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 23.62/3.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.62/3.50  --sup_immed_bw_main                     []
% 23.62/3.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 23.62/3.50  --sup_input_triv                        [Unflattening;TrivRules]
% 23.62/3.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.62/3.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 23.62/3.50  
% 23.62/3.50  ------ Combination Options
% 23.62/3.50  
% 23.62/3.50  --comb_res_mult                         3
% 23.62/3.50  --comb_sup_mult                         2
% 23.62/3.50  --comb_inst_mult                        10
% 23.62/3.50  
% 23.62/3.50  ------ Debug Options
% 23.62/3.50  
% 23.62/3.50  --dbg_backtrace                         false
% 23.62/3.50  --dbg_dump_prop_clauses                 false
% 23.62/3.50  --dbg_dump_prop_clauses_file            -
% 23.62/3.50  --dbg_out_stat                          false
% 23.62/3.50  ------ Parsing...
% 23.62/3.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 23.62/3.50  
% 23.62/3.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 23.62/3.50  
% 23.62/3.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 23.62/3.50  
% 23.62/3.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 23.62/3.50  ------ Proving...
% 23.62/3.50  ------ Problem Properties 
% 23.62/3.50  
% 23.62/3.50  
% 23.62/3.50  clauses                                 14
% 23.62/3.50  conjectures                             6
% 23.62/3.50  EPR                                     6
% 23.62/3.50  Horn                                    14
% 23.62/3.50  unary                                   9
% 23.62/3.50  binary                                  1
% 23.62/3.50  lits                                    25
% 23.62/3.50  lits eq                                 4
% 23.62/3.50  fd_pure                                 0
% 23.62/3.50  fd_pseudo                               0
% 23.62/3.50  fd_cond                                 0
% 23.62/3.50  fd_pseudo_cond                          1
% 23.62/3.50  AC symbols                              0
% 23.62/3.50  
% 23.62/3.50  ------ Input Options Time Limit: Unbounded
% 23.62/3.50  
% 23.62/3.50  
% 23.62/3.50  ------ 
% 23.62/3.50  Current options:
% 23.62/3.50  ------ 
% 23.62/3.50  
% 23.62/3.50  ------ Input Options
% 23.62/3.50  
% 23.62/3.50  --out_options                           all
% 23.62/3.50  --tptp_safe_out                         true
% 23.62/3.50  --problem_path                          ""
% 23.62/3.50  --include_path                          ""
% 23.62/3.50  --clausifier                            res/vclausify_rel
% 23.62/3.50  --clausifier_options                    --mode clausify
% 23.62/3.50  --stdin                                 false
% 23.62/3.50  --stats_out                             sel
% 23.62/3.50  
% 23.62/3.50  ------ General Options
% 23.62/3.50  
% 23.62/3.50  --fof                                   false
% 23.62/3.50  --time_out_real                         604.99
% 23.62/3.50  --time_out_virtual                      -1.
% 23.62/3.50  --symbol_type_check                     false
% 23.62/3.50  --clausify_out                          false
% 23.62/3.50  --sig_cnt_out                           false
% 23.62/3.50  --trig_cnt_out                          false
% 23.62/3.50  --trig_cnt_out_tolerance                1.
% 23.62/3.50  --trig_cnt_out_sk_spl                   false
% 23.62/3.50  --abstr_cl_out                          false
% 23.62/3.50  
% 23.62/3.50  ------ Global Options
% 23.62/3.50  
% 23.62/3.50  --schedule                              none
% 23.62/3.50  --add_important_lit                     false
% 23.62/3.50  --prop_solver_per_cl                    1000
% 23.62/3.50  --min_unsat_core                        false
% 23.62/3.50  --soft_assumptions                      false
% 23.62/3.50  --soft_lemma_size                       3
% 23.62/3.50  --prop_impl_unit_size                   0
% 23.62/3.50  --prop_impl_unit                        []
% 23.62/3.50  --share_sel_clauses                     true
% 23.62/3.50  --reset_solvers                         false
% 23.62/3.50  --bc_imp_inh                            [conj_cone]
% 23.62/3.50  --conj_cone_tolerance                   3.
% 23.62/3.50  --extra_neg_conj                        none
% 23.62/3.50  --large_theory_mode                     true
% 23.62/3.50  --prolific_symb_bound                   200
% 23.62/3.50  --lt_threshold                          2000
% 23.62/3.50  --clause_weak_htbl                      true
% 23.62/3.50  --gc_record_bc_elim                     false
% 23.62/3.50  
% 23.62/3.50  ------ Preprocessing Options
% 23.62/3.50  
% 23.62/3.50  --preprocessing_flag                    true
% 23.62/3.50  --time_out_prep_mult                    0.1
% 23.62/3.50  --splitting_mode                        input
% 23.62/3.50  --splitting_grd                         true
% 23.62/3.50  --splitting_cvd                         false
% 23.62/3.50  --splitting_cvd_svl                     false
% 23.62/3.50  --splitting_nvd                         32
% 23.62/3.50  --sub_typing                            true
% 23.62/3.50  --prep_gs_sim                           false
% 23.62/3.50  --prep_unflatten                        true
% 23.62/3.50  --prep_res_sim                          true
% 23.62/3.50  --prep_upred                            true
% 23.62/3.50  --prep_sem_filter                       exhaustive
% 23.62/3.50  --prep_sem_filter_out                   false
% 23.62/3.50  --pred_elim                             false
% 23.62/3.50  --res_sim_input                         true
% 23.62/3.50  --eq_ax_congr_red                       true
% 23.62/3.50  --pure_diseq_elim                       true
% 23.62/3.50  --brand_transform                       false
% 23.62/3.50  --non_eq_to_eq                          false
% 23.62/3.50  --prep_def_merge                        true
% 23.62/3.50  --prep_def_merge_prop_impl              false
% 23.62/3.50  --prep_def_merge_mbd                    true
% 23.62/3.50  --prep_def_merge_tr_red                 false
% 23.62/3.50  --prep_def_merge_tr_cl                  false
% 23.62/3.50  --smt_preprocessing                     true
% 23.62/3.50  --smt_ac_axioms                         fast
% 23.62/3.50  --preprocessed_out                      false
% 23.62/3.50  --preprocessed_stats                    false
% 23.62/3.50  
% 23.62/3.50  ------ Abstraction refinement Options
% 23.62/3.50  
% 23.62/3.50  --abstr_ref                             []
% 23.62/3.50  --abstr_ref_prep                        false
% 23.62/3.50  --abstr_ref_until_sat                   false
% 23.62/3.50  --abstr_ref_sig_restrict                funpre
% 23.62/3.50  --abstr_ref_af_restrict_to_split_sk     false
% 23.62/3.50  --abstr_ref_under                       []
% 23.62/3.50  
% 23.62/3.50  ------ SAT Options
% 23.62/3.50  
% 23.62/3.50  --sat_mode                              false
% 23.62/3.50  --sat_fm_restart_options                ""
% 23.62/3.50  --sat_gr_def                            false
% 23.62/3.50  --sat_epr_types                         true
% 23.62/3.50  --sat_non_cyclic_types                  false
% 23.62/3.50  --sat_finite_models                     false
% 23.62/3.50  --sat_fm_lemmas                         false
% 23.62/3.50  --sat_fm_prep                           false
% 23.62/3.50  --sat_fm_uc_incr                        true
% 23.62/3.50  --sat_out_model                         small
% 23.62/3.50  --sat_out_clauses                       false
% 23.62/3.50  
% 23.62/3.50  ------ QBF Options
% 23.62/3.50  
% 23.62/3.50  --qbf_mode                              false
% 23.62/3.50  --qbf_elim_univ                         false
% 23.62/3.50  --qbf_dom_inst                          none
% 23.62/3.50  --qbf_dom_pre_inst                      false
% 23.62/3.50  --qbf_sk_in                             false
% 23.62/3.50  --qbf_pred_elim                         true
% 23.62/3.50  --qbf_split                             512
% 23.62/3.50  
% 23.62/3.50  ------ BMC1 Options
% 23.62/3.50  
% 23.62/3.50  --bmc1_incremental                      false
% 23.62/3.50  --bmc1_axioms                           reachable_all
% 23.62/3.50  --bmc1_min_bound                        0
% 23.62/3.50  --bmc1_max_bound                        -1
% 23.62/3.50  --bmc1_max_bound_default                -1
% 23.62/3.50  --bmc1_symbol_reachability              true
% 23.62/3.50  --bmc1_property_lemmas                  false
% 23.62/3.50  --bmc1_k_induction                      false
% 23.62/3.50  --bmc1_non_equiv_states                 false
% 23.62/3.50  --bmc1_deadlock                         false
% 23.62/3.50  --bmc1_ucm                              false
% 23.62/3.50  --bmc1_add_unsat_core                   none
% 23.62/3.50  --bmc1_unsat_core_children              false
% 23.62/3.50  --bmc1_unsat_core_extrapolate_axioms    false
% 23.62/3.50  --bmc1_out_stat                         full
% 23.62/3.50  --bmc1_ground_init                      false
% 23.62/3.50  --bmc1_pre_inst_next_state              false
% 23.62/3.50  --bmc1_pre_inst_state                   false
% 23.62/3.50  --bmc1_pre_inst_reach_state             false
% 23.62/3.50  --bmc1_out_unsat_core                   false
% 23.62/3.50  --bmc1_aig_witness_out                  false
% 23.62/3.50  --bmc1_verbose                          false
% 23.62/3.50  --bmc1_dump_clauses_tptp                false
% 23.62/3.50  --bmc1_dump_unsat_core_tptp             false
% 23.62/3.50  --bmc1_dump_file                        -
% 23.62/3.50  --bmc1_ucm_expand_uc_limit              128
% 23.62/3.50  --bmc1_ucm_n_expand_iterations          6
% 23.62/3.50  --bmc1_ucm_extend_mode                  1
% 23.62/3.50  --bmc1_ucm_init_mode                    2
% 23.62/3.50  --bmc1_ucm_cone_mode                    none
% 23.62/3.50  --bmc1_ucm_reduced_relation_type        0
% 23.62/3.50  --bmc1_ucm_relax_model                  4
% 23.62/3.50  --bmc1_ucm_full_tr_after_sat            true
% 23.62/3.50  --bmc1_ucm_expand_neg_assumptions       false
% 23.62/3.50  --bmc1_ucm_layered_model                none
% 23.62/3.50  --bmc1_ucm_max_lemma_size               10
% 23.62/3.50  
% 23.62/3.50  ------ AIG Options
% 23.62/3.50  
% 23.62/3.50  --aig_mode                              false
% 23.62/3.50  
% 23.62/3.50  ------ Instantiation Options
% 23.62/3.50  
% 23.62/3.50  --instantiation_flag                    true
% 23.62/3.50  --inst_sos_flag                         false
% 23.62/3.50  --inst_sos_phase                        true
% 23.62/3.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 23.62/3.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 23.62/3.50  --inst_lit_sel_side                     num_symb
% 23.62/3.50  --inst_solver_per_active                1400
% 23.62/3.50  --inst_solver_calls_frac                1.
% 23.62/3.50  --inst_passive_queue_type               priority_queues
% 23.62/3.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 23.62/3.50  --inst_passive_queues_freq              [25;2]
% 23.62/3.50  --inst_dismatching                      true
% 23.62/3.50  --inst_eager_unprocessed_to_passive     true
% 23.62/3.50  --inst_prop_sim_given                   true
% 23.62/3.50  --inst_prop_sim_new                     false
% 23.62/3.50  --inst_subs_new                         false
% 23.62/3.50  --inst_eq_res_simp                      false
% 23.62/3.50  --inst_subs_given                       false
% 23.62/3.50  --inst_orphan_elimination               true
% 23.62/3.50  --inst_learning_loop_flag               true
% 23.62/3.50  --inst_learning_start                   3000
% 23.62/3.50  --inst_learning_factor                  2
% 23.62/3.50  --inst_start_prop_sim_after_learn       3
% 23.62/3.50  --inst_sel_renew                        solver
% 23.62/3.50  --inst_lit_activity_flag                true
% 23.62/3.50  --inst_restr_to_given                   false
% 23.62/3.50  --inst_activity_threshold               500
% 23.62/3.50  --inst_out_proof                        true
% 23.62/3.50  
% 23.62/3.50  ------ Resolution Options
% 23.62/3.50  
% 23.62/3.50  --resolution_flag                       true
% 23.62/3.50  --res_lit_sel                           adaptive
% 23.62/3.50  --res_lit_sel_side                      none
% 23.62/3.50  --res_ordering                          kbo
% 23.62/3.50  --res_to_prop_solver                    active
% 23.62/3.50  --res_prop_simpl_new                    false
% 23.62/3.50  --res_prop_simpl_given                  true
% 23.62/3.50  --res_passive_queue_type                priority_queues
% 23.62/3.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 23.62/3.50  --res_passive_queues_freq               [15;5]
% 23.62/3.50  --res_forward_subs                      full
% 23.62/3.50  --res_backward_subs                     full
% 23.62/3.50  --res_forward_subs_resolution           true
% 23.62/3.50  --res_backward_subs_resolution          true
% 23.62/3.50  --res_orphan_elimination                true
% 23.62/3.50  --res_time_limit                        2.
% 23.62/3.50  --res_out_proof                         true
% 23.62/3.50  
% 23.62/3.50  ------ Superposition Options
% 23.62/3.50  
% 23.62/3.50  --superposition_flag                    true
% 23.62/3.50  --sup_passive_queue_type                priority_queues
% 23.62/3.50  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 23.62/3.50  --sup_passive_queues_freq               [1;4]
% 23.62/3.50  --demod_completeness_check              fast
% 23.62/3.50  --demod_use_ground                      true
% 23.62/3.50  --sup_to_prop_solver                    passive
% 23.62/3.50  --sup_prop_simpl_new                    true
% 23.62/3.50  --sup_prop_simpl_given                  true
% 23.62/3.50  --sup_fun_splitting                     false
% 23.62/3.50  --sup_smt_interval                      50000
% 23.62/3.50  
% 23.62/3.50  ------ Superposition Simplification Setup
% 23.62/3.50  
% 23.62/3.50  --sup_indices_passive                   []
% 23.62/3.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.62/3.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.62/3.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.62/3.50  --sup_full_triv                         [TrivRules;PropSubs]
% 23.62/3.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.62/3.50  --sup_full_bw                           [BwDemod]
% 23.62/3.50  --sup_immed_triv                        [TrivRules]
% 23.62/3.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 23.62/3.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.62/3.50  --sup_immed_bw_main                     []
% 23.62/3.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 23.62/3.50  --sup_input_triv                        [Unflattening;TrivRules]
% 23.62/3.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.62/3.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 23.62/3.50  
% 23.62/3.50  ------ Combination Options
% 23.62/3.50  
% 23.62/3.50  --comb_res_mult                         3
% 23.62/3.50  --comb_sup_mult                         2
% 23.62/3.50  --comb_inst_mult                        10
% 23.62/3.50  
% 23.62/3.50  ------ Debug Options
% 23.62/3.50  
% 23.62/3.50  --dbg_backtrace                         false
% 23.62/3.50  --dbg_dump_prop_clauses                 false
% 23.62/3.50  --dbg_dump_prop_clauses_file            -
% 23.62/3.50  --dbg_out_stat                          false
% 23.62/3.50  
% 23.62/3.50  
% 23.62/3.50  
% 23.62/3.50  
% 23.62/3.50  ------ Proving...
% 23.62/3.50  
% 23.62/3.50  
% 23.62/3.50  % SZS status Theorem for theBenchmark.p
% 23.62/3.50  
% 23.62/3.50  % SZS output start CNFRefutation for theBenchmark.p
% 23.62/3.50  
% 23.62/3.50  fof(f4,axiom,(
% 23.62/3.50    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 23.62/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.62/3.50  
% 23.62/3.50  fof(f30,plain,(
% 23.62/3.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 23.62/3.50    inference(cnf_transformation,[],[f4])).
% 23.62/3.50  
% 23.62/3.50  fof(f5,axiom,(
% 23.62/3.50    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)),
% 23.62/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.62/3.50  
% 23.62/3.50  fof(f31,plain,(
% 23.62/3.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 23.62/3.50    inference(cnf_transformation,[],[f5])).
% 23.62/3.50  
% 23.62/3.50  fof(f45,plain,(
% 23.62/3.50    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0)) )),
% 23.62/3.50    inference(definition_unfolding,[],[f30,f31,f31])).
% 23.62/3.50  
% 23.62/3.50  fof(f10,conjecture,(
% 23.62/3.50    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 23.62/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.62/3.50  
% 23.62/3.50  fof(f11,negated_conjecture,(
% 23.62/3.50    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 23.62/3.50    inference(negated_conjecture,[],[f10])).
% 23.62/3.50  
% 23.62/3.50  fof(f19,plain,(
% 23.62/3.50    ? [X0,X1,X2] : ((~r1_tarski(X0,X1) & (v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 23.62/3.50    inference(ennf_transformation,[],[f11])).
% 23.62/3.50  
% 23.62/3.50  fof(f20,plain,(
% 23.62/3.50    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 23.62/3.50    inference(flattening,[],[f19])).
% 23.62/3.50  
% 23.62/3.50  fof(f23,plain,(
% 23.62/3.50    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_tarski(sK0,sK1) & v2_funct_1(sK2) & r1_tarski(sK0,k1_relat_1(sK2)) & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 23.62/3.50    introduced(choice_axiom,[])).
% 23.62/3.50  
% 23.62/3.50  fof(f24,plain,(
% 23.62/3.50    ~r1_tarski(sK0,sK1) & v2_funct_1(sK2) & r1_tarski(sK0,k1_relat_1(sK2)) & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 23.62/3.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f23])).
% 23.62/3.50  
% 23.62/3.50  fof(f36,plain,(
% 23.62/3.50    v1_relat_1(sK2)),
% 23.62/3.50    inference(cnf_transformation,[],[f24])).
% 23.62/3.50  
% 23.62/3.50  fof(f7,axiom,(
% 23.62/3.50    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (v2_funct_1(X2) => k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k3_xboole_0(X0,X1))))),
% 23.62/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.62/3.50  
% 23.62/3.50  fof(f13,plain,(
% 23.62/3.50    ! [X0,X1,X2] : ((k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k3_xboole_0(X0,X1)) | ~v2_funct_1(X2)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 23.62/3.50    inference(ennf_transformation,[],[f7])).
% 23.62/3.50  
% 23.62/3.50  fof(f14,plain,(
% 23.62/3.50    ! [X0,X1,X2] : (k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k3_xboole_0(X0,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 23.62/3.50    inference(flattening,[],[f13])).
% 23.62/3.50  
% 23.62/3.50  fof(f33,plain,(
% 23.62/3.50    ( ! [X2,X0,X1] : (k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k3_xboole_0(X0,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 23.62/3.50    inference(cnf_transformation,[],[f14])).
% 23.62/3.50  
% 23.62/3.50  fof(f6,axiom,(
% 23.62/3.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 23.62/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.62/3.50  
% 23.62/3.50  fof(f32,plain,(
% 23.62/3.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 23.62/3.50    inference(cnf_transformation,[],[f6])).
% 23.62/3.50  
% 23.62/3.50  fof(f42,plain,(
% 23.62/3.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 23.62/3.50    inference(definition_unfolding,[],[f32,f31])).
% 23.62/3.50  
% 23.62/3.50  fof(f46,plain,(
% 23.62/3.50    ( ! [X2,X0,X1] : (k1_setfam_1(k2_enumset1(k9_relat_1(X2,X0),k9_relat_1(X2,X0),k9_relat_1(X2,X0),k9_relat_1(X2,X1))) = k9_relat_1(X2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 23.62/3.50    inference(definition_unfolding,[],[f33,f42,f42])).
% 23.62/3.50  
% 23.62/3.50  fof(f37,plain,(
% 23.62/3.50    v1_funct_1(sK2)),
% 23.62/3.50    inference(cnf_transformation,[],[f24])).
% 23.62/3.50  
% 23.62/3.50  fof(f40,plain,(
% 23.62/3.50    v2_funct_1(sK2)),
% 23.62/3.50    inference(cnf_transformation,[],[f24])).
% 23.62/3.50  
% 23.62/3.50  fof(f38,plain,(
% 23.62/3.50    r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),
% 23.62/3.50    inference(cnf_transformation,[],[f24])).
% 23.62/3.50  
% 23.62/3.50  fof(f3,axiom,(
% 23.62/3.50    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 23.62/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.62/3.50  
% 23.62/3.50  fof(f12,plain,(
% 23.62/3.50    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 23.62/3.50    inference(ennf_transformation,[],[f3])).
% 23.62/3.50  
% 23.62/3.50  fof(f29,plain,(
% 23.62/3.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 23.62/3.50    inference(cnf_transformation,[],[f12])).
% 23.62/3.50  
% 23.62/3.50  fof(f44,plain,(
% 23.62/3.50    ( ! [X0,X1] : (k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 23.62/3.50    inference(definition_unfolding,[],[f29,f42])).
% 23.62/3.50  
% 23.62/3.50  fof(f9,axiom,(
% 23.62/3.50    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)))),
% 23.62/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.62/3.50  
% 23.62/3.50  fof(f17,plain,(
% 23.62/3.50    ! [X0,X1] : ((r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 23.62/3.50    inference(ennf_transformation,[],[f9])).
% 23.62/3.50  
% 23.62/3.50  fof(f18,plain,(
% 23.62/3.50    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 23.62/3.50    inference(flattening,[],[f17])).
% 23.62/3.50  
% 23.62/3.50  fof(f35,plain,(
% 23.62/3.50    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 23.62/3.50    inference(cnf_transformation,[],[f18])).
% 23.62/3.50  
% 23.62/3.50  fof(f39,plain,(
% 23.62/3.50    r1_tarski(sK0,k1_relat_1(sK2))),
% 23.62/3.50    inference(cnf_transformation,[],[f24])).
% 23.62/3.50  
% 23.62/3.50  fof(f8,axiom,(
% 23.62/3.50    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 23.62/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.62/3.50  
% 23.62/3.50  fof(f15,plain,(
% 23.62/3.50    ! [X0,X1] : ((r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 23.62/3.50    inference(ennf_transformation,[],[f8])).
% 23.62/3.50  
% 23.62/3.50  fof(f16,plain,(
% 23.62/3.50    ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 23.62/3.50    inference(flattening,[],[f15])).
% 23.62/3.50  
% 23.62/3.50  fof(f34,plain,(
% 23.62/3.50    ( ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 23.62/3.50    inference(cnf_transformation,[],[f16])).
% 23.62/3.50  
% 23.62/3.50  fof(f2,axiom,(
% 23.62/3.50    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 23.62/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.62/3.50  
% 23.62/3.50  fof(f28,plain,(
% 23.62/3.50    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 23.62/3.50    inference(cnf_transformation,[],[f2])).
% 23.62/3.50  
% 23.62/3.50  fof(f43,plain,(
% 23.62/3.50    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0)) )),
% 23.62/3.50    inference(definition_unfolding,[],[f28,f42])).
% 23.62/3.50  
% 23.62/3.50  fof(f1,axiom,(
% 23.62/3.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 23.62/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.62/3.50  
% 23.62/3.50  fof(f21,plain,(
% 23.62/3.50    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 23.62/3.50    inference(nnf_transformation,[],[f1])).
% 23.62/3.50  
% 23.62/3.50  fof(f22,plain,(
% 23.62/3.50    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 23.62/3.50    inference(flattening,[],[f21])).
% 23.62/3.50  
% 23.62/3.50  fof(f27,plain,(
% 23.62/3.50    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 23.62/3.50    inference(cnf_transformation,[],[f22])).
% 23.62/3.50  
% 23.62/3.50  fof(f25,plain,(
% 23.62/3.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 23.62/3.50    inference(cnf_transformation,[],[f22])).
% 23.62/3.50  
% 23.62/3.50  fof(f48,plain,(
% 23.62/3.50    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 23.62/3.50    inference(equality_resolution,[],[f25])).
% 23.62/3.50  
% 23.62/3.50  fof(f41,plain,(
% 23.62/3.50    ~r1_tarski(sK0,sK1)),
% 23.62/3.50    inference(cnf_transformation,[],[f24])).
% 23.62/3.50  
% 23.62/3.50  cnf(c_5,plain,
% 23.62/3.50      ( k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
% 23.62/3.50      inference(cnf_transformation,[],[f45]) ).
% 23.62/3.50  
% 23.62/3.50  cnf(c_14,negated_conjecture,
% 23.62/3.50      ( v1_relat_1(sK2) ),
% 23.62/3.50      inference(cnf_transformation,[],[f36]) ).
% 23.62/3.50  
% 23.62/3.50  cnf(c_430,plain,
% 23.62/3.50      ( v1_relat_1(sK2) = iProver_top ),
% 23.62/3.50      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 23.62/3.50  
% 23.62/3.50  cnf(c_6,plain,
% 23.62/3.50      ( ~ v1_relat_1(X0)
% 23.62/3.50      | ~ v1_funct_1(X0)
% 23.62/3.50      | ~ v2_funct_1(X0)
% 23.62/3.50      | k1_setfam_1(k2_enumset1(k9_relat_1(X0,X1),k9_relat_1(X0,X1),k9_relat_1(X0,X1),k9_relat_1(X0,X2))) = k9_relat_1(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) ),
% 23.62/3.50      inference(cnf_transformation,[],[f46]) ).
% 23.62/3.50  
% 23.62/3.50  cnf(c_438,plain,
% 23.62/3.50      ( k1_setfam_1(k2_enumset1(k9_relat_1(X0,X1),k9_relat_1(X0,X1),k9_relat_1(X0,X1),k9_relat_1(X0,X2))) = k9_relat_1(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))
% 23.62/3.50      | v1_relat_1(X0) != iProver_top
% 23.62/3.50      | v1_funct_1(X0) != iProver_top
% 23.62/3.50      | v2_funct_1(X0) != iProver_top ),
% 23.62/3.50      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 23.62/3.50  
% 23.62/3.50  cnf(c_1265,plain,
% 23.62/3.50      ( k1_setfam_1(k2_enumset1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X0),k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) = k9_relat_1(sK2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))
% 23.62/3.50      | v1_funct_1(sK2) != iProver_top
% 23.62/3.50      | v2_funct_1(sK2) != iProver_top ),
% 23.62/3.50      inference(superposition,[status(thm)],[c_430,c_438]) ).
% 23.62/3.50  
% 23.62/3.50  cnf(c_13,negated_conjecture,
% 23.62/3.50      ( v1_funct_1(sK2) ),
% 23.62/3.50      inference(cnf_transformation,[],[f37]) ).
% 23.62/3.50  
% 23.62/3.50  cnf(c_16,plain,
% 23.62/3.50      ( v1_funct_1(sK2) = iProver_top ),
% 23.62/3.50      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 23.62/3.50  
% 23.62/3.50  cnf(c_10,negated_conjecture,
% 23.62/3.50      ( v2_funct_1(sK2) ),
% 23.62/3.50      inference(cnf_transformation,[],[f40]) ).
% 23.62/3.50  
% 23.62/3.50  cnf(c_19,plain,
% 23.62/3.50      ( v2_funct_1(sK2) = iProver_top ),
% 23.62/3.50      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 23.62/3.50  
% 23.62/3.50  cnf(c_3083,plain,
% 23.62/3.50      ( k1_setfam_1(k2_enumset1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X0),k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) = k9_relat_1(sK2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) ),
% 23.62/3.50      inference(global_propositional_subsumption,
% 23.62/3.50                [status(thm)],
% 23.62/3.50                [c_1265,c_16,c_19]) ).
% 23.62/3.50  
% 23.62/3.50  cnf(c_3089,plain,
% 23.62/3.50      ( k1_setfam_1(k2_enumset1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X0),k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) = k9_relat_1(sK2,k1_setfam_1(k2_enumset1(X1,X1,X1,X0))) ),
% 23.62/3.50      inference(superposition,[status(thm)],[c_5,c_3083]) ).
% 23.62/3.50  
% 23.62/3.50  cnf(c_12,negated_conjecture,
% 23.62/3.50      ( r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
% 23.62/3.50      inference(cnf_transformation,[],[f38]) ).
% 23.62/3.50  
% 23.62/3.50  cnf(c_432,plain,
% 23.62/3.50      ( r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) = iProver_top ),
% 23.62/3.50      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 23.62/3.50  
% 23.62/3.50  cnf(c_4,plain,
% 23.62/3.50      ( ~ r1_tarski(X0,X1) | k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = X0 ),
% 23.62/3.50      inference(cnf_transformation,[],[f44]) ).
% 23.62/3.50  
% 23.62/3.50  cnf(c_439,plain,
% 23.62/3.50      ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = X0
% 23.62/3.50      | r1_tarski(X0,X1) != iProver_top ),
% 23.62/3.50      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 23.62/3.50  
% 23.62/3.50  cnf(c_944,plain,
% 23.62/3.50      ( k1_setfam_1(k2_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) = k9_relat_1(sK2,sK0) ),
% 23.62/3.50      inference(superposition,[status(thm)],[c_432,c_439]) ).
% 23.62/3.50  
% 23.62/3.50  cnf(c_3410,plain,
% 23.62/3.50      ( k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK0))) = k9_relat_1(sK2,sK0) ),
% 23.62/3.50      inference(superposition,[status(thm)],[c_3089,c_944]) ).
% 23.62/3.50  
% 23.62/3.50  cnf(c_8,plain,
% 23.62/3.50      ( r1_tarski(k10_relat_1(X0,k9_relat_1(X0,X1)),X1)
% 23.62/3.50      | ~ v1_relat_1(X0)
% 23.62/3.50      | ~ v1_funct_1(X0)
% 23.62/3.50      | ~ v2_funct_1(X0) ),
% 23.62/3.50      inference(cnf_transformation,[],[f35]) ).
% 23.62/3.50  
% 23.62/3.50  cnf(c_436,plain,
% 23.62/3.50      ( r1_tarski(k10_relat_1(X0,k9_relat_1(X0,X1)),X1) = iProver_top
% 23.62/3.50      | v1_relat_1(X0) != iProver_top
% 23.62/3.50      | v1_funct_1(X0) != iProver_top
% 23.62/3.50      | v2_funct_1(X0) != iProver_top ),
% 23.62/3.50      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 23.62/3.50  
% 23.62/3.50  cnf(c_942,plain,
% 23.62/3.50      ( k1_setfam_1(k2_enumset1(k10_relat_1(X0,k9_relat_1(X0,X1)),k10_relat_1(X0,k9_relat_1(X0,X1)),k10_relat_1(X0,k9_relat_1(X0,X1)),X1)) = k10_relat_1(X0,k9_relat_1(X0,X1))
% 23.62/3.50      | v1_relat_1(X0) != iProver_top
% 23.62/3.50      | v1_funct_1(X0) != iProver_top
% 23.62/3.50      | v2_funct_1(X0) != iProver_top ),
% 23.62/3.50      inference(superposition,[status(thm)],[c_436,c_439]) ).
% 23.62/3.50  
% 23.62/3.50  cnf(c_1274,plain,
% 23.62/3.50      ( k1_setfam_1(k2_enumset1(k10_relat_1(sK2,k9_relat_1(sK2,X0)),k10_relat_1(sK2,k9_relat_1(sK2,X0)),k10_relat_1(sK2,k9_relat_1(sK2,X0)),X0)) = k10_relat_1(sK2,k9_relat_1(sK2,X0))
% 23.62/3.50      | v1_funct_1(sK2) != iProver_top
% 23.62/3.50      | v2_funct_1(sK2) != iProver_top ),
% 23.62/3.50      inference(superposition,[status(thm)],[c_430,c_942]) ).
% 23.62/3.50  
% 23.62/3.50  cnf(c_4192,plain,
% 23.62/3.50      ( k1_setfam_1(k2_enumset1(k10_relat_1(sK2,k9_relat_1(sK2,X0)),k10_relat_1(sK2,k9_relat_1(sK2,X0)),k10_relat_1(sK2,k9_relat_1(sK2,X0)),X0)) = k10_relat_1(sK2,k9_relat_1(sK2,X0)) ),
% 23.62/3.50      inference(global_propositional_subsumption,
% 23.62/3.50                [status(thm)],
% 23.62/3.50                [c_1274,c_16,c_19]) ).
% 23.62/3.50  
% 23.62/3.50  cnf(c_4204,plain,
% 23.62/3.50      ( k1_setfam_1(k2_enumset1(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),k10_relat_1(sK2,k9_relat_1(sK2,sK0)),k10_relat_1(sK2,k9_relat_1(sK2,sK0)),k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK0)))) = k10_relat_1(sK2,k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK0)))) ),
% 23.62/3.50      inference(superposition,[status(thm)],[c_3410,c_4192]) ).
% 23.62/3.50  
% 23.62/3.50  cnf(c_11,negated_conjecture,
% 23.62/3.50      ( r1_tarski(sK0,k1_relat_1(sK2)) ),
% 23.62/3.50      inference(cnf_transformation,[],[f39]) ).
% 23.62/3.50  
% 23.62/3.50  cnf(c_433,plain,
% 23.62/3.50      ( r1_tarski(sK0,k1_relat_1(sK2)) = iProver_top ),
% 23.62/3.50      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 23.62/3.50  
% 23.62/3.50  cnf(c_7,plain,
% 23.62/3.50      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
% 23.62/3.50      | ~ r1_tarski(X0,k1_relat_1(X1))
% 23.62/3.50      | ~ v1_relat_1(X1) ),
% 23.62/3.50      inference(cnf_transformation,[],[f34]) ).
% 23.62/3.50  
% 23.62/3.50  cnf(c_437,plain,
% 23.62/3.50      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) = iProver_top
% 23.62/3.50      | r1_tarski(X0,k1_relat_1(X1)) != iProver_top
% 23.62/3.50      | v1_relat_1(X1) != iProver_top ),
% 23.62/3.50      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 23.62/3.50  
% 23.62/3.50  cnf(c_1118,plain,
% 23.62/3.50      ( k1_setfam_1(k2_enumset1(X0,X0,X0,k10_relat_1(X1,k9_relat_1(X1,X0)))) = X0
% 23.62/3.50      | r1_tarski(X0,k1_relat_1(X1)) != iProver_top
% 23.62/3.50      | v1_relat_1(X1) != iProver_top ),
% 23.62/3.50      inference(superposition,[status(thm)],[c_437,c_439]) ).
% 23.62/3.50  
% 23.62/3.50  cnf(c_2272,plain,
% 23.62/3.50      ( k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK0)))) = sK0
% 23.62/3.50      | v1_relat_1(sK2) != iProver_top ),
% 23.62/3.50      inference(superposition,[status(thm)],[c_433,c_1118]) ).
% 23.62/3.50  
% 23.62/3.50  cnf(c_570,plain,
% 23.62/3.50      ( r1_tarski(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK0)))
% 23.62/3.50      | ~ r1_tarski(sK0,k1_relat_1(sK2))
% 23.62/3.50      | ~ v1_relat_1(sK2) ),
% 23.62/3.50      inference(instantiation,[status(thm)],[c_7]) ).
% 23.62/3.50  
% 23.62/3.50  cnf(c_757,plain,
% 23.62/3.50      ( ~ r1_tarski(sK0,X0)
% 23.62/3.50      | k1_setfam_1(k2_enumset1(sK0,sK0,sK0,X0)) = sK0 ),
% 23.62/3.50      inference(instantiation,[status(thm)],[c_4]) ).
% 23.62/3.50  
% 23.62/3.50  cnf(c_1030,plain,
% 23.62/3.50      ( ~ r1_tarski(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK0)))
% 23.62/3.50      | k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK0)))) = sK0 ),
% 23.62/3.50      inference(instantiation,[status(thm)],[c_757]) ).
% 23.62/3.50  
% 23.62/3.50  cnf(c_2465,plain,
% 23.62/3.50      ( k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK0)))) = sK0 ),
% 23.62/3.50      inference(global_propositional_subsumption,
% 23.62/3.50                [status(thm)],
% 23.62/3.50                [c_2272,c_14,c_11,c_570,c_1030]) ).
% 23.62/3.50  
% 23.62/3.50  cnf(c_3,plain,
% 23.62/3.50      ( r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0) ),
% 23.62/3.50      inference(cnf_transformation,[],[f43]) ).
% 23.62/3.50  
% 23.62/3.50  cnf(c_440,plain,
% 23.62/3.50      ( r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0) = iProver_top ),
% 23.62/3.50      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 23.62/3.50  
% 23.62/3.50  cnf(c_809,plain,
% 23.62/3.50      ( r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X1) = iProver_top ),
% 23.62/3.50      inference(superposition,[status(thm)],[c_5,c_440]) ).
% 23.62/3.50  
% 23.62/3.50  cnf(c_0,plain,
% 23.62/3.50      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 23.62/3.50      inference(cnf_transformation,[],[f27]) ).
% 23.62/3.50  
% 23.62/3.50  cnf(c_442,plain,
% 23.62/3.50      ( X0 = X1
% 23.62/3.50      | r1_tarski(X0,X1) != iProver_top
% 23.62/3.50      | r1_tarski(X1,X0) != iProver_top ),
% 23.62/3.50      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 23.62/3.50  
% 23.62/3.50  cnf(c_1079,plain,
% 23.62/3.50      ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = X1
% 23.62/3.50      | r1_tarski(X1,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) != iProver_top ),
% 23.62/3.50      inference(superposition,[status(thm)],[c_809,c_442]) ).
% 23.62/3.50  
% 23.62/3.50  cnf(c_1975,plain,
% 23.62/3.50      ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = X1
% 23.62/3.50      | r1_tarski(X1,k1_setfam_1(k2_enumset1(X1,X1,X1,X0))) != iProver_top ),
% 23.62/3.50      inference(superposition,[status(thm)],[c_5,c_1079]) ).
% 23.62/3.50  
% 23.62/3.50  cnf(c_2472,plain,
% 23.62/3.50      ( k1_setfam_1(k2_enumset1(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),k10_relat_1(sK2,k9_relat_1(sK2,sK0)),k10_relat_1(sK2,k9_relat_1(sK2,sK0)),sK0)) = sK0
% 23.62/3.50      | r1_tarski(sK0,sK0) != iProver_top ),
% 23.62/3.50      inference(superposition,[status(thm)],[c_2465,c_1975]) ).
% 23.62/3.50  
% 23.62/3.50  cnf(c_2,plain,
% 23.62/3.50      ( r1_tarski(X0,X0) ),
% 23.62/3.50      inference(cnf_transformation,[],[f48]) ).
% 23.62/3.50  
% 23.62/3.50  cnf(c_998,plain,
% 23.62/3.50      ( r1_tarski(sK0,sK0) ),
% 23.62/3.50      inference(instantiation,[status(thm)],[c_2]) ).
% 23.62/3.50  
% 23.62/3.50  cnf(c_1003,plain,
% 23.62/3.50      ( r1_tarski(sK0,sK0) = iProver_top ),
% 23.62/3.50      inference(predicate_to_equality,[status(thm)],[c_998]) ).
% 23.62/3.50  
% 23.62/3.50  cnf(c_3071,plain,
% 23.62/3.50      ( k1_setfam_1(k2_enumset1(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),k10_relat_1(sK2,k9_relat_1(sK2,sK0)),k10_relat_1(sK2,k9_relat_1(sK2,sK0)),sK0)) = sK0 ),
% 23.62/3.50      inference(global_propositional_subsumption,
% 23.62/3.50                [status(thm)],
% 23.62/3.50                [c_2472,c_1003]) ).
% 23.62/3.50  
% 23.62/3.50  cnf(c_4214,plain,
% 23.62/3.50      ( k10_relat_1(sK2,k9_relat_1(sK2,sK0)) = sK0 ),
% 23.62/3.50      inference(superposition,[status(thm)],[c_4192,c_3071]) ).
% 23.62/3.50  
% 23.62/3.50  cnf(c_4236,plain,
% 23.62/3.50      ( k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK0)))) = k10_relat_1(sK2,k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK0)))) ),
% 23.62/3.50      inference(light_normalisation,[status(thm)],[c_4204,c_4214]) ).
% 23.62/3.50  
% 23.62/3.50  cnf(c_4238,plain,
% 23.62/3.50      ( k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK0)))) = k10_relat_1(sK2,k9_relat_1(sK2,sK0)) ),
% 23.62/3.50      inference(light_normalisation,[status(thm)],[c_4236,c_3410]) ).
% 23.62/3.50  
% 23.62/3.50  cnf(c_79684,plain,
% 23.62/3.50      ( k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK0)))) = sK0 ),
% 23.62/3.50      inference(light_normalisation,[status(thm)],[c_4238,c_4214]) ).
% 23.62/3.50  
% 23.62/3.50  cnf(c_941,plain,
% 23.62/3.50      ( k1_setfam_1(k2_enumset1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0)) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
% 23.62/3.50      inference(superposition,[status(thm)],[c_440,c_439]) ).
% 23.62/3.50  
% 23.62/3.50  cnf(c_6069,plain,
% 23.62/3.50      ( k1_setfam_1(k2_enumset1(X0,X0,X0,k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
% 23.62/3.50      inference(superposition,[status(thm)],[c_5,c_941]) ).
% 23.62/3.50  
% 23.62/3.50  cnf(c_6377,plain,
% 23.62/3.50      ( k1_setfam_1(k2_enumset1(X0,X0,X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X0)))) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
% 23.62/3.50      inference(superposition,[status(thm)],[c_5,c_6069]) ).
% 23.62/3.50  
% 23.62/3.50  cnf(c_79884,plain,
% 23.62/3.50      ( k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)) = sK0 ),
% 23.62/3.50      inference(superposition,[status(thm)],[c_79684,c_6377]) ).
% 23.62/3.50  
% 23.62/3.50  cnf(c_81807,plain,
% 23.62/3.50      ( r1_tarski(sK0,sK1) = iProver_top ),
% 23.62/3.50      inference(superposition,[status(thm)],[c_79884,c_809]) ).
% 23.62/3.50  
% 23.62/3.50  cnf(c_9,negated_conjecture,
% 23.62/3.50      ( ~ r1_tarski(sK0,sK1) ),
% 23.62/3.50      inference(cnf_transformation,[],[f41]) ).
% 23.62/3.50  
% 23.62/3.50  cnf(c_20,plain,
% 23.62/3.50      ( r1_tarski(sK0,sK1) != iProver_top ),
% 23.62/3.50      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 23.62/3.50  
% 23.62/3.50  cnf(contradiction,plain,
% 23.62/3.50      ( $false ),
% 23.62/3.50      inference(minisat,[status(thm)],[c_81807,c_20]) ).
% 23.62/3.50  
% 23.62/3.50  
% 23.62/3.50  % SZS output end CNFRefutation for theBenchmark.p
% 23.62/3.50  
% 23.62/3.50  ------                               Statistics
% 23.62/3.50  
% 23.62/3.50  ------ Selected
% 23.62/3.50  
% 23.62/3.50  total_time:                             2.894
% 23.62/3.50  
%------------------------------------------------------------------------------
