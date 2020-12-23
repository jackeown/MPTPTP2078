%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:47:45 EST 2020

% Result     : Theorem 19.30s
% Output     : CNFRefutation 19.30s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 275 expanded)
%              Number of clauses        :   55 (  65 expanded)
%              Number of leaves         :   20 (  73 expanded)
%              Depth                    :   16
%              Number of atoms          :  208 ( 439 expanded)
%              Number of equality atoms :  104 ( 252 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f13,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f7,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f12])).

fof(f45,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f39,f40])).

fof(f46,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f38,f45])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f37,f46])).

fof(f48,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f36,f47])).

fof(f49,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f35,f48])).

fof(f50,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f41,f49])).

fof(f51,plain,(
    ! [X0,X1] : k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)) ),
    inference(definition_unfolding,[],[f27,f50,f50])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f52,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f33,f50])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k2_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k2_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k2_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k10_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => r1_tarski(k10_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k10_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f25,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k10_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ~ r1_tarski(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f25])).

fof(f43,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f34,f50])).

fof(f44,plain,(
    ~ r1_tarski(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f26])).

fof(f54,plain,(
    ~ r1_tarski(k10_relat_1(sK2,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k1_setfam_1(k6_enumset1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))) ),
    inference(definition_unfolding,[],[f44,f50,f50])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

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

fof(f56,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f28])).

fof(f30,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_4,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_454,plain,
    ( r1_tarski(k10_relat_1(sK2,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k10_relat_1(sK2,sK0))
    | ~ r1_tarski(k2_xboole_0(k10_relat_1(sK2,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),X0),k10_relat_1(sK2,sK0)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_54076,plain,
    ( r1_tarski(k10_relat_1(sK2,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k10_relat_1(sK2,sK0))
    | ~ r1_tarski(k2_xboole_0(k10_relat_1(sK2,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k10_relat_1(sK2,X0)),k10_relat_1(sK2,sK0)) ),
    inference(instantiation,[status(thm)],[c_454])).

cnf(c_54078,plain,
    ( r1_tarski(k10_relat_1(sK2,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k10_relat_1(sK2,sK0))
    | ~ r1_tarski(k2_xboole_0(k10_relat_1(sK2,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k10_relat_1(sK2,sK0)),k10_relat_1(sK2,sK0)) ),
    inference(instantiation,[status(thm)],[c_54076])).

cnf(c_0,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_6,plain,
    ( r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_313,plain,
    ( r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_426,plain,
    ( r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_313])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_314,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_667,plain,
    ( k2_xboole_0(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X1) = X1 ),
    inference(superposition,[status(thm)],[c_426,c_314])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | k2_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k10_relat_1(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_10,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_114,plain,
    ( k2_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k10_relat_1(X0,k2_xboole_0(X1,X2))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_10])).

cnf(c_115,plain,
    ( k2_xboole_0(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) = k10_relat_1(sK2,k2_xboole_0(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_114])).

cnf(c_315,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(k2_xboole_0(X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_518,plain,
    ( r1_tarski(k10_relat_1(sK2,X0),X1) = iProver_top
    | r1_tarski(k10_relat_1(sK2,k2_xboole_0(X0,X2)),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_115,c_315])).

cnf(c_1842,plain,
    ( r1_tarski(k10_relat_1(sK2,X0),X1) != iProver_top
    | r1_tarski(k10_relat_1(sK2,k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X0))),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_667,c_518])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_312,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_9,negated_conjecture,
    ( ~ r1_tarski(k10_relat_1(sK2,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k1_setfam_1(k6_enumset1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_311,plain,
    ( r1_tarski(k10_relat_1(sK2,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k1_setfam_1(k6_enumset1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_849,plain,
    ( r1_tarski(k10_relat_1(sK2,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k10_relat_1(sK2,sK1)) != iProver_top
    | r1_tarski(k10_relat_1(sK2,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k10_relat_1(sK2,sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_312,c_311])).

cnf(c_34460,plain,
    ( r1_tarski(k10_relat_1(sK2,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k10_relat_1(sK2,sK0)) != iProver_top
    | r1_tarski(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1842,c_849])).

cnf(c_34486,plain,
    ( ~ r1_tarski(k10_relat_1(sK2,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k10_relat_1(sK2,sK0))
    | ~ r1_tarski(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK1)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_34460])).

cnf(c_175,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_24877,plain,
    ( X0 != X1
    | X0 = k2_xboole_0(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),X2)
    | k2_xboole_0(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),X2) != X1 ),
    inference(instantiation,[status(thm)],[c_175])).

cnf(c_24878,plain,
    ( k2_xboole_0(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK0) != sK0
    | sK0 = k2_xboole_0(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK0)
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_24877])).

cnf(c_23973,plain,
    ( ~ r1_tarski(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),X0)
    | k2_xboole_0(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),X0) = X0 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_23975,plain,
    ( ~ r1_tarski(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK0)
    | k2_xboole_0(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK0) = sK0 ),
    inference(instantiation,[status(thm)],[c_23973])).

cnf(c_178,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_353,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_xboole_0(X2,X3),X4)
    | X4 != X1
    | k2_xboole_0(X2,X3) != X0 ),
    inference(instantiation,[status(thm)],[c_178])).

cnf(c_492,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_xboole_0(k10_relat_1(sK2,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),X2),k10_relat_1(sK2,sK0))
    | k10_relat_1(sK2,sK0) != X1
    | k2_xboole_0(k10_relat_1(sK2,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),X2) != X0 ),
    inference(instantiation,[status(thm)],[c_353])).

cnf(c_1753,plain,
    ( ~ r1_tarski(X0,k10_relat_1(sK2,X1))
    | r1_tarski(k2_xboole_0(k10_relat_1(sK2,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),X2),k10_relat_1(sK2,sK0))
    | k10_relat_1(sK2,sK0) != k10_relat_1(sK2,X1)
    | k2_xboole_0(k10_relat_1(sK2,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),X2) != X0 ),
    inference(instantiation,[status(thm)],[c_492])).

cnf(c_4000,plain,
    ( ~ r1_tarski(k10_relat_1(sK2,k2_xboole_0(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),X0)),k10_relat_1(sK2,X1))
    | r1_tarski(k2_xboole_0(k10_relat_1(sK2,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k10_relat_1(sK2,X0)),k10_relat_1(sK2,sK0))
    | k10_relat_1(sK2,sK0) != k10_relat_1(sK2,X1)
    | k2_xboole_0(k10_relat_1(sK2,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k10_relat_1(sK2,X0)) != k10_relat_1(sK2,k2_xboole_0(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),X0)) ),
    inference(instantiation,[status(thm)],[c_1753])).

cnf(c_23927,plain,
    ( ~ r1_tarski(k10_relat_1(sK2,k2_xboole_0(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),X0)),k10_relat_1(sK2,k2_xboole_0(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),X0)))
    | r1_tarski(k2_xboole_0(k10_relat_1(sK2,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k10_relat_1(sK2,X0)),k10_relat_1(sK2,sK0))
    | k10_relat_1(sK2,sK0) != k10_relat_1(sK2,k2_xboole_0(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),X0))
    | k2_xboole_0(k10_relat_1(sK2,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k10_relat_1(sK2,X0)) != k10_relat_1(sK2,k2_xboole_0(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),X0)) ),
    inference(instantiation,[status(thm)],[c_4000])).

cnf(c_23929,plain,
    ( ~ r1_tarski(k10_relat_1(sK2,k2_xboole_0(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK0)),k10_relat_1(sK2,k2_xboole_0(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK0)))
    | r1_tarski(k2_xboole_0(k10_relat_1(sK2,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k10_relat_1(sK2,sK0)),k10_relat_1(sK2,sK0))
    | k10_relat_1(sK2,sK0) != k10_relat_1(sK2,k2_xboole_0(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK0))
    | k2_xboole_0(k10_relat_1(sK2,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k10_relat_1(sK2,sK0)) != k10_relat_1(sK2,k2_xboole_0(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK0)) ),
    inference(instantiation,[status(thm)],[c_23927])).

cnf(c_3,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_7302,plain,
    ( r1_tarski(k10_relat_1(sK2,X0),k10_relat_1(sK2,X0)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_18393,plain,
    ( r1_tarski(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK1)) ),
    inference(instantiation,[status(thm)],[c_7302])).

cnf(c_18006,plain,
    ( r1_tarski(k10_relat_1(sK2,k2_xboole_0(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),X0)),k10_relat_1(sK2,k2_xboole_0(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),X0))) ),
    inference(instantiation,[status(thm)],[c_7302])).

cnf(c_18012,plain,
    ( r1_tarski(k10_relat_1(sK2,k2_xboole_0(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK0)),k10_relat_1(sK2,k2_xboole_0(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK0))) ),
    inference(instantiation,[status(thm)],[c_18006])).

cnf(c_180,plain,
    ( X0 != X1
    | X2 != X3
    | k10_relat_1(X0,X2) = k10_relat_1(X1,X3) ),
    theory(equality)).

cnf(c_3287,plain,
    ( X0 != k2_xboole_0(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),X1)
    | X2 != sK2
    | k10_relat_1(X2,X0) = k10_relat_1(sK2,k2_xboole_0(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),X1)) ),
    inference(instantiation,[status(thm)],[c_180])).

cnf(c_9901,plain,
    ( X0 != k2_xboole_0(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),X1)
    | k10_relat_1(sK2,X0) = k10_relat_1(sK2,k2_xboole_0(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),X1))
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_3287])).

cnf(c_9902,plain,
    ( k10_relat_1(sK2,sK0) = k10_relat_1(sK2,k2_xboole_0(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK0))
    | sK0 != k2_xboole_0(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK0)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_9901])).

cnf(c_1908,plain,
    ( r1_tarski(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK0) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1074,plain,
    ( k2_xboole_0(k10_relat_1(sK2,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k10_relat_1(sK2,X0)) = k10_relat_1(sK2,k2_xboole_0(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),X0)) ),
    inference(instantiation,[status(thm)],[c_115])).

cnf(c_1079,plain,
    ( k2_xboole_0(k10_relat_1(sK2,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k10_relat_1(sK2,sK0)) = k10_relat_1(sK2,k2_xboole_0(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK0)) ),
    inference(instantiation,[status(thm)],[c_1074])).

cnf(c_174,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_627,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_174])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_33,plain,
    ( ~ r1_tarski(sK0,sK0)
    | sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_29,plain,
    ( r1_tarski(sK0,sK0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_54078,c_34486,c_24878,c_23975,c_23929,c_18393,c_18012,c_9902,c_1908,c_1079,c_627,c_33,c_29])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:01:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 19.30/2.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.30/2.98  
% 19.30/2.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 19.30/2.98  
% 19.30/2.98  ------  iProver source info
% 19.30/2.98  
% 19.30/2.98  git: date: 2020-06-30 10:37:57 +0100
% 19.30/2.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 19.30/2.98  git: non_committed_changes: false
% 19.30/2.98  git: last_make_outside_of_git: false
% 19.30/2.98  
% 19.30/2.98  ------ 
% 19.30/2.98  ------ Parsing...
% 19.30/2.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 19.30/2.98  
% 19.30/2.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 19.30/2.98  
% 19.30/2.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 19.30/2.98  
% 19.30/2.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.30/2.98  ------ Proving...
% 19.30/2.98  ------ Problem Properties 
% 19.30/2.98  
% 19.30/2.98  
% 19.30/2.98  clauses                                 9
% 19.30/2.98  conjectures                             1
% 19.30/2.98  EPR                                     2
% 19.30/2.98  Horn                                    9
% 19.30/2.98  unary                                   5
% 19.30/2.98  binary                                  2
% 19.30/2.98  lits                                    15
% 19.30/2.98  lits eq                                 4
% 19.30/2.98  fd_pure                                 0
% 19.30/2.98  fd_pseudo                               0
% 19.30/2.98  fd_cond                                 0
% 19.30/2.98  fd_pseudo_cond                          1
% 19.30/2.98  AC symbols                              0
% 19.30/2.98  
% 19.30/2.98  ------ Input Options Time Limit: Unbounded
% 19.30/2.98  
% 19.30/2.98  
% 19.30/2.98  ------ 
% 19.30/2.98  Current options:
% 19.30/2.98  ------ 
% 19.30/2.98  
% 19.30/2.98  
% 19.30/2.98  
% 19.30/2.98  
% 19.30/2.98  ------ Proving...
% 19.30/2.98  
% 19.30/2.98  
% 19.30/2.98  % SZS status Theorem for theBenchmark.p
% 19.30/2.98  
% 19.30/2.98  % SZS output start CNFRefutation for theBenchmark.p
% 19.30/2.98  
% 19.30/2.98  fof(f3,axiom,(
% 19.30/2.98    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 19.30/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.30/2.98  
% 19.30/2.98  fof(f17,plain,(
% 19.30/2.98    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 19.30/2.98    inference(ennf_transformation,[],[f3])).
% 19.30/2.98  
% 19.30/2.98  fof(f31,plain,(
% 19.30/2.98    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 19.30/2.98    inference(cnf_transformation,[],[f17])).
% 19.30/2.98  
% 19.30/2.98  fof(f1,axiom,(
% 19.30/2.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 19.30/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.30/2.98  
% 19.30/2.98  fof(f27,plain,(
% 19.30/2.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 19.30/2.98    inference(cnf_transformation,[],[f1])).
% 19.30/2.98  
% 19.30/2.98  fof(f13,axiom,(
% 19.30/2.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 19.30/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.30/2.98  
% 19.30/2.98  fof(f41,plain,(
% 19.30/2.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 19.30/2.98    inference(cnf_transformation,[],[f13])).
% 19.30/2.98  
% 19.30/2.98  fof(f7,axiom,(
% 19.30/2.98    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 19.30/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.30/2.98  
% 19.30/2.98  fof(f35,plain,(
% 19.30/2.98    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 19.30/2.98    inference(cnf_transformation,[],[f7])).
% 19.30/2.98  
% 19.30/2.98  fof(f8,axiom,(
% 19.30/2.98    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 19.30/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.30/2.98  
% 19.30/2.98  fof(f36,plain,(
% 19.30/2.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 19.30/2.98    inference(cnf_transformation,[],[f8])).
% 19.30/2.98  
% 19.30/2.98  fof(f9,axiom,(
% 19.30/2.98    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 19.30/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.30/2.98  
% 19.30/2.98  fof(f37,plain,(
% 19.30/2.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 19.30/2.98    inference(cnf_transformation,[],[f9])).
% 19.30/2.98  
% 19.30/2.98  fof(f10,axiom,(
% 19.30/2.98    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 19.30/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.30/2.98  
% 19.30/2.98  fof(f38,plain,(
% 19.30/2.98    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 19.30/2.98    inference(cnf_transformation,[],[f10])).
% 19.30/2.98  
% 19.30/2.98  fof(f11,axiom,(
% 19.30/2.98    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 19.30/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.30/2.98  
% 19.30/2.98  fof(f39,plain,(
% 19.30/2.98    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 19.30/2.98    inference(cnf_transformation,[],[f11])).
% 19.30/2.98  
% 19.30/2.98  fof(f12,axiom,(
% 19.30/2.98    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 19.30/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.30/2.98  
% 19.30/2.98  fof(f40,plain,(
% 19.30/2.98    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 19.30/2.98    inference(cnf_transformation,[],[f12])).
% 19.30/2.98  
% 19.30/2.98  fof(f45,plain,(
% 19.30/2.98    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 19.30/2.98    inference(definition_unfolding,[],[f39,f40])).
% 19.30/2.98  
% 19.30/2.98  fof(f46,plain,(
% 19.30/2.98    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 19.30/2.98    inference(definition_unfolding,[],[f38,f45])).
% 19.30/2.98  
% 19.30/2.98  fof(f47,plain,(
% 19.30/2.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 19.30/2.98    inference(definition_unfolding,[],[f37,f46])).
% 19.30/2.98  
% 19.30/2.98  fof(f48,plain,(
% 19.30/2.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 19.30/2.98    inference(definition_unfolding,[],[f36,f47])).
% 19.30/2.98  
% 19.30/2.98  fof(f49,plain,(
% 19.30/2.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 19.30/2.98    inference(definition_unfolding,[],[f35,f48])).
% 19.30/2.98  
% 19.30/2.98  fof(f50,plain,(
% 19.30/2.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 19.30/2.98    inference(definition_unfolding,[],[f41,f49])).
% 19.30/2.98  
% 19.30/2.98  fof(f51,plain,(
% 19.30/2.98    ( ! [X0,X1] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))) )),
% 19.30/2.98    inference(definition_unfolding,[],[f27,f50,f50])).
% 19.30/2.98  
% 19.30/2.98  fof(f5,axiom,(
% 19.30/2.98    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 19.30/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.30/2.98  
% 19.30/2.98  fof(f33,plain,(
% 19.30/2.98    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 19.30/2.98    inference(cnf_transformation,[],[f5])).
% 19.30/2.98  
% 19.30/2.98  fof(f52,plain,(
% 19.30/2.98    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0)) )),
% 19.30/2.98    inference(definition_unfolding,[],[f33,f50])).
% 19.30/2.98  
% 19.30/2.98  fof(f4,axiom,(
% 19.30/2.98    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 19.30/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.30/2.98  
% 19.30/2.98  fof(f18,plain,(
% 19.30/2.98    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 19.30/2.98    inference(ennf_transformation,[],[f4])).
% 19.30/2.98  
% 19.30/2.98  fof(f32,plain,(
% 19.30/2.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 19.30/2.98    inference(cnf_transformation,[],[f18])).
% 19.30/2.98  
% 19.30/2.98  fof(f14,axiom,(
% 19.30/2.98    ! [X0,X1,X2] : (v1_relat_1(X2) => k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k2_xboole_0(X0,X1)))),
% 19.30/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.30/2.98  
% 19.30/2.98  fof(f21,plain,(
% 19.30/2.98    ! [X0,X1,X2] : (k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k2_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 19.30/2.98    inference(ennf_transformation,[],[f14])).
% 19.30/2.98  
% 19.30/2.98  fof(f42,plain,(
% 19.30/2.98    ( ! [X2,X0,X1] : (k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k2_xboole_0(X0,X1)) | ~v1_relat_1(X2)) )),
% 19.30/2.98    inference(cnf_transformation,[],[f21])).
% 19.30/2.98  
% 19.30/2.98  fof(f15,conjecture,(
% 19.30/2.98    ! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k10_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))))),
% 19.30/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.30/2.98  
% 19.30/2.98  fof(f16,negated_conjecture,(
% 19.30/2.98    ~! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k10_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))))),
% 19.30/2.98    inference(negated_conjecture,[],[f15])).
% 19.30/2.98  
% 19.30/2.98  fof(f22,plain,(
% 19.30/2.98    ? [X0,X1,X2] : (~r1_tarski(k10_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) & v1_relat_1(X2))),
% 19.30/2.98    inference(ennf_transformation,[],[f16])).
% 19.30/2.98  
% 19.30/2.98  fof(f25,plain,(
% 19.30/2.98    ? [X0,X1,X2] : (~r1_tarski(k10_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) & v1_relat_1(X2)) => (~r1_tarski(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))) & v1_relat_1(sK2))),
% 19.30/2.98    introduced(choice_axiom,[])).
% 19.30/2.98  
% 19.30/2.98  fof(f26,plain,(
% 19.30/2.98    ~r1_tarski(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))) & v1_relat_1(sK2)),
% 19.30/2.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f25])).
% 19.30/2.98  
% 19.30/2.98  fof(f43,plain,(
% 19.30/2.98    v1_relat_1(sK2)),
% 19.30/2.98    inference(cnf_transformation,[],[f26])).
% 19.30/2.98  
% 19.30/2.98  fof(f6,axiom,(
% 19.30/2.98    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 19.30/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.30/2.98  
% 19.30/2.98  fof(f19,plain,(
% 19.30/2.98    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 19.30/2.98    inference(ennf_transformation,[],[f6])).
% 19.30/2.98  
% 19.30/2.98  fof(f20,plain,(
% 19.30/2.98    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 19.30/2.98    inference(flattening,[],[f19])).
% 19.30/2.98  
% 19.30/2.98  fof(f34,plain,(
% 19.30/2.98    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 19.30/2.98    inference(cnf_transformation,[],[f20])).
% 19.30/2.98  
% 19.30/2.98  fof(f53,plain,(
% 19.30/2.98    ( ! [X2,X0,X1] : (r1_tarski(X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 19.30/2.98    inference(definition_unfolding,[],[f34,f50])).
% 19.30/2.98  
% 19.30/2.98  fof(f44,plain,(
% 19.30/2.98    ~r1_tarski(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))),
% 19.30/2.98    inference(cnf_transformation,[],[f26])).
% 19.30/2.98  
% 19.30/2.98  fof(f54,plain,(
% 19.30/2.98    ~r1_tarski(k10_relat_1(sK2,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k1_setfam_1(k6_enumset1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))))),
% 19.30/2.98    inference(definition_unfolding,[],[f44,f50,f50])).
% 19.30/2.98  
% 19.30/2.98  fof(f2,axiom,(
% 19.30/2.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 19.30/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.30/2.98  
% 19.30/2.98  fof(f23,plain,(
% 19.30/2.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 19.30/2.98    inference(nnf_transformation,[],[f2])).
% 19.30/2.98  
% 19.30/2.98  fof(f24,plain,(
% 19.30/2.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 19.30/2.98    inference(flattening,[],[f23])).
% 19.30/2.98  
% 19.30/2.98  fof(f28,plain,(
% 19.30/2.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 19.30/2.98    inference(cnf_transformation,[],[f24])).
% 19.30/2.98  
% 19.30/2.98  fof(f56,plain,(
% 19.30/2.98    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 19.30/2.98    inference(equality_resolution,[],[f28])).
% 19.30/2.98  
% 19.30/2.98  fof(f30,plain,(
% 19.30/2.98    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 19.30/2.98    inference(cnf_transformation,[],[f24])).
% 19.30/2.98  
% 19.30/2.98  cnf(c_4,plain,
% 19.30/2.98      ( r1_tarski(X0,X1) | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
% 19.30/2.98      inference(cnf_transformation,[],[f31]) ).
% 19.30/2.98  
% 19.30/2.98  cnf(c_454,plain,
% 19.30/2.98      ( r1_tarski(k10_relat_1(sK2,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k10_relat_1(sK2,sK0))
% 19.30/2.98      | ~ r1_tarski(k2_xboole_0(k10_relat_1(sK2,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),X0),k10_relat_1(sK2,sK0)) ),
% 19.30/2.98      inference(instantiation,[status(thm)],[c_4]) ).
% 19.30/2.98  
% 19.30/2.98  cnf(c_54076,plain,
% 19.30/2.98      ( r1_tarski(k10_relat_1(sK2,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k10_relat_1(sK2,sK0))
% 19.30/2.98      | ~ r1_tarski(k2_xboole_0(k10_relat_1(sK2,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k10_relat_1(sK2,X0)),k10_relat_1(sK2,sK0)) ),
% 19.30/2.98      inference(instantiation,[status(thm)],[c_454]) ).
% 19.30/2.98  
% 19.30/2.98  cnf(c_54078,plain,
% 19.30/2.98      ( r1_tarski(k10_relat_1(sK2,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k10_relat_1(sK2,sK0))
% 19.30/2.98      | ~ r1_tarski(k2_xboole_0(k10_relat_1(sK2,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k10_relat_1(sK2,sK0)),k10_relat_1(sK2,sK0)) ),
% 19.30/2.98      inference(instantiation,[status(thm)],[c_54076]) ).
% 19.30/2.98  
% 19.30/2.98  cnf(c_0,plain,
% 19.30/2.98      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)) ),
% 19.30/2.98      inference(cnf_transformation,[],[f51]) ).
% 19.30/2.98  
% 19.30/2.98  cnf(c_6,plain,
% 19.30/2.98      ( r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0) ),
% 19.30/2.98      inference(cnf_transformation,[],[f52]) ).
% 19.30/2.98  
% 19.30/2.98  cnf(c_313,plain,
% 19.30/2.98      ( r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0) = iProver_top ),
% 19.30/2.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 19.30/2.98  
% 19.30/2.98  cnf(c_426,plain,
% 19.30/2.98      ( r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X1) = iProver_top ),
% 19.30/2.98      inference(superposition,[status(thm)],[c_0,c_313]) ).
% 19.30/2.98  
% 19.30/2.98  cnf(c_5,plain,
% 19.30/2.98      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 19.30/2.98      inference(cnf_transformation,[],[f32]) ).
% 19.30/2.98  
% 19.30/2.98  cnf(c_314,plain,
% 19.30/2.98      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 19.30/2.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 19.30/2.98  
% 19.30/2.98  cnf(c_667,plain,
% 19.30/2.98      ( k2_xboole_0(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X1) = X1 ),
% 19.30/2.98      inference(superposition,[status(thm)],[c_426,c_314]) ).
% 19.30/2.98  
% 19.30/2.98  cnf(c_8,plain,
% 19.30/2.98      ( ~ v1_relat_1(X0)
% 19.30/2.98      | k2_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k10_relat_1(X0,k2_xboole_0(X1,X2)) ),
% 19.30/2.98      inference(cnf_transformation,[],[f42]) ).
% 19.30/2.98  
% 19.30/2.98  cnf(c_10,negated_conjecture,
% 19.30/2.98      ( v1_relat_1(sK2) ),
% 19.30/2.98      inference(cnf_transformation,[],[f43]) ).
% 19.30/2.98  
% 19.30/2.98  cnf(c_114,plain,
% 19.30/2.98      ( k2_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k10_relat_1(X0,k2_xboole_0(X1,X2))
% 19.30/2.98      | sK2 != X0 ),
% 19.30/2.98      inference(resolution_lifted,[status(thm)],[c_8,c_10]) ).
% 19.30/2.98  
% 19.30/2.98  cnf(c_115,plain,
% 19.30/2.98      ( k2_xboole_0(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) = k10_relat_1(sK2,k2_xboole_0(X0,X1)) ),
% 19.30/2.98      inference(unflattening,[status(thm)],[c_114]) ).
% 19.30/2.98  
% 19.30/2.98  cnf(c_315,plain,
% 19.30/2.98      ( r1_tarski(X0,X1) = iProver_top
% 19.30/2.98      | r1_tarski(k2_xboole_0(X0,X2),X1) != iProver_top ),
% 19.30/2.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 19.30/2.98  
% 19.30/2.98  cnf(c_518,plain,
% 19.30/2.98      ( r1_tarski(k10_relat_1(sK2,X0),X1) = iProver_top
% 19.30/2.98      | r1_tarski(k10_relat_1(sK2,k2_xboole_0(X0,X2)),X1) != iProver_top ),
% 19.30/2.98      inference(superposition,[status(thm)],[c_115,c_315]) ).
% 19.30/2.98  
% 19.30/2.98  cnf(c_1842,plain,
% 19.30/2.98      ( r1_tarski(k10_relat_1(sK2,X0),X1) != iProver_top
% 19.30/2.98      | r1_tarski(k10_relat_1(sK2,k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X0))),X1) = iProver_top ),
% 19.30/2.98      inference(superposition,[status(thm)],[c_667,c_518]) ).
% 19.30/2.98  
% 19.30/2.98  cnf(c_7,plain,
% 19.30/2.98      ( ~ r1_tarski(X0,X1)
% 19.30/2.98      | ~ r1_tarski(X0,X2)
% 19.30/2.98      | r1_tarski(X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) ),
% 19.30/2.98      inference(cnf_transformation,[],[f53]) ).
% 19.30/2.98  
% 19.30/2.98  cnf(c_312,plain,
% 19.30/2.98      ( r1_tarski(X0,X1) != iProver_top
% 19.30/2.98      | r1_tarski(X0,X2) != iProver_top
% 19.30/2.98      | r1_tarski(X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) = iProver_top ),
% 19.30/2.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 19.30/2.98  
% 19.30/2.98  cnf(c_9,negated_conjecture,
% 19.30/2.98      ( ~ r1_tarski(k10_relat_1(sK2,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k1_setfam_1(k6_enumset1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))) ),
% 19.30/2.98      inference(cnf_transformation,[],[f54]) ).
% 19.30/2.98  
% 19.30/2.98  cnf(c_311,plain,
% 19.30/2.98      ( r1_tarski(k10_relat_1(sK2,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k1_setfam_1(k6_enumset1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))) != iProver_top ),
% 19.30/2.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 19.30/2.98  
% 19.30/2.98  cnf(c_849,plain,
% 19.30/2.98      ( r1_tarski(k10_relat_1(sK2,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k10_relat_1(sK2,sK1)) != iProver_top
% 19.30/2.98      | r1_tarski(k10_relat_1(sK2,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k10_relat_1(sK2,sK0)) != iProver_top ),
% 19.30/2.98      inference(superposition,[status(thm)],[c_312,c_311]) ).
% 19.30/2.98  
% 19.30/2.98  cnf(c_34460,plain,
% 19.30/2.98      ( r1_tarski(k10_relat_1(sK2,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k10_relat_1(sK2,sK0)) != iProver_top
% 19.30/2.98      | r1_tarski(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK1)) != iProver_top ),
% 19.30/2.98      inference(superposition,[status(thm)],[c_1842,c_849]) ).
% 19.30/2.98  
% 19.30/2.98  cnf(c_34486,plain,
% 19.30/2.98      ( ~ r1_tarski(k10_relat_1(sK2,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k10_relat_1(sK2,sK0))
% 19.30/2.98      | ~ r1_tarski(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK1)) ),
% 19.30/2.98      inference(predicate_to_equality_rev,[status(thm)],[c_34460]) ).
% 19.30/2.98  
% 19.30/2.98  cnf(c_175,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 19.30/2.98  
% 19.30/2.98  cnf(c_24877,plain,
% 19.30/2.98      ( X0 != X1
% 19.30/2.98      | X0 = k2_xboole_0(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),X2)
% 19.30/2.98      | k2_xboole_0(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),X2) != X1 ),
% 19.30/2.98      inference(instantiation,[status(thm)],[c_175]) ).
% 19.30/2.98  
% 19.30/2.98  cnf(c_24878,plain,
% 19.30/2.98      ( k2_xboole_0(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK0) != sK0
% 19.30/2.98      | sK0 = k2_xboole_0(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK0)
% 19.30/2.98      | sK0 != sK0 ),
% 19.30/2.98      inference(instantiation,[status(thm)],[c_24877]) ).
% 19.30/2.98  
% 19.30/2.98  cnf(c_23973,plain,
% 19.30/2.98      ( ~ r1_tarski(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),X0)
% 19.30/2.98      | k2_xboole_0(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),X0) = X0 ),
% 19.30/2.98      inference(instantiation,[status(thm)],[c_5]) ).
% 19.30/2.98  
% 19.30/2.98  cnf(c_23975,plain,
% 19.30/2.98      ( ~ r1_tarski(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK0)
% 19.30/2.98      | k2_xboole_0(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK0) = sK0 ),
% 19.30/2.98      inference(instantiation,[status(thm)],[c_23973]) ).
% 19.30/2.98  
% 19.30/2.98  cnf(c_178,plain,
% 19.30/2.98      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 19.30/2.98      theory(equality) ).
% 19.30/2.98  
% 19.30/2.98  cnf(c_353,plain,
% 19.30/2.98      ( ~ r1_tarski(X0,X1)
% 19.30/2.98      | r1_tarski(k2_xboole_0(X2,X3),X4)
% 19.30/2.98      | X4 != X1
% 19.30/2.98      | k2_xboole_0(X2,X3) != X0 ),
% 19.30/2.98      inference(instantiation,[status(thm)],[c_178]) ).
% 19.30/2.98  
% 19.30/2.98  cnf(c_492,plain,
% 19.30/2.98      ( ~ r1_tarski(X0,X1)
% 19.30/2.98      | r1_tarski(k2_xboole_0(k10_relat_1(sK2,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),X2),k10_relat_1(sK2,sK0))
% 19.30/2.98      | k10_relat_1(sK2,sK0) != X1
% 19.30/2.98      | k2_xboole_0(k10_relat_1(sK2,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),X2) != X0 ),
% 19.30/2.98      inference(instantiation,[status(thm)],[c_353]) ).
% 19.30/2.98  
% 19.30/2.98  cnf(c_1753,plain,
% 19.30/2.98      ( ~ r1_tarski(X0,k10_relat_1(sK2,X1))
% 19.30/2.98      | r1_tarski(k2_xboole_0(k10_relat_1(sK2,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),X2),k10_relat_1(sK2,sK0))
% 19.30/2.98      | k10_relat_1(sK2,sK0) != k10_relat_1(sK2,X1)
% 19.30/2.98      | k2_xboole_0(k10_relat_1(sK2,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),X2) != X0 ),
% 19.30/2.98      inference(instantiation,[status(thm)],[c_492]) ).
% 19.30/2.98  
% 19.30/2.98  cnf(c_4000,plain,
% 19.30/2.98      ( ~ r1_tarski(k10_relat_1(sK2,k2_xboole_0(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),X0)),k10_relat_1(sK2,X1))
% 19.30/2.98      | r1_tarski(k2_xboole_0(k10_relat_1(sK2,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k10_relat_1(sK2,X0)),k10_relat_1(sK2,sK0))
% 19.30/2.98      | k10_relat_1(sK2,sK0) != k10_relat_1(sK2,X1)
% 19.30/2.98      | k2_xboole_0(k10_relat_1(sK2,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k10_relat_1(sK2,X0)) != k10_relat_1(sK2,k2_xboole_0(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),X0)) ),
% 19.30/2.98      inference(instantiation,[status(thm)],[c_1753]) ).
% 19.30/2.98  
% 19.30/2.98  cnf(c_23927,plain,
% 19.30/2.98      ( ~ r1_tarski(k10_relat_1(sK2,k2_xboole_0(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),X0)),k10_relat_1(sK2,k2_xboole_0(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),X0)))
% 19.30/2.98      | r1_tarski(k2_xboole_0(k10_relat_1(sK2,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k10_relat_1(sK2,X0)),k10_relat_1(sK2,sK0))
% 19.30/2.98      | k10_relat_1(sK2,sK0) != k10_relat_1(sK2,k2_xboole_0(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),X0))
% 19.30/2.98      | k2_xboole_0(k10_relat_1(sK2,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k10_relat_1(sK2,X0)) != k10_relat_1(sK2,k2_xboole_0(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),X0)) ),
% 19.30/2.98      inference(instantiation,[status(thm)],[c_4000]) ).
% 19.30/2.98  
% 19.30/2.98  cnf(c_23929,plain,
% 19.30/2.98      ( ~ r1_tarski(k10_relat_1(sK2,k2_xboole_0(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK0)),k10_relat_1(sK2,k2_xboole_0(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK0)))
% 19.30/2.98      | r1_tarski(k2_xboole_0(k10_relat_1(sK2,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k10_relat_1(sK2,sK0)),k10_relat_1(sK2,sK0))
% 19.30/2.98      | k10_relat_1(sK2,sK0) != k10_relat_1(sK2,k2_xboole_0(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK0))
% 19.30/2.98      | k2_xboole_0(k10_relat_1(sK2,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k10_relat_1(sK2,sK0)) != k10_relat_1(sK2,k2_xboole_0(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK0)) ),
% 19.30/2.98      inference(instantiation,[status(thm)],[c_23927]) ).
% 19.30/2.98  
% 19.30/2.98  cnf(c_3,plain,
% 19.30/2.98      ( r1_tarski(X0,X0) ),
% 19.30/2.98      inference(cnf_transformation,[],[f56]) ).
% 19.30/2.98  
% 19.30/2.98  cnf(c_7302,plain,
% 19.30/2.98      ( r1_tarski(k10_relat_1(sK2,X0),k10_relat_1(sK2,X0)) ),
% 19.30/2.98      inference(instantiation,[status(thm)],[c_3]) ).
% 19.30/2.98  
% 19.30/2.98  cnf(c_18393,plain,
% 19.30/2.98      ( r1_tarski(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK1)) ),
% 19.30/2.98      inference(instantiation,[status(thm)],[c_7302]) ).
% 19.30/2.98  
% 19.30/2.98  cnf(c_18006,plain,
% 19.30/2.98      ( r1_tarski(k10_relat_1(sK2,k2_xboole_0(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),X0)),k10_relat_1(sK2,k2_xboole_0(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),X0))) ),
% 19.30/2.98      inference(instantiation,[status(thm)],[c_7302]) ).
% 19.30/2.98  
% 19.30/2.98  cnf(c_18012,plain,
% 19.30/2.98      ( r1_tarski(k10_relat_1(sK2,k2_xboole_0(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK0)),k10_relat_1(sK2,k2_xboole_0(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK0))) ),
% 19.30/2.98      inference(instantiation,[status(thm)],[c_18006]) ).
% 19.30/2.98  
% 19.30/2.98  cnf(c_180,plain,
% 19.30/2.98      ( X0 != X1 | X2 != X3 | k10_relat_1(X0,X2) = k10_relat_1(X1,X3) ),
% 19.30/2.98      theory(equality) ).
% 19.30/2.98  
% 19.30/2.98  cnf(c_3287,plain,
% 19.30/2.98      ( X0 != k2_xboole_0(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),X1)
% 19.30/2.98      | X2 != sK2
% 19.30/2.98      | k10_relat_1(X2,X0) = k10_relat_1(sK2,k2_xboole_0(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),X1)) ),
% 19.30/2.98      inference(instantiation,[status(thm)],[c_180]) ).
% 19.30/2.98  
% 19.30/2.98  cnf(c_9901,plain,
% 19.30/2.98      ( X0 != k2_xboole_0(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),X1)
% 19.30/2.98      | k10_relat_1(sK2,X0) = k10_relat_1(sK2,k2_xboole_0(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),X1))
% 19.30/2.98      | sK2 != sK2 ),
% 19.30/2.98      inference(instantiation,[status(thm)],[c_3287]) ).
% 19.30/2.98  
% 19.30/2.98  cnf(c_9902,plain,
% 19.30/2.98      ( k10_relat_1(sK2,sK0) = k10_relat_1(sK2,k2_xboole_0(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK0))
% 19.30/2.98      | sK0 != k2_xboole_0(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK0)
% 19.30/2.98      | sK2 != sK2 ),
% 19.30/2.98      inference(instantiation,[status(thm)],[c_9901]) ).
% 19.30/2.98  
% 19.30/2.98  cnf(c_1908,plain,
% 19.30/2.98      ( r1_tarski(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK0) ),
% 19.30/2.98      inference(instantiation,[status(thm)],[c_6]) ).
% 19.30/2.98  
% 19.30/2.98  cnf(c_1074,plain,
% 19.30/2.98      ( k2_xboole_0(k10_relat_1(sK2,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k10_relat_1(sK2,X0)) = k10_relat_1(sK2,k2_xboole_0(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),X0)) ),
% 19.30/2.98      inference(instantiation,[status(thm)],[c_115]) ).
% 19.30/2.98  
% 19.30/2.98  cnf(c_1079,plain,
% 19.30/2.98      ( k2_xboole_0(k10_relat_1(sK2,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k10_relat_1(sK2,sK0)) = k10_relat_1(sK2,k2_xboole_0(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK0)) ),
% 19.30/2.98      inference(instantiation,[status(thm)],[c_1074]) ).
% 19.30/2.98  
% 19.30/2.98  cnf(c_174,plain,( X0 = X0 ),theory(equality) ).
% 19.30/2.98  
% 19.30/2.98  cnf(c_627,plain,
% 19.30/2.98      ( sK2 = sK2 ),
% 19.30/2.98      inference(instantiation,[status(thm)],[c_174]) ).
% 19.30/2.98  
% 19.30/2.98  cnf(c_1,plain,
% 19.30/2.98      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 19.30/2.98      inference(cnf_transformation,[],[f30]) ).
% 19.30/2.98  
% 19.30/2.98  cnf(c_33,plain,
% 19.30/2.98      ( ~ r1_tarski(sK0,sK0) | sK0 = sK0 ),
% 19.30/2.98      inference(instantiation,[status(thm)],[c_1]) ).
% 19.30/2.98  
% 19.30/2.98  cnf(c_29,plain,
% 19.30/2.98      ( r1_tarski(sK0,sK0) ),
% 19.30/2.98      inference(instantiation,[status(thm)],[c_3]) ).
% 19.30/2.98  
% 19.30/2.98  cnf(contradiction,plain,
% 19.30/2.98      ( $false ),
% 19.30/2.98      inference(minisat,
% 19.30/2.98                [status(thm)],
% 19.30/2.98                [c_54078,c_34486,c_24878,c_23975,c_23929,c_18393,c_18012,
% 19.30/2.98                 c_9902,c_1908,c_1079,c_627,c_33,c_29]) ).
% 19.30/2.98  
% 19.30/2.98  
% 19.30/2.98  % SZS output end CNFRefutation for theBenchmark.p
% 19.30/2.98  
% 19.30/2.98  ------                               Statistics
% 19.30/2.98  
% 19.30/2.98  ------ Selected
% 19.30/2.98  
% 19.30/2.98  total_time:                             2.468
% 19.30/2.98  
%------------------------------------------------------------------------------
