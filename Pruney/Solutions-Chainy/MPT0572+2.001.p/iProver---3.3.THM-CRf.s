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
% DateTime   : Thu Dec  3 11:47:43 EST 2020

% Result     : Theorem 23.46s
% Output     : CNFRefutation 23.46s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 286 expanded)
%              Number of clauses        :   28 (  43 expanded)
%              Number of leaves         :   17 (  81 expanded)
%              Depth                    :   15
%              Number of atoms          :  136 ( 380 expanded)
%              Number of equality atoms :   66 ( 250 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f13])).

fof(f47,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f41,f42])).

fof(f48,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f40,f47])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f39,f48])).

fof(f50,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f38,f49])).

fof(f51,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f37,f50])).

fof(f57,plain,(
    ! [X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f36,f51,f51])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f14,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f52,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f43,f51])).

fof(f54,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f33,f52])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f53,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f31,f52])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)))) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f35,f53])).

fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k10_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => r1_tarski(k10_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k10_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f26,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k10_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ~ r1_tarski(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f26])).

fof(f45,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k2_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k2_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k2_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f24])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f59,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f29])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f5,axiom,(
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
    inference(ennf_transformation,[],[f5])).

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

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f34,f52])).

fof(f46,plain,(
    ~ r1_tarski(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f27])).

fof(f58,plain,(
    ~ r1_tarski(k10_relat_1(sK2,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k1_setfam_1(k6_enumset1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))) ),
    inference(definition_unfolding,[],[f46,f52,f52])).

cnf(c_7,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_4,plain,
    ( r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_315,plain,
    ( r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_827,plain,
    ( r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_315])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)))) = X1 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_313,plain,
    ( k2_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)))) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1212,plain,
    ( k2_xboole_0(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))))) = X1 ),
    inference(superposition,[status(thm)],[c_827,c_313])).

cnf(c_10,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_310,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | k2_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k10_relat_1(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_312,plain,
    ( k2_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k10_relat_1(X0,k2_xboole_0(X1,X2))
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1059,plain,
    ( k2_xboole_0(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) = k10_relat_1(sK2,k2_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_310,c_312])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_317,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_316,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(k2_xboole_0(X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_595,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_317,c_316])).

cnf(c_1233,plain,
    ( r1_tarski(k10_relat_1(sK2,X0),k10_relat_1(sK2,k2_xboole_0(X0,X1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1059,c_595])).

cnf(c_24127,plain,
    ( r1_tarski(k10_relat_1(sK2,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),k10_relat_1(sK2,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1212,c_1233])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_314,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_9,negated_conjecture,
    ( ~ r1_tarski(k10_relat_1(sK2,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k1_setfam_1(k6_enumset1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_311,plain,
    ( r1_tarski(k10_relat_1(sK2,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k1_setfam_1(k6_enumset1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2276,plain,
    ( r1_tarski(k10_relat_1(sK2,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k10_relat_1(sK2,sK1)) != iProver_top
    | r1_tarski(k10_relat_1(sK2,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k10_relat_1(sK2,sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_314,c_311])).

cnf(c_48476,plain,
    ( r1_tarski(k10_relat_1(sK2,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k10_relat_1(sK2,sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_24127,c_2276])).

cnf(c_1208,plain,
    ( k2_xboole_0(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))))) = X0 ),
    inference(superposition,[status(thm)],[c_315,c_313])).

cnf(c_10197,plain,
    ( r1_tarski(k10_relat_1(sK2,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),k10_relat_1(sK2,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1208,c_1233])).

cnf(c_48902,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_48476,c_10197])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 11:23:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 23.46/3.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 23.46/3.49  
% 23.46/3.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 23.46/3.49  
% 23.46/3.49  ------  iProver source info
% 23.46/3.49  
% 23.46/3.49  git: date: 2020-06-30 10:37:57 +0100
% 23.46/3.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 23.46/3.49  git: non_committed_changes: false
% 23.46/3.49  git: last_make_outside_of_git: false
% 23.46/3.49  
% 23.46/3.49  ------ 
% 23.46/3.49  ------ Parsing...
% 23.46/3.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 23.46/3.49  
% 23.46/3.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 23.46/3.49  
% 23.46/3.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 23.46/3.49  
% 23.46/3.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 23.46/3.49  ------ Proving...
% 23.46/3.49  ------ Problem Properties 
% 23.46/3.49  
% 23.46/3.49  
% 23.46/3.49  clauses                                 10
% 23.46/3.49  conjectures                             2
% 23.46/3.49  EPR                                     3
% 23.46/3.49  Horn                                    10
% 23.46/3.49  unary                                   5
% 23.46/3.49  binary                                  3
% 23.46/3.49  lits                                    17
% 23.46/3.49  lits eq                                 4
% 23.46/3.49  fd_pure                                 0
% 23.46/3.49  fd_pseudo                               0
% 23.46/3.49  fd_cond                                 0
% 23.46/3.49  fd_pseudo_cond                          1
% 23.46/3.49  AC symbols                              0
% 23.46/3.49  
% 23.46/3.49  ------ Input Options Time Limit: Unbounded
% 23.46/3.49  
% 23.46/3.49  
% 23.46/3.49  ------ 
% 23.46/3.49  Current options:
% 23.46/3.49  ------ 
% 23.46/3.49  
% 23.46/3.49  
% 23.46/3.49  
% 23.46/3.49  
% 23.46/3.49  ------ Proving...
% 23.46/3.49  
% 23.46/3.49  
% 23.46/3.49  % SZS status Theorem for theBenchmark.p
% 23.46/3.49  
% 23.46/3.49   Resolution empty clause
% 23.46/3.49  
% 23.46/3.49  % SZS output start CNFRefutation for theBenchmark.p
% 23.46/3.49  
% 23.46/3.49  fof(f7,axiom,(
% 23.46/3.49    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 23.46/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.46/3.49  
% 23.46/3.49  fof(f36,plain,(
% 23.46/3.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 23.46/3.49    inference(cnf_transformation,[],[f7])).
% 23.46/3.49  
% 23.46/3.49  fof(f8,axiom,(
% 23.46/3.49    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 23.46/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.46/3.49  
% 23.46/3.49  fof(f37,plain,(
% 23.46/3.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 23.46/3.49    inference(cnf_transformation,[],[f8])).
% 23.46/3.49  
% 23.46/3.49  fof(f9,axiom,(
% 23.46/3.49    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 23.46/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.46/3.49  
% 23.46/3.49  fof(f38,plain,(
% 23.46/3.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 23.46/3.49    inference(cnf_transformation,[],[f9])).
% 23.46/3.49  
% 23.46/3.49  fof(f10,axiom,(
% 23.46/3.49    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 23.46/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.46/3.49  
% 23.46/3.49  fof(f39,plain,(
% 23.46/3.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 23.46/3.49    inference(cnf_transformation,[],[f10])).
% 23.46/3.49  
% 23.46/3.49  fof(f11,axiom,(
% 23.46/3.49    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 23.46/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.46/3.49  
% 23.46/3.49  fof(f40,plain,(
% 23.46/3.49    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 23.46/3.49    inference(cnf_transformation,[],[f11])).
% 23.46/3.49  
% 23.46/3.49  fof(f12,axiom,(
% 23.46/3.49    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 23.46/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.46/3.49  
% 23.46/3.49  fof(f41,plain,(
% 23.46/3.49    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 23.46/3.49    inference(cnf_transformation,[],[f12])).
% 23.46/3.49  
% 23.46/3.49  fof(f13,axiom,(
% 23.46/3.49    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 23.46/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.46/3.49  
% 23.46/3.49  fof(f42,plain,(
% 23.46/3.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 23.46/3.49    inference(cnf_transformation,[],[f13])).
% 23.46/3.49  
% 23.46/3.49  fof(f47,plain,(
% 23.46/3.49    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 23.46/3.49    inference(definition_unfolding,[],[f41,f42])).
% 23.46/3.49  
% 23.46/3.49  fof(f48,plain,(
% 23.46/3.49    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 23.46/3.49    inference(definition_unfolding,[],[f40,f47])).
% 23.46/3.49  
% 23.46/3.49  fof(f49,plain,(
% 23.46/3.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 23.46/3.49    inference(definition_unfolding,[],[f39,f48])).
% 23.46/3.49  
% 23.46/3.49  fof(f50,plain,(
% 23.46/3.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 23.46/3.49    inference(definition_unfolding,[],[f38,f49])).
% 23.46/3.49  
% 23.46/3.49  fof(f51,plain,(
% 23.46/3.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 23.46/3.49    inference(definition_unfolding,[],[f37,f50])).
% 23.46/3.49  
% 23.46/3.49  fof(f57,plain,(
% 23.46/3.49    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)) )),
% 23.46/3.49    inference(definition_unfolding,[],[f36,f51,f51])).
% 23.46/3.49  
% 23.46/3.49  fof(f4,axiom,(
% 23.46/3.49    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 23.46/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.46/3.49  
% 23.46/3.49  fof(f33,plain,(
% 23.46/3.49    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 23.46/3.49    inference(cnf_transformation,[],[f4])).
% 23.46/3.49  
% 23.46/3.49  fof(f14,axiom,(
% 23.46/3.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 23.46/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.46/3.49  
% 23.46/3.49  fof(f43,plain,(
% 23.46/3.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 23.46/3.49    inference(cnf_transformation,[],[f14])).
% 23.46/3.49  
% 23.46/3.49  fof(f52,plain,(
% 23.46/3.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 23.46/3.49    inference(definition_unfolding,[],[f43,f51])).
% 23.46/3.49  
% 23.46/3.49  fof(f54,plain,(
% 23.46/3.49    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0)) )),
% 23.46/3.49    inference(definition_unfolding,[],[f33,f52])).
% 23.46/3.49  
% 23.46/3.49  fof(f6,axiom,(
% 23.46/3.49    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1)),
% 23.46/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.46/3.49  
% 23.46/3.49  fof(f21,plain,(
% 23.46/3.49    ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1))),
% 23.46/3.49    inference(ennf_transformation,[],[f6])).
% 23.46/3.49  
% 23.46/3.49  fof(f35,plain,(
% 23.46/3.49    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1)) )),
% 23.46/3.49    inference(cnf_transformation,[],[f21])).
% 23.46/3.49  
% 23.46/3.49  fof(f2,axiom,(
% 23.46/3.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 23.46/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.46/3.49  
% 23.46/3.49  fof(f31,plain,(
% 23.46/3.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 23.46/3.49    inference(cnf_transformation,[],[f2])).
% 23.46/3.49  
% 23.46/3.49  fof(f53,plain,(
% 23.46/3.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 23.46/3.49    inference(definition_unfolding,[],[f31,f52])).
% 23.46/3.49  
% 23.46/3.49  fof(f56,plain,(
% 23.46/3.49    ( ! [X0,X1] : (k2_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)))) = X1 | ~r1_tarski(X0,X1)) )),
% 23.46/3.49    inference(definition_unfolding,[],[f35,f53])).
% 23.46/3.49  
% 23.46/3.49  fof(f16,conjecture,(
% 23.46/3.49    ! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k10_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))))),
% 23.46/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.46/3.49  
% 23.46/3.49  fof(f17,negated_conjecture,(
% 23.46/3.49    ~! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k10_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))))),
% 23.46/3.49    inference(negated_conjecture,[],[f16])).
% 23.46/3.49  
% 23.46/3.49  fof(f23,plain,(
% 23.46/3.49    ? [X0,X1,X2] : (~r1_tarski(k10_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) & v1_relat_1(X2))),
% 23.46/3.49    inference(ennf_transformation,[],[f17])).
% 23.46/3.49  
% 23.46/3.49  fof(f26,plain,(
% 23.46/3.49    ? [X0,X1,X2] : (~r1_tarski(k10_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) & v1_relat_1(X2)) => (~r1_tarski(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))) & v1_relat_1(sK2))),
% 23.46/3.49    introduced(choice_axiom,[])).
% 23.46/3.49  
% 23.46/3.49  fof(f27,plain,(
% 23.46/3.49    ~r1_tarski(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))) & v1_relat_1(sK2)),
% 23.46/3.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f26])).
% 23.46/3.49  
% 23.46/3.49  fof(f45,plain,(
% 23.46/3.49    v1_relat_1(sK2)),
% 23.46/3.49    inference(cnf_transformation,[],[f27])).
% 23.46/3.49  
% 23.46/3.49  fof(f15,axiom,(
% 23.46/3.49    ! [X0,X1,X2] : (v1_relat_1(X2) => k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k2_xboole_0(X0,X1)))),
% 23.46/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.46/3.49  
% 23.46/3.49  fof(f22,plain,(
% 23.46/3.49    ! [X0,X1,X2] : (k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k2_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 23.46/3.49    inference(ennf_transformation,[],[f15])).
% 23.46/3.49  
% 23.46/3.49  fof(f44,plain,(
% 23.46/3.49    ( ! [X2,X0,X1] : (k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k2_xboole_0(X0,X1)) | ~v1_relat_1(X2)) )),
% 23.46/3.49    inference(cnf_transformation,[],[f22])).
% 23.46/3.49  
% 23.46/3.49  fof(f1,axiom,(
% 23.46/3.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 23.46/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.46/3.49  
% 23.46/3.49  fof(f24,plain,(
% 23.46/3.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 23.46/3.49    inference(nnf_transformation,[],[f1])).
% 23.46/3.49  
% 23.46/3.49  fof(f25,plain,(
% 23.46/3.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 23.46/3.49    inference(flattening,[],[f24])).
% 23.46/3.49  
% 23.46/3.49  fof(f29,plain,(
% 23.46/3.49    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 23.46/3.49    inference(cnf_transformation,[],[f25])).
% 23.46/3.49  
% 23.46/3.49  fof(f59,plain,(
% 23.46/3.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 23.46/3.49    inference(equality_resolution,[],[f29])).
% 23.46/3.49  
% 23.46/3.49  fof(f3,axiom,(
% 23.46/3.49    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 23.46/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.46/3.49  
% 23.46/3.49  fof(f18,plain,(
% 23.46/3.49    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 23.46/3.49    inference(ennf_transformation,[],[f3])).
% 23.46/3.49  
% 23.46/3.49  fof(f32,plain,(
% 23.46/3.49    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 23.46/3.49    inference(cnf_transformation,[],[f18])).
% 23.46/3.49  
% 23.46/3.49  fof(f5,axiom,(
% 23.46/3.49    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 23.46/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.46/3.49  
% 23.46/3.49  fof(f19,plain,(
% 23.46/3.49    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 23.46/3.49    inference(ennf_transformation,[],[f5])).
% 23.46/3.49  
% 23.46/3.49  fof(f20,plain,(
% 23.46/3.49    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 23.46/3.49    inference(flattening,[],[f19])).
% 23.46/3.49  
% 23.46/3.49  fof(f34,plain,(
% 23.46/3.49    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 23.46/3.49    inference(cnf_transformation,[],[f20])).
% 23.46/3.49  
% 23.46/3.49  fof(f55,plain,(
% 23.46/3.49    ( ! [X2,X0,X1] : (r1_tarski(X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 23.46/3.49    inference(definition_unfolding,[],[f34,f52])).
% 23.46/3.49  
% 23.46/3.49  fof(f46,plain,(
% 23.46/3.49    ~r1_tarski(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))),
% 23.46/3.49    inference(cnf_transformation,[],[f27])).
% 23.46/3.49  
% 23.46/3.49  fof(f58,plain,(
% 23.46/3.49    ~r1_tarski(k10_relat_1(sK2,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k1_setfam_1(k6_enumset1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))))),
% 23.46/3.49    inference(definition_unfolding,[],[f46,f52,f52])).
% 23.46/3.49  
% 23.46/3.49  cnf(c_7,plain,
% 23.46/3.49      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
% 23.46/3.49      inference(cnf_transformation,[],[f57]) ).
% 23.46/3.49  
% 23.46/3.49  cnf(c_4,plain,
% 23.46/3.49      ( r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0) ),
% 23.46/3.49      inference(cnf_transformation,[],[f54]) ).
% 23.46/3.49  
% 23.46/3.49  cnf(c_315,plain,
% 23.46/3.49      ( r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0) = iProver_top ),
% 23.46/3.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 23.46/3.49  
% 23.46/3.49  cnf(c_827,plain,
% 23.46/3.49      ( r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X1) = iProver_top ),
% 23.46/3.49      inference(superposition,[status(thm)],[c_7,c_315]) ).
% 23.46/3.49  
% 23.46/3.49  cnf(c_6,plain,
% 23.46/3.49      ( ~ r1_tarski(X0,X1)
% 23.46/3.49      | k2_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)))) = X1 ),
% 23.46/3.49      inference(cnf_transformation,[],[f56]) ).
% 23.46/3.49  
% 23.46/3.49  cnf(c_313,plain,
% 23.46/3.49      ( k2_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)))) = X1
% 23.46/3.49      | r1_tarski(X0,X1) != iProver_top ),
% 23.46/3.49      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 23.46/3.49  
% 23.46/3.49  cnf(c_1212,plain,
% 23.46/3.49      ( k2_xboole_0(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))))) = X1 ),
% 23.46/3.49      inference(superposition,[status(thm)],[c_827,c_313]) ).
% 23.46/3.49  
% 23.46/3.49  cnf(c_10,negated_conjecture,
% 23.46/3.49      ( v1_relat_1(sK2) ),
% 23.46/3.49      inference(cnf_transformation,[],[f45]) ).
% 23.46/3.49  
% 23.46/3.49  cnf(c_310,plain,
% 23.46/3.49      ( v1_relat_1(sK2) = iProver_top ),
% 23.46/3.49      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 23.46/3.49  
% 23.46/3.49  cnf(c_8,plain,
% 23.46/3.49      ( ~ v1_relat_1(X0)
% 23.46/3.49      | k2_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k10_relat_1(X0,k2_xboole_0(X1,X2)) ),
% 23.46/3.49      inference(cnf_transformation,[],[f44]) ).
% 23.46/3.49  
% 23.46/3.49  cnf(c_312,plain,
% 23.46/3.49      ( k2_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k10_relat_1(X0,k2_xboole_0(X1,X2))
% 23.46/3.49      | v1_relat_1(X0) != iProver_top ),
% 23.46/3.49      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 23.46/3.49  
% 23.46/3.49  cnf(c_1059,plain,
% 23.46/3.49      ( k2_xboole_0(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) = k10_relat_1(sK2,k2_xboole_0(X0,X1)) ),
% 23.46/3.49      inference(superposition,[status(thm)],[c_310,c_312]) ).
% 23.46/3.49  
% 23.46/3.49  cnf(c_1,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f59]) ).
% 23.46/3.49  
% 23.46/3.49  cnf(c_317,plain,
% 23.46/3.49      ( r1_tarski(X0,X0) = iProver_top ),
% 23.46/3.49      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 23.46/3.49  
% 23.46/3.49  cnf(c_3,plain,
% 23.46/3.49      ( r1_tarski(X0,X1) | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
% 23.46/3.49      inference(cnf_transformation,[],[f32]) ).
% 23.46/3.49  
% 23.46/3.49  cnf(c_316,plain,
% 23.46/3.49      ( r1_tarski(X0,X1) = iProver_top
% 23.46/3.49      | r1_tarski(k2_xboole_0(X0,X2),X1) != iProver_top ),
% 23.46/3.49      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 23.46/3.49  
% 23.46/3.49  cnf(c_595,plain,
% 23.46/3.49      ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
% 23.46/3.49      inference(superposition,[status(thm)],[c_317,c_316]) ).
% 23.46/3.49  
% 23.46/3.49  cnf(c_1233,plain,
% 23.46/3.49      ( r1_tarski(k10_relat_1(sK2,X0),k10_relat_1(sK2,k2_xboole_0(X0,X1))) = iProver_top ),
% 23.46/3.49      inference(superposition,[status(thm)],[c_1059,c_595]) ).
% 23.46/3.49  
% 23.46/3.49  cnf(c_24127,plain,
% 23.46/3.49      ( r1_tarski(k10_relat_1(sK2,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),k10_relat_1(sK2,X1)) = iProver_top ),
% 23.46/3.49      inference(superposition,[status(thm)],[c_1212,c_1233]) ).
% 23.46/3.49  
% 23.46/3.49  cnf(c_5,plain,
% 23.46/3.49      ( ~ r1_tarski(X0,X1)
% 23.46/3.49      | ~ r1_tarski(X0,X2)
% 23.46/3.49      | r1_tarski(X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) ),
% 23.46/3.49      inference(cnf_transformation,[],[f55]) ).
% 23.46/3.49  
% 23.46/3.49  cnf(c_314,plain,
% 23.46/3.49      ( r1_tarski(X0,X1) != iProver_top
% 23.46/3.49      | r1_tarski(X0,X2) != iProver_top
% 23.46/3.49      | r1_tarski(X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) = iProver_top ),
% 23.46/3.49      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 23.46/3.49  
% 23.46/3.49  cnf(c_9,negated_conjecture,
% 23.46/3.49      ( ~ r1_tarski(k10_relat_1(sK2,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k1_setfam_1(k6_enumset1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))) ),
% 23.46/3.49      inference(cnf_transformation,[],[f58]) ).
% 23.46/3.49  
% 23.46/3.49  cnf(c_311,plain,
% 23.46/3.49      ( r1_tarski(k10_relat_1(sK2,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k1_setfam_1(k6_enumset1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))) != iProver_top ),
% 23.46/3.49      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 23.46/3.49  
% 23.46/3.49  cnf(c_2276,plain,
% 23.46/3.49      ( r1_tarski(k10_relat_1(sK2,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k10_relat_1(sK2,sK1)) != iProver_top
% 23.46/3.49      | r1_tarski(k10_relat_1(sK2,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k10_relat_1(sK2,sK0)) != iProver_top ),
% 23.46/3.49      inference(superposition,[status(thm)],[c_314,c_311]) ).
% 23.46/3.49  
% 23.46/3.49  cnf(c_48476,plain,
% 23.46/3.49      ( r1_tarski(k10_relat_1(sK2,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k10_relat_1(sK2,sK0)) != iProver_top ),
% 23.46/3.49      inference(superposition,[status(thm)],[c_24127,c_2276]) ).
% 23.46/3.49  
% 23.46/3.49  cnf(c_1208,plain,
% 23.46/3.49      ( k2_xboole_0(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))))) = X0 ),
% 23.46/3.49      inference(superposition,[status(thm)],[c_315,c_313]) ).
% 23.46/3.49  
% 23.46/3.49  cnf(c_10197,plain,
% 23.46/3.49      ( r1_tarski(k10_relat_1(sK2,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),k10_relat_1(sK2,X0)) = iProver_top ),
% 23.46/3.49      inference(superposition,[status(thm)],[c_1208,c_1233]) ).
% 23.46/3.49  
% 23.46/3.49  cnf(c_48902,plain,
% 23.46/3.49      ( $false ),
% 23.46/3.49      inference(forward_subsumption_resolution,[status(thm)],[c_48476,c_10197]) ).
% 23.46/3.49  
% 23.46/3.49  
% 23.46/3.49  % SZS output end CNFRefutation for theBenchmark.p
% 23.46/3.49  
% 23.46/3.49  ------                               Statistics
% 23.46/3.49  
% 23.46/3.49  ------ Selected
% 23.46/3.49  
% 23.46/3.49  total_time:                             2.626
% 23.46/3.49  
%------------------------------------------------------------------------------
