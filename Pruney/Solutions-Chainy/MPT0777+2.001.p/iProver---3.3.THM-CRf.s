%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:54:19 EST 2020

% Result     : Theorem 19.99s
% Output     : CNFRefutation 19.99s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 454 expanded)
%              Number of clauses        :   49 ( 127 expanded)
%              Number of leaves         :   14 ( 111 expanded)
%              Depth                    :   19
%              Number of atoms          :  147 ( 668 expanded)
%              Number of equality atoms :   94 ( 429 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k2_wellord1(X2,k3_xboole_0(X0,X1)) = k2_wellord1(k2_wellord1(X2,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => k2_wellord1(X2,k3_xboole_0(X0,X1)) = k2_wellord1(k2_wellord1(X2,X0),X1) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( k2_wellord1(X2,k3_xboole_0(X0,X1)) != k2_wellord1(k2_wellord1(X2,X0),X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f22,plain,
    ( ? [X0,X1,X2] :
        ( k2_wellord1(X2,k3_xboole_0(X0,X1)) != k2_wellord1(k2_wellord1(X2,X0),X1)
        & v1_relat_1(X2) )
   => ( k2_wellord1(k2_wellord1(sK2,sK0),sK1) != k2_wellord1(sK2,k3_xboole_0(sK0,sK1))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( k2_wellord1(k2_wellord1(sK2,sK0),sK1) != k2_wellord1(sK2,k3_xboole_0(sK0,sK1))
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f22])).

fof(f36,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(k8_relat_1(X0,X1),X0) = k2_wellord1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k7_relat_1(k8_relat_1(X0,X1),X0) = k2_wellord1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k7_relat_1(k8_relat_1(X0,X1),X0) = k2_wellord1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f31,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f1,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f5])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f27,f28])).

fof(f39,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f26,f38])).

fof(f40,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f25,f39])).

fof(f42,plain,(
    ! [X0,X1] : k4_enumset1(X0,X0,X0,X0,X0,X1) = k4_enumset1(X1,X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f24,f40,f40])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f6,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f41,plain,(
    ! [X0,X1] : k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f29,f40])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f33,f41])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f32,f41])).

fof(f37,plain,(
    k2_wellord1(k2_wellord1(sK2,sK0),sK1) != k2_wellord1(sK2,k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f45,plain,(
    k2_wellord1(k2_wellord1(sK2,sK0),sK1) != k2_wellord1(sK2,k1_setfam_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))) ),
    inference(definition_unfolding,[],[f37,f41])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f30,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_8,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_93,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_274,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_93])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(k8_relat_1(X1,X0),X1) = k2_wellord1(X0,X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_95,plain,
    ( ~ v1_relat_1(X0_37)
    | k7_relat_1(k8_relat_1(X0_38,X0_37),X0_38) = k2_wellord1(X0_37,X0_38) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_273,plain,
    ( k7_relat_1(k8_relat_1(X0_38,X0_37),X0_38) = k2_wellord1(X0_37,X0_38)
    | v1_relat_1(X0_37) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_95])).

cnf(c_441,plain,
    ( k7_relat_1(k8_relat_1(X0_38,sK2),X0_38) = k2_wellord1(sK2,X0_38) ),
    inference(superposition,[status(thm)],[c_274,c_273])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k8_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_99,plain,
    ( ~ v1_relat_1(X0_37)
    | v1_relat_1(k8_relat_1(X0_38,X0_37)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_269,plain,
    ( v1_relat_1(X0_37) != iProver_top
    | v1_relat_1(k8_relat_1(X0_38,X0_37)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_99])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | k8_relat_1(X1,k7_relat_1(X0,X2)) = k7_relat_1(k8_relat_1(X1,X0),X2) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_96,plain,
    ( ~ v1_relat_1(X0_37)
    | k8_relat_1(X0_38,k7_relat_1(X0_37,X1_38)) = k7_relat_1(k8_relat_1(X0_38,X0_37),X1_38) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_272,plain,
    ( k8_relat_1(X0_38,k7_relat_1(X0_37,X1_38)) = k7_relat_1(k8_relat_1(X0_38,X0_37),X1_38)
    | v1_relat_1(X0_37) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_96])).

cnf(c_453,plain,
    ( k8_relat_1(X0_38,k7_relat_1(k8_relat_1(X1_38,X0_37),X2_38)) = k7_relat_1(k8_relat_1(X0_38,k8_relat_1(X1_38,X0_37)),X2_38)
    | v1_relat_1(X0_37) != iProver_top ),
    inference(superposition,[status(thm)],[c_269,c_272])).

cnf(c_2381,plain,
    ( k8_relat_1(X0_38,k7_relat_1(k8_relat_1(X1_38,sK2),X2_38)) = k7_relat_1(k8_relat_1(X0_38,k8_relat_1(X1_38,sK2)),X2_38) ),
    inference(superposition,[status(thm)],[c_274,c_453])).

cnf(c_2653,plain,
    ( k7_relat_1(k8_relat_1(X0_38,k8_relat_1(X1_38,sK2)),X1_38) = k8_relat_1(X0_38,k2_wellord1(sK2,X1_38)) ),
    inference(superposition,[status(thm)],[c_441,c_2381])).

cnf(c_0,plain,
    ( k4_enumset1(X0,X0,X0,X0,X0,X1) = k4_enumset1(X1,X1,X1,X1,X1,X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_101,plain,
    ( k4_enumset1(X0_38,X0_38,X0_38,X0_38,X0_38,X1_38) = k4_enumset1(X1_38,X1_38,X1_38,X1_38,X1_38,X0_38) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | k8_relat_1(k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X2)),X0) = k8_relat_1(X1,k8_relat_1(X2,X0)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_97,plain,
    ( ~ v1_relat_1(X0_37)
    | k8_relat_1(k1_setfam_1(k4_enumset1(X0_38,X0_38,X0_38,X0_38,X0_38,X1_38)),X0_37) = k8_relat_1(X0_38,k8_relat_1(X1_38,X0_37)) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_271,plain,
    ( k8_relat_1(k1_setfam_1(k4_enumset1(X0_38,X0_38,X0_38,X0_38,X0_38,X1_38)),X0_37) = k8_relat_1(X0_38,k8_relat_1(X1_38,X0_37))
    | v1_relat_1(X0_37) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_97])).

cnf(c_541,plain,
    ( k8_relat_1(k1_setfam_1(k4_enumset1(X0_38,X0_38,X0_38,X0_38,X0_38,X1_38)),sK2) = k8_relat_1(X0_38,k8_relat_1(X1_38,sK2)) ),
    inference(superposition,[status(thm)],[c_274,c_271])).

cnf(c_1541,plain,
    ( v1_relat_1(k8_relat_1(X0_38,k8_relat_1(X1_38,sK2))) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_541,c_269])).

cnf(c_9,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1854,plain,
    ( v1_relat_1(k8_relat_1(X0_38,k8_relat_1(X1_38,sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1541,c_9])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(X0,k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X2))) = k7_relat_1(k7_relat_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_98,plain,
    ( ~ v1_relat_1(X0_37)
    | k7_relat_1(X0_37,k1_setfam_1(k4_enumset1(X0_38,X0_38,X0_38,X0_38,X0_38,X1_38))) = k7_relat_1(k7_relat_1(X0_37,X0_38),X1_38) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_270,plain,
    ( k7_relat_1(X0_37,k1_setfam_1(k4_enumset1(X0_38,X0_38,X0_38,X0_38,X0_38,X1_38))) = k7_relat_1(k7_relat_1(X0_37,X0_38),X1_38)
    | v1_relat_1(X0_37) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_98])).

cnf(c_1870,plain,
    ( k7_relat_1(k8_relat_1(X0_38,k8_relat_1(X1_38,sK2)),k1_setfam_1(k4_enumset1(X2_38,X2_38,X2_38,X2_38,X2_38,X3_38))) = k7_relat_1(k7_relat_1(k8_relat_1(X0_38,k8_relat_1(X1_38,sK2)),X2_38),X3_38) ),
    inference(superposition,[status(thm)],[c_1854,c_270])).

cnf(c_39229,plain,
    ( k7_relat_1(k8_relat_1(X0_38,k8_relat_1(X1_38,sK2)),k1_setfam_1(k4_enumset1(X2_38,X2_38,X2_38,X2_38,X2_38,X3_38))) = k7_relat_1(k7_relat_1(k8_relat_1(X0_38,k8_relat_1(X1_38,sK2)),X3_38),X2_38) ),
    inference(superposition,[status(thm)],[c_101,c_1870])).

cnf(c_39660,plain,
    ( k7_relat_1(k7_relat_1(k8_relat_1(X0_38,k8_relat_1(X1_38,sK2)),X2_38),X3_38) = k7_relat_1(k7_relat_1(k8_relat_1(X0_38,k8_relat_1(X1_38,sK2)),X3_38),X2_38) ),
    inference(superposition,[status(thm)],[c_39229,c_1870])).

cnf(c_1539,plain,
    ( k8_relat_1(k1_setfam_1(k4_enumset1(X0_38,X0_38,X0_38,X0_38,X0_38,X1_38)),sK2) = k8_relat_1(X1_38,k8_relat_1(X0_38,sK2)) ),
    inference(superposition,[status(thm)],[c_101,c_541])).

cnf(c_1714,plain,
    ( k7_relat_1(k8_relat_1(X0_38,k8_relat_1(X1_38,sK2)),k1_setfam_1(k4_enumset1(X1_38,X1_38,X1_38,X1_38,X1_38,X0_38))) = k2_wellord1(sK2,k1_setfam_1(k4_enumset1(X1_38,X1_38,X1_38,X1_38,X1_38,X0_38))) ),
    inference(superposition,[status(thm)],[c_1539,c_441])).

cnf(c_39646,plain,
    ( k2_wellord1(sK2,k1_setfam_1(k4_enumset1(X0_38,X0_38,X0_38,X0_38,X0_38,X1_38))) = k7_relat_1(k7_relat_1(k8_relat_1(X1_38,k8_relat_1(X0_38,sK2)),X1_38),X0_38) ),
    inference(superposition,[status(thm)],[c_39229,c_1714])).

cnf(c_7,negated_conjecture,
    ( k2_wellord1(k2_wellord1(sK2,sK0),sK1) != k2_wellord1(sK2,k1_setfam_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_94,negated_conjecture,
    ( k2_wellord1(k2_wellord1(sK2,sK0),sK1) != k2_wellord1(sK2,k1_setfam_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_42563,plain,
    ( k7_relat_1(k7_relat_1(k8_relat_1(sK1,k8_relat_1(sK0,sK2)),sK1),sK0) != k2_wellord1(k2_wellord1(sK2,sK0),sK1) ),
    inference(superposition,[status(thm)],[c_39646,c_94])).

cnf(c_42956,plain,
    ( k7_relat_1(k7_relat_1(k8_relat_1(sK1,k8_relat_1(sK0,sK2)),sK0),sK1) != k2_wellord1(k2_wellord1(sK2,sK0),sK1) ),
    inference(superposition,[status(thm)],[c_39660,c_42563])).

cnf(c_73196,plain,
    ( k7_relat_1(k8_relat_1(sK1,k2_wellord1(sK2,sK0)),sK1) != k2_wellord1(k2_wellord1(sK2,sK0),sK1) ),
    inference(superposition,[status(thm)],[c_2653,c_42956])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_100,plain,
    ( ~ v1_relat_1(X0_37)
    | v1_relat_1(k7_relat_1(X0_37,X0_38)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_268,plain,
    ( v1_relat_1(X0_37) != iProver_top
    | v1_relat_1(k7_relat_1(X0_37,X0_38)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_100])).

cnf(c_551,plain,
    ( v1_relat_1(k2_wellord1(sK2,X0_38)) = iProver_top
    | v1_relat_1(k8_relat_1(X0_38,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_441,c_268])).

cnf(c_553,plain,
    ( v1_relat_1(k2_wellord1(sK2,sK0)) = iProver_top
    | v1_relat_1(k8_relat_1(sK0,sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_551])).

cnf(c_399,plain,
    ( ~ v1_relat_1(k2_wellord1(sK2,sK0))
    | k7_relat_1(k8_relat_1(sK1,k2_wellord1(sK2,sK0)),sK1) = k2_wellord1(k2_wellord1(sK2,sK0),sK1) ),
    inference(instantiation,[status(thm)],[c_95])).

cnf(c_400,plain,
    ( k7_relat_1(k8_relat_1(sK1,k2_wellord1(sK2,sK0)),sK1) = k2_wellord1(k2_wellord1(sK2,sK0),sK1)
    | v1_relat_1(k2_wellord1(sK2,sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_399])).

cnf(c_128,plain,
    ( v1_relat_1(X0_37) != iProver_top
    | v1_relat_1(k8_relat_1(X0_38,X0_37)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_99])).

cnf(c_130,plain,
    ( v1_relat_1(k8_relat_1(sK0,sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_128])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_73196,c_553,c_400,c_130,c_9])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:02:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 19.99/3.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.99/3.01  
% 19.99/3.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 19.99/3.01  
% 19.99/3.01  ------  iProver source info
% 19.99/3.01  
% 19.99/3.01  git: date: 2020-06-30 10:37:57 +0100
% 19.99/3.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 19.99/3.01  git: non_committed_changes: false
% 19.99/3.01  git: last_make_outside_of_git: false
% 19.99/3.01  
% 19.99/3.01  ------ 
% 19.99/3.01  ------ Parsing...
% 19.99/3.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 19.99/3.01  
% 19.99/3.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 19.99/3.01  
% 19.99/3.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 19.99/3.01  
% 19.99/3.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.99/3.01  ------ Proving...
% 19.99/3.01  ------ Problem Properties 
% 19.99/3.01  
% 19.99/3.01  
% 19.99/3.01  clauses                                 9
% 19.99/3.01  conjectures                             2
% 19.99/3.01  EPR                                     1
% 19.99/3.01  Horn                                    9
% 19.99/3.01  unary                                   3
% 19.99/3.01  binary                                  6
% 19.99/3.01  lits                                    15
% 19.99/3.01  lits eq                                 6
% 19.99/3.01  fd_pure                                 0
% 19.99/3.01  fd_pseudo                               0
% 19.99/3.01  fd_cond                                 0
% 19.99/3.01  fd_pseudo_cond                          0
% 19.99/3.01  AC symbols                              0
% 19.99/3.01  
% 19.99/3.01  ------ Input Options Time Limit: Unbounded
% 19.99/3.01  
% 19.99/3.01  
% 19.99/3.01  ------ 
% 19.99/3.01  Current options:
% 19.99/3.01  ------ 
% 19.99/3.01  
% 19.99/3.01  
% 19.99/3.01  
% 19.99/3.01  
% 19.99/3.01  ------ Proving...
% 19.99/3.01  
% 19.99/3.01  
% 19.99/3.01  % SZS status Theorem for theBenchmark.p
% 19.99/3.01  
% 19.99/3.01  % SZS output start CNFRefutation for theBenchmark.p
% 19.99/3.01  
% 19.99/3.01  fof(f13,conjecture,(
% 19.99/3.01    ! [X0,X1,X2] : (v1_relat_1(X2) => k2_wellord1(X2,k3_xboole_0(X0,X1)) = k2_wellord1(k2_wellord1(X2,X0),X1))),
% 19.99/3.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.99/3.01  
% 19.99/3.01  fof(f14,negated_conjecture,(
% 19.99/3.01    ~! [X0,X1,X2] : (v1_relat_1(X2) => k2_wellord1(X2,k3_xboole_0(X0,X1)) = k2_wellord1(k2_wellord1(X2,X0),X1))),
% 19.99/3.01    inference(negated_conjecture,[],[f13])).
% 19.99/3.01  
% 19.99/3.01  fof(f21,plain,(
% 19.99/3.01    ? [X0,X1,X2] : (k2_wellord1(X2,k3_xboole_0(X0,X1)) != k2_wellord1(k2_wellord1(X2,X0),X1) & v1_relat_1(X2))),
% 19.99/3.01    inference(ennf_transformation,[],[f14])).
% 19.99/3.01  
% 19.99/3.01  fof(f22,plain,(
% 19.99/3.01    ? [X0,X1,X2] : (k2_wellord1(X2,k3_xboole_0(X0,X1)) != k2_wellord1(k2_wellord1(X2,X0),X1) & v1_relat_1(X2)) => (k2_wellord1(k2_wellord1(sK2,sK0),sK1) != k2_wellord1(sK2,k3_xboole_0(sK0,sK1)) & v1_relat_1(sK2))),
% 19.99/3.01    introduced(choice_axiom,[])).
% 19.99/3.01  
% 19.99/3.01  fof(f23,plain,(
% 19.99/3.01    k2_wellord1(k2_wellord1(sK2,sK0),sK1) != k2_wellord1(sK2,k3_xboole_0(sK0,sK1)) & v1_relat_1(sK2)),
% 19.99/3.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f22])).
% 19.99/3.01  
% 19.99/3.01  fof(f36,plain,(
% 19.99/3.01    v1_relat_1(sK2)),
% 19.99/3.01    inference(cnf_transformation,[],[f23])).
% 19.99/3.01  
% 19.99/3.01  fof(f12,axiom,(
% 19.99/3.01    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(k8_relat_1(X0,X1),X0) = k2_wellord1(X1,X0))),
% 19.99/3.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.99/3.01  
% 19.99/3.01  fof(f20,plain,(
% 19.99/3.01    ! [X0,X1] : (k7_relat_1(k8_relat_1(X0,X1),X0) = k2_wellord1(X1,X0) | ~v1_relat_1(X1))),
% 19.99/3.01    inference(ennf_transformation,[],[f12])).
% 19.99/3.01  
% 19.99/3.01  fof(f35,plain,(
% 19.99/3.01    ( ! [X0,X1] : (k7_relat_1(k8_relat_1(X0,X1),X0) = k2_wellord1(X1,X0) | ~v1_relat_1(X1)) )),
% 19.99/3.01    inference(cnf_transformation,[],[f20])).
% 19.99/3.01  
% 19.99/3.01  fof(f8,axiom,(
% 19.99/3.01    ! [X0,X1] : (v1_relat_1(X1) => v1_relat_1(k8_relat_1(X0,X1)))),
% 19.99/3.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.99/3.01  
% 19.99/3.01  fof(f16,plain,(
% 19.99/3.01    ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1))),
% 19.99/3.01    inference(ennf_transformation,[],[f8])).
% 19.99/3.01  
% 19.99/3.01  fof(f31,plain,(
% 19.99/3.01    ( ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1)) )),
% 19.99/3.01    inference(cnf_transformation,[],[f16])).
% 19.99/3.01  
% 19.99/3.01  fof(f11,axiom,(
% 19.99/3.01    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)))),
% 19.99/3.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.99/3.01  
% 19.99/3.01  fof(f19,plain,(
% 19.99/3.01    ! [X0,X1,X2] : (k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 19.99/3.01    inference(ennf_transformation,[],[f11])).
% 19.99/3.01  
% 19.99/3.01  fof(f34,plain,(
% 19.99/3.01    ( ! [X2,X0,X1] : (k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 19.99/3.01    inference(cnf_transformation,[],[f19])).
% 19.99/3.01  
% 19.99/3.01  fof(f1,axiom,(
% 19.99/3.01    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 19.99/3.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.99/3.01  
% 19.99/3.01  fof(f24,plain,(
% 19.99/3.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 19.99/3.01    inference(cnf_transformation,[],[f1])).
% 19.99/3.01  
% 19.99/3.01  fof(f2,axiom,(
% 19.99/3.01    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 19.99/3.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.99/3.01  
% 19.99/3.01  fof(f25,plain,(
% 19.99/3.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 19.99/3.01    inference(cnf_transformation,[],[f2])).
% 19.99/3.01  
% 19.99/3.01  fof(f3,axiom,(
% 19.99/3.01    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 19.99/3.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.99/3.01  
% 19.99/3.01  fof(f26,plain,(
% 19.99/3.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 19.99/3.01    inference(cnf_transformation,[],[f3])).
% 19.99/3.01  
% 19.99/3.01  fof(f4,axiom,(
% 19.99/3.01    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 19.99/3.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.99/3.01  
% 19.99/3.01  fof(f27,plain,(
% 19.99/3.01    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 19.99/3.01    inference(cnf_transformation,[],[f4])).
% 19.99/3.01  
% 19.99/3.01  fof(f5,axiom,(
% 19.99/3.01    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 19.99/3.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.99/3.01  
% 19.99/3.01  fof(f28,plain,(
% 19.99/3.01    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 19.99/3.01    inference(cnf_transformation,[],[f5])).
% 19.99/3.01  
% 19.99/3.01  fof(f38,plain,(
% 19.99/3.01    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 19.99/3.01    inference(definition_unfolding,[],[f27,f28])).
% 19.99/3.01  
% 19.99/3.01  fof(f39,plain,(
% 19.99/3.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 19.99/3.01    inference(definition_unfolding,[],[f26,f38])).
% 19.99/3.01  
% 19.99/3.01  fof(f40,plain,(
% 19.99/3.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1)) )),
% 19.99/3.01    inference(definition_unfolding,[],[f25,f39])).
% 19.99/3.01  
% 19.99/3.01  fof(f42,plain,(
% 19.99/3.01    ( ! [X0,X1] : (k4_enumset1(X0,X0,X0,X0,X0,X1) = k4_enumset1(X1,X1,X1,X1,X1,X0)) )),
% 19.99/3.01    inference(definition_unfolding,[],[f24,f40,f40])).
% 19.99/3.01  
% 19.99/3.01  fof(f10,axiom,(
% 19.99/3.01    ! [X0,X1,X2] : (v1_relat_1(X2) => k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2))),
% 19.99/3.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.99/3.01  
% 19.99/3.01  fof(f18,plain,(
% 19.99/3.01    ! [X0,X1,X2] : (k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2) | ~v1_relat_1(X2))),
% 19.99/3.01    inference(ennf_transformation,[],[f10])).
% 19.99/3.01  
% 19.99/3.01  fof(f33,plain,(
% 19.99/3.01    ( ! [X2,X0,X1] : (k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2) | ~v1_relat_1(X2)) )),
% 19.99/3.01    inference(cnf_transformation,[],[f18])).
% 19.99/3.01  
% 19.99/3.01  fof(f6,axiom,(
% 19.99/3.01    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 19.99/3.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.99/3.01  
% 19.99/3.01  fof(f29,plain,(
% 19.99/3.01    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 19.99/3.01    inference(cnf_transformation,[],[f6])).
% 19.99/3.01  
% 19.99/3.01  fof(f41,plain,(
% 19.99/3.01    ( ! [X0,X1] : (k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)) = k3_xboole_0(X0,X1)) )),
% 19.99/3.01    inference(definition_unfolding,[],[f29,f40])).
% 19.99/3.01  
% 19.99/3.01  fof(f44,plain,(
% 19.99/3.01    ( ! [X2,X0,X1] : (k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)),X2) | ~v1_relat_1(X2)) )),
% 19.99/3.01    inference(definition_unfolding,[],[f33,f41])).
% 19.99/3.01  
% 19.99/3.01  fof(f9,axiom,(
% 19.99/3.01    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1))),
% 19.99/3.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.99/3.01  
% 19.99/3.01  fof(f17,plain,(
% 19.99/3.01    ! [X0,X1,X2] : (k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2))),
% 19.99/3.01    inference(ennf_transformation,[],[f9])).
% 19.99/3.01  
% 19.99/3.01  fof(f32,plain,(
% 19.99/3.01    ( ! [X2,X0,X1] : (k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 19.99/3.01    inference(cnf_transformation,[],[f17])).
% 19.99/3.01  
% 19.99/3.01  fof(f43,plain,(
% 19.99/3.01    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))) | ~v1_relat_1(X2)) )),
% 19.99/3.01    inference(definition_unfolding,[],[f32,f41])).
% 19.99/3.01  
% 19.99/3.01  fof(f37,plain,(
% 19.99/3.01    k2_wellord1(k2_wellord1(sK2,sK0),sK1) != k2_wellord1(sK2,k3_xboole_0(sK0,sK1))),
% 19.99/3.01    inference(cnf_transformation,[],[f23])).
% 19.99/3.01  
% 19.99/3.01  fof(f45,plain,(
% 19.99/3.01    k2_wellord1(k2_wellord1(sK2,sK0),sK1) != k2_wellord1(sK2,k1_setfam_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1)))),
% 19.99/3.01    inference(definition_unfolding,[],[f37,f41])).
% 19.99/3.01  
% 19.99/3.01  fof(f7,axiom,(
% 19.99/3.01    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 19.99/3.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.99/3.01  
% 19.99/3.01  fof(f15,plain,(
% 19.99/3.01    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 19.99/3.01    inference(ennf_transformation,[],[f7])).
% 19.99/3.01  
% 19.99/3.01  fof(f30,plain,(
% 19.99/3.01    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 19.99/3.01    inference(cnf_transformation,[],[f15])).
% 19.99/3.01  
% 19.99/3.01  cnf(c_8,negated_conjecture,
% 19.99/3.01      ( v1_relat_1(sK2) ),
% 19.99/3.01      inference(cnf_transformation,[],[f36]) ).
% 19.99/3.01  
% 19.99/3.01  cnf(c_93,negated_conjecture,
% 19.99/3.01      ( v1_relat_1(sK2) ),
% 19.99/3.01      inference(subtyping,[status(esa)],[c_8]) ).
% 19.99/3.01  
% 19.99/3.01  cnf(c_274,plain,
% 19.99/3.01      ( v1_relat_1(sK2) = iProver_top ),
% 19.99/3.01      inference(predicate_to_equality,[status(thm)],[c_93]) ).
% 19.99/3.01  
% 19.99/3.01  cnf(c_6,plain,
% 19.99/3.01      ( ~ v1_relat_1(X0)
% 19.99/3.01      | k7_relat_1(k8_relat_1(X1,X0),X1) = k2_wellord1(X0,X1) ),
% 19.99/3.01      inference(cnf_transformation,[],[f35]) ).
% 19.99/3.01  
% 19.99/3.01  cnf(c_95,plain,
% 19.99/3.01      ( ~ v1_relat_1(X0_37)
% 19.99/3.01      | k7_relat_1(k8_relat_1(X0_38,X0_37),X0_38) = k2_wellord1(X0_37,X0_38) ),
% 19.99/3.01      inference(subtyping,[status(esa)],[c_6]) ).
% 19.99/3.01  
% 19.99/3.01  cnf(c_273,plain,
% 19.99/3.01      ( k7_relat_1(k8_relat_1(X0_38,X0_37),X0_38) = k2_wellord1(X0_37,X0_38)
% 19.99/3.01      | v1_relat_1(X0_37) != iProver_top ),
% 19.99/3.01      inference(predicate_to_equality,[status(thm)],[c_95]) ).
% 19.99/3.01  
% 19.99/3.01  cnf(c_441,plain,
% 19.99/3.01      ( k7_relat_1(k8_relat_1(X0_38,sK2),X0_38) = k2_wellord1(sK2,X0_38) ),
% 19.99/3.01      inference(superposition,[status(thm)],[c_274,c_273]) ).
% 19.99/3.01  
% 19.99/3.01  cnf(c_2,plain,
% 19.99/3.01      ( ~ v1_relat_1(X0) | v1_relat_1(k8_relat_1(X1,X0)) ),
% 19.99/3.01      inference(cnf_transformation,[],[f31]) ).
% 19.99/3.01  
% 19.99/3.01  cnf(c_99,plain,
% 19.99/3.01      ( ~ v1_relat_1(X0_37) | v1_relat_1(k8_relat_1(X0_38,X0_37)) ),
% 19.99/3.01      inference(subtyping,[status(esa)],[c_2]) ).
% 19.99/3.01  
% 19.99/3.01  cnf(c_269,plain,
% 19.99/3.01      ( v1_relat_1(X0_37) != iProver_top
% 19.99/3.01      | v1_relat_1(k8_relat_1(X0_38,X0_37)) = iProver_top ),
% 19.99/3.01      inference(predicate_to_equality,[status(thm)],[c_99]) ).
% 19.99/3.01  
% 19.99/3.01  cnf(c_5,plain,
% 19.99/3.01      ( ~ v1_relat_1(X0)
% 19.99/3.01      | k8_relat_1(X1,k7_relat_1(X0,X2)) = k7_relat_1(k8_relat_1(X1,X0),X2) ),
% 19.99/3.01      inference(cnf_transformation,[],[f34]) ).
% 19.99/3.01  
% 19.99/3.01  cnf(c_96,plain,
% 19.99/3.01      ( ~ v1_relat_1(X0_37)
% 19.99/3.01      | k8_relat_1(X0_38,k7_relat_1(X0_37,X1_38)) = k7_relat_1(k8_relat_1(X0_38,X0_37),X1_38) ),
% 19.99/3.01      inference(subtyping,[status(esa)],[c_5]) ).
% 19.99/3.01  
% 19.99/3.01  cnf(c_272,plain,
% 19.99/3.01      ( k8_relat_1(X0_38,k7_relat_1(X0_37,X1_38)) = k7_relat_1(k8_relat_1(X0_38,X0_37),X1_38)
% 19.99/3.01      | v1_relat_1(X0_37) != iProver_top ),
% 19.99/3.01      inference(predicate_to_equality,[status(thm)],[c_96]) ).
% 19.99/3.01  
% 19.99/3.01  cnf(c_453,plain,
% 19.99/3.01      ( k8_relat_1(X0_38,k7_relat_1(k8_relat_1(X1_38,X0_37),X2_38)) = k7_relat_1(k8_relat_1(X0_38,k8_relat_1(X1_38,X0_37)),X2_38)
% 19.99/3.01      | v1_relat_1(X0_37) != iProver_top ),
% 19.99/3.01      inference(superposition,[status(thm)],[c_269,c_272]) ).
% 19.99/3.01  
% 19.99/3.01  cnf(c_2381,plain,
% 19.99/3.01      ( k8_relat_1(X0_38,k7_relat_1(k8_relat_1(X1_38,sK2),X2_38)) = k7_relat_1(k8_relat_1(X0_38,k8_relat_1(X1_38,sK2)),X2_38) ),
% 19.99/3.01      inference(superposition,[status(thm)],[c_274,c_453]) ).
% 19.99/3.01  
% 19.99/3.01  cnf(c_2653,plain,
% 19.99/3.01      ( k7_relat_1(k8_relat_1(X0_38,k8_relat_1(X1_38,sK2)),X1_38) = k8_relat_1(X0_38,k2_wellord1(sK2,X1_38)) ),
% 19.99/3.01      inference(superposition,[status(thm)],[c_441,c_2381]) ).
% 19.99/3.01  
% 19.99/3.01  cnf(c_0,plain,
% 19.99/3.01      ( k4_enumset1(X0,X0,X0,X0,X0,X1) = k4_enumset1(X1,X1,X1,X1,X1,X0) ),
% 19.99/3.01      inference(cnf_transformation,[],[f42]) ).
% 19.99/3.01  
% 19.99/3.01  cnf(c_101,plain,
% 19.99/3.01      ( k4_enumset1(X0_38,X0_38,X0_38,X0_38,X0_38,X1_38) = k4_enumset1(X1_38,X1_38,X1_38,X1_38,X1_38,X0_38) ),
% 19.99/3.01      inference(subtyping,[status(esa)],[c_0]) ).
% 19.99/3.01  
% 19.99/3.01  cnf(c_4,plain,
% 19.99/3.01      ( ~ v1_relat_1(X0)
% 19.99/3.01      | k8_relat_1(k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X2)),X0) = k8_relat_1(X1,k8_relat_1(X2,X0)) ),
% 19.99/3.01      inference(cnf_transformation,[],[f44]) ).
% 19.99/3.01  
% 19.99/3.01  cnf(c_97,plain,
% 19.99/3.01      ( ~ v1_relat_1(X0_37)
% 19.99/3.01      | k8_relat_1(k1_setfam_1(k4_enumset1(X0_38,X0_38,X0_38,X0_38,X0_38,X1_38)),X0_37) = k8_relat_1(X0_38,k8_relat_1(X1_38,X0_37)) ),
% 19.99/3.01      inference(subtyping,[status(esa)],[c_4]) ).
% 19.99/3.01  
% 19.99/3.01  cnf(c_271,plain,
% 19.99/3.01      ( k8_relat_1(k1_setfam_1(k4_enumset1(X0_38,X0_38,X0_38,X0_38,X0_38,X1_38)),X0_37) = k8_relat_1(X0_38,k8_relat_1(X1_38,X0_37))
% 19.99/3.01      | v1_relat_1(X0_37) != iProver_top ),
% 19.99/3.01      inference(predicate_to_equality,[status(thm)],[c_97]) ).
% 19.99/3.01  
% 19.99/3.01  cnf(c_541,plain,
% 19.99/3.01      ( k8_relat_1(k1_setfam_1(k4_enumset1(X0_38,X0_38,X0_38,X0_38,X0_38,X1_38)),sK2) = k8_relat_1(X0_38,k8_relat_1(X1_38,sK2)) ),
% 19.99/3.01      inference(superposition,[status(thm)],[c_274,c_271]) ).
% 19.99/3.01  
% 19.99/3.01  cnf(c_1541,plain,
% 19.99/3.01      ( v1_relat_1(k8_relat_1(X0_38,k8_relat_1(X1_38,sK2))) = iProver_top
% 19.99/3.01      | v1_relat_1(sK2) != iProver_top ),
% 19.99/3.01      inference(superposition,[status(thm)],[c_541,c_269]) ).
% 19.99/3.01  
% 19.99/3.01  cnf(c_9,plain,
% 19.99/3.01      ( v1_relat_1(sK2) = iProver_top ),
% 19.99/3.01      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 19.99/3.01  
% 19.99/3.01  cnf(c_1854,plain,
% 19.99/3.01      ( v1_relat_1(k8_relat_1(X0_38,k8_relat_1(X1_38,sK2))) = iProver_top ),
% 19.99/3.01      inference(global_propositional_subsumption,
% 19.99/3.01                [status(thm)],
% 19.99/3.01                [c_1541,c_9]) ).
% 19.99/3.01  
% 19.99/3.01  cnf(c_3,plain,
% 19.99/3.01      ( ~ v1_relat_1(X0)
% 19.99/3.01      | k7_relat_1(X0,k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X2))) = k7_relat_1(k7_relat_1(X0,X1),X2) ),
% 19.99/3.01      inference(cnf_transformation,[],[f43]) ).
% 19.99/3.01  
% 19.99/3.01  cnf(c_98,plain,
% 19.99/3.01      ( ~ v1_relat_1(X0_37)
% 19.99/3.01      | k7_relat_1(X0_37,k1_setfam_1(k4_enumset1(X0_38,X0_38,X0_38,X0_38,X0_38,X1_38))) = k7_relat_1(k7_relat_1(X0_37,X0_38),X1_38) ),
% 19.99/3.01      inference(subtyping,[status(esa)],[c_3]) ).
% 19.99/3.01  
% 19.99/3.01  cnf(c_270,plain,
% 19.99/3.01      ( k7_relat_1(X0_37,k1_setfam_1(k4_enumset1(X0_38,X0_38,X0_38,X0_38,X0_38,X1_38))) = k7_relat_1(k7_relat_1(X0_37,X0_38),X1_38)
% 19.99/3.01      | v1_relat_1(X0_37) != iProver_top ),
% 19.99/3.01      inference(predicate_to_equality,[status(thm)],[c_98]) ).
% 19.99/3.01  
% 19.99/3.01  cnf(c_1870,plain,
% 19.99/3.01      ( k7_relat_1(k8_relat_1(X0_38,k8_relat_1(X1_38,sK2)),k1_setfam_1(k4_enumset1(X2_38,X2_38,X2_38,X2_38,X2_38,X3_38))) = k7_relat_1(k7_relat_1(k8_relat_1(X0_38,k8_relat_1(X1_38,sK2)),X2_38),X3_38) ),
% 19.99/3.01      inference(superposition,[status(thm)],[c_1854,c_270]) ).
% 19.99/3.01  
% 19.99/3.01  cnf(c_39229,plain,
% 19.99/3.01      ( k7_relat_1(k8_relat_1(X0_38,k8_relat_1(X1_38,sK2)),k1_setfam_1(k4_enumset1(X2_38,X2_38,X2_38,X2_38,X2_38,X3_38))) = k7_relat_1(k7_relat_1(k8_relat_1(X0_38,k8_relat_1(X1_38,sK2)),X3_38),X2_38) ),
% 19.99/3.01      inference(superposition,[status(thm)],[c_101,c_1870]) ).
% 19.99/3.01  
% 19.99/3.01  cnf(c_39660,plain,
% 19.99/3.01      ( k7_relat_1(k7_relat_1(k8_relat_1(X0_38,k8_relat_1(X1_38,sK2)),X2_38),X3_38) = k7_relat_1(k7_relat_1(k8_relat_1(X0_38,k8_relat_1(X1_38,sK2)),X3_38),X2_38) ),
% 19.99/3.01      inference(superposition,[status(thm)],[c_39229,c_1870]) ).
% 19.99/3.01  
% 19.99/3.01  cnf(c_1539,plain,
% 19.99/3.01      ( k8_relat_1(k1_setfam_1(k4_enumset1(X0_38,X0_38,X0_38,X0_38,X0_38,X1_38)),sK2) = k8_relat_1(X1_38,k8_relat_1(X0_38,sK2)) ),
% 19.99/3.01      inference(superposition,[status(thm)],[c_101,c_541]) ).
% 19.99/3.01  
% 19.99/3.01  cnf(c_1714,plain,
% 19.99/3.01      ( k7_relat_1(k8_relat_1(X0_38,k8_relat_1(X1_38,sK2)),k1_setfam_1(k4_enumset1(X1_38,X1_38,X1_38,X1_38,X1_38,X0_38))) = k2_wellord1(sK2,k1_setfam_1(k4_enumset1(X1_38,X1_38,X1_38,X1_38,X1_38,X0_38))) ),
% 19.99/3.01      inference(superposition,[status(thm)],[c_1539,c_441]) ).
% 19.99/3.01  
% 19.99/3.01  cnf(c_39646,plain,
% 19.99/3.01      ( k2_wellord1(sK2,k1_setfam_1(k4_enumset1(X0_38,X0_38,X0_38,X0_38,X0_38,X1_38))) = k7_relat_1(k7_relat_1(k8_relat_1(X1_38,k8_relat_1(X0_38,sK2)),X1_38),X0_38) ),
% 19.99/3.01      inference(superposition,[status(thm)],[c_39229,c_1714]) ).
% 19.99/3.01  
% 19.99/3.01  cnf(c_7,negated_conjecture,
% 19.99/3.01      ( k2_wellord1(k2_wellord1(sK2,sK0),sK1) != k2_wellord1(sK2,k1_setfam_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))) ),
% 19.99/3.01      inference(cnf_transformation,[],[f45]) ).
% 19.99/3.01  
% 19.99/3.01  cnf(c_94,negated_conjecture,
% 19.99/3.01      ( k2_wellord1(k2_wellord1(sK2,sK0),sK1) != k2_wellord1(sK2,k1_setfam_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))) ),
% 19.99/3.01      inference(subtyping,[status(esa)],[c_7]) ).
% 19.99/3.01  
% 19.99/3.01  cnf(c_42563,plain,
% 19.99/3.01      ( k7_relat_1(k7_relat_1(k8_relat_1(sK1,k8_relat_1(sK0,sK2)),sK1),sK0) != k2_wellord1(k2_wellord1(sK2,sK0),sK1) ),
% 19.99/3.01      inference(superposition,[status(thm)],[c_39646,c_94]) ).
% 19.99/3.01  
% 19.99/3.01  cnf(c_42956,plain,
% 19.99/3.01      ( k7_relat_1(k7_relat_1(k8_relat_1(sK1,k8_relat_1(sK0,sK2)),sK0),sK1) != k2_wellord1(k2_wellord1(sK2,sK0),sK1) ),
% 19.99/3.01      inference(superposition,[status(thm)],[c_39660,c_42563]) ).
% 19.99/3.01  
% 19.99/3.01  cnf(c_73196,plain,
% 19.99/3.01      ( k7_relat_1(k8_relat_1(sK1,k2_wellord1(sK2,sK0)),sK1) != k2_wellord1(k2_wellord1(sK2,sK0),sK1) ),
% 19.99/3.01      inference(superposition,[status(thm)],[c_2653,c_42956]) ).
% 19.99/3.01  
% 19.99/3.01  cnf(c_1,plain,
% 19.99/3.01      ( ~ v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1)) ),
% 19.99/3.01      inference(cnf_transformation,[],[f30]) ).
% 19.99/3.01  
% 19.99/3.01  cnf(c_100,plain,
% 19.99/3.01      ( ~ v1_relat_1(X0_37) | v1_relat_1(k7_relat_1(X0_37,X0_38)) ),
% 19.99/3.01      inference(subtyping,[status(esa)],[c_1]) ).
% 19.99/3.01  
% 19.99/3.01  cnf(c_268,plain,
% 19.99/3.01      ( v1_relat_1(X0_37) != iProver_top
% 19.99/3.01      | v1_relat_1(k7_relat_1(X0_37,X0_38)) = iProver_top ),
% 19.99/3.01      inference(predicate_to_equality,[status(thm)],[c_100]) ).
% 19.99/3.01  
% 19.99/3.01  cnf(c_551,plain,
% 19.99/3.01      ( v1_relat_1(k2_wellord1(sK2,X0_38)) = iProver_top
% 19.99/3.01      | v1_relat_1(k8_relat_1(X0_38,sK2)) != iProver_top ),
% 19.99/3.01      inference(superposition,[status(thm)],[c_441,c_268]) ).
% 19.99/3.01  
% 19.99/3.01  cnf(c_553,plain,
% 19.99/3.01      ( v1_relat_1(k2_wellord1(sK2,sK0)) = iProver_top
% 19.99/3.01      | v1_relat_1(k8_relat_1(sK0,sK2)) != iProver_top ),
% 19.99/3.01      inference(instantiation,[status(thm)],[c_551]) ).
% 19.99/3.01  
% 19.99/3.01  cnf(c_399,plain,
% 19.99/3.01      ( ~ v1_relat_1(k2_wellord1(sK2,sK0))
% 19.99/3.01      | k7_relat_1(k8_relat_1(sK1,k2_wellord1(sK2,sK0)),sK1) = k2_wellord1(k2_wellord1(sK2,sK0),sK1) ),
% 19.99/3.01      inference(instantiation,[status(thm)],[c_95]) ).
% 19.99/3.01  
% 19.99/3.01  cnf(c_400,plain,
% 19.99/3.01      ( k7_relat_1(k8_relat_1(sK1,k2_wellord1(sK2,sK0)),sK1) = k2_wellord1(k2_wellord1(sK2,sK0),sK1)
% 19.99/3.01      | v1_relat_1(k2_wellord1(sK2,sK0)) != iProver_top ),
% 19.99/3.01      inference(predicate_to_equality,[status(thm)],[c_399]) ).
% 19.99/3.01  
% 19.99/3.01  cnf(c_128,plain,
% 19.99/3.01      ( v1_relat_1(X0_37) != iProver_top
% 19.99/3.01      | v1_relat_1(k8_relat_1(X0_38,X0_37)) = iProver_top ),
% 19.99/3.01      inference(predicate_to_equality,[status(thm)],[c_99]) ).
% 19.99/3.01  
% 19.99/3.01  cnf(c_130,plain,
% 19.99/3.01      ( v1_relat_1(k8_relat_1(sK0,sK2)) = iProver_top
% 19.99/3.01      | v1_relat_1(sK2) != iProver_top ),
% 19.99/3.01      inference(instantiation,[status(thm)],[c_128]) ).
% 19.99/3.01  
% 19.99/3.01  cnf(contradiction,plain,
% 19.99/3.01      ( $false ),
% 19.99/3.01      inference(minisat,[status(thm)],[c_73196,c_553,c_400,c_130,c_9]) ).
% 19.99/3.01  
% 19.99/3.01  
% 19.99/3.01  % SZS output end CNFRefutation for theBenchmark.p
% 19.99/3.01  
% 19.99/3.01  ------                               Statistics
% 19.99/3.01  
% 19.99/3.01  ------ Selected
% 19.99/3.01  
% 19.99/3.01  total_time:                             2.497
% 19.99/3.01  
%------------------------------------------------------------------------------
