%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:46:39 EST 2020

% Result     : Theorem 3.74s
% Output     : CNFRefutation 3.74s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 312 expanded)
%              Number of clauses        :   48 ( 134 expanded)
%              Number of leaves         :   11 (  60 expanded)
%              Depth                    :   14
%              Number of atoms          :  149 ( 554 expanded)
%              Number of equality atoms :   64 ( 180 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f36,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(definition_unfolding,[],[f24,f25,f25])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f20,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f20])).

fof(f31,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f33,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f26,f25])).

fof(f34,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f22,f33])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f27,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f12])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k1_setfam_1(k1_enumset1(X1,X1,X2)))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f23,f33])).

fof(f32,plain,(
    ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f21])).

fof(f37,plain,(
    ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k1_setfam_1(k1_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))) ),
    inference(definition_unfolding,[],[f32,f33,f33])).

cnf(c_2,plain,
    ( k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_105,plain,
    ( k1_enumset1(X0_39,X0_39,X1_39) = k1_enumset1(X1_39,X1_39,X0_39) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_8,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_99,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_9523,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_99])).

cnf(c_0,plain,
    ( r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_107,plain,
    ( r1_tarski(k1_setfam_1(k1_enumset1(X0_39,X0_39,X1_39)),X0_39) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_9517,plain,
    ( r1_tarski(k1_setfam_1(k1_enumset1(X0_39,X0_39,X1_39)),X0_39) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_107])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X2)
    | k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_103,plain,
    ( ~ r1_tarski(X0_39,X1_39)
    | ~ v1_relat_1(X0_38)
    | k7_relat_1(k7_relat_1(X0_38,X1_39),X0_39) = k7_relat_1(X0_38,X0_39) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_9520,plain,
    ( k7_relat_1(k7_relat_1(X0_38,X0_39),X1_39) = k7_relat_1(X0_38,X1_39)
    | r1_tarski(X1_39,X0_39) != iProver_top
    | v1_relat_1(X0_38) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_103])).

cnf(c_9675,plain,
    ( k7_relat_1(k7_relat_1(X0_38,X0_39),k1_setfam_1(k1_enumset1(X0_39,X0_39,X1_39))) = k7_relat_1(X0_38,k1_setfam_1(k1_enumset1(X0_39,X0_39,X1_39)))
    | v1_relat_1(X0_38) != iProver_top ),
    inference(superposition,[status(thm)],[c_9517,c_9520])).

cnf(c_10565,plain,
    ( k7_relat_1(k7_relat_1(sK2,X0_39),k1_setfam_1(k1_enumset1(X0_39,X0_39,X1_39))) = k7_relat_1(sK2,k1_setfam_1(k1_enumset1(X0_39,X0_39,X1_39))) ),
    inference(superposition,[status(thm)],[c_9523,c_9675])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_104,plain,
    ( ~ v1_relat_1(X0_38)
    | v1_relat_1(k7_relat_1(X0_38,X0_39)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_9519,plain,
    ( v1_relat_1(X0_38) != iProver_top
    | v1_relat_1(k7_relat_1(X0_38,X0_39)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_104])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_101,plain,
    ( ~ v1_relat_1(X0_38)
    | k2_relat_1(k7_relat_1(X0_38,X0_39)) = k9_relat_1(X0_38,X0_39) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_9522,plain,
    ( k2_relat_1(k7_relat_1(X0_38,X0_39)) = k9_relat_1(X0_38,X0_39)
    | v1_relat_1(X0_38) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_101])).

cnf(c_9635,plain,
    ( k2_relat_1(k7_relat_1(k7_relat_1(X0_38,X0_39),X1_39)) = k9_relat_1(k7_relat_1(X0_38,X0_39),X1_39)
    | v1_relat_1(X0_38) != iProver_top ),
    inference(superposition,[status(thm)],[c_9519,c_9522])).

cnf(c_9729,plain,
    ( k2_relat_1(k7_relat_1(k7_relat_1(sK2,X0_39),X1_39)) = k9_relat_1(k7_relat_1(sK2,X0_39),X1_39) ),
    inference(superposition,[status(thm)],[c_9523,c_9635])).

cnf(c_10605,plain,
    ( k9_relat_1(k7_relat_1(sK2,X0_39),k1_setfam_1(k1_enumset1(X0_39,X0_39,X1_39))) = k2_relat_1(k7_relat_1(sK2,k1_setfam_1(k1_enumset1(X0_39,X0_39,X1_39)))) ),
    inference(superposition,[status(thm)],[c_10565,c_9729])).

cnf(c_9634,plain,
    ( k2_relat_1(k7_relat_1(sK2,X0_39)) = k9_relat_1(sK2,X0_39) ),
    inference(superposition,[status(thm)],[c_9523,c_9522])).

cnf(c_10615,plain,
    ( k9_relat_1(k7_relat_1(sK2,X0_39),k1_setfam_1(k1_enumset1(X0_39,X0_39,X1_39))) = k9_relat_1(sK2,k1_setfam_1(k1_enumset1(X0_39,X0_39,X1_39))) ),
    inference(demodulation,[status(thm)],[c_10605,c_9634])).

cnf(c_5,plain,
    ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_102,plain,
    ( r1_tarski(k9_relat_1(X0_38,X0_39),k2_relat_1(X0_38))
    | ~ v1_relat_1(X0_38) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_9521,plain,
    ( r1_tarski(k9_relat_1(X0_38,X0_39),k2_relat_1(X0_38)) = iProver_top
    | v1_relat_1(X0_38) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_102])).

cnf(c_9713,plain,
    ( r1_tarski(k9_relat_1(k7_relat_1(sK2,X0_39),X1_39),k9_relat_1(sK2,X0_39)) = iProver_top
    | v1_relat_1(k7_relat_1(sK2,X0_39)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9634,c_9521])).

cnf(c_9,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2498,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_99])).

cnf(c_2497,plain,
    ( k2_relat_1(k7_relat_1(X0_38,X0_39)) = k9_relat_1(X0_38,X0_39)
    | v1_relat_1(X0_38) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_101])).

cnf(c_2700,plain,
    ( k2_relat_1(k7_relat_1(sK2,X0_39)) = k9_relat_1(sK2,X0_39) ),
    inference(superposition,[status(thm)],[c_2498,c_2497])).

cnf(c_2496,plain,
    ( r1_tarski(k9_relat_1(X0_38,X0_39),k2_relat_1(X0_38)) = iProver_top
    | v1_relat_1(X0_38) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_102])).

cnf(c_2721,plain,
    ( r1_tarski(k9_relat_1(k7_relat_1(sK2,X0_39),X1_39),k9_relat_1(sK2,X0_39)) = iProver_top
    | v1_relat_1(k7_relat_1(sK2,X0_39)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2700,c_2496])).

cnf(c_8617,plain,
    ( v1_relat_1(k7_relat_1(sK2,X0_39))
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_104])).

cnf(c_8618,plain,
    ( v1_relat_1(k7_relat_1(sK2,X0_39)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8617])).

cnf(c_9767,plain,
    ( r1_tarski(k9_relat_1(k7_relat_1(sK2,X0_39),X1_39),k9_relat_1(sK2,X0_39)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9713,c_9,c_2721,c_8618])).

cnf(c_10748,plain,
    ( r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(X0_39,X0_39,X1_39))),k9_relat_1(sK2,X0_39)) = iProver_top ),
    inference(superposition,[status(thm)],[c_10615,c_9767])).

cnf(c_11010,plain,
    ( r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(X0_39,X0_39,X1_39))),k9_relat_1(sK2,X1_39)) = iProver_top ),
    inference(superposition,[status(thm)],[c_105,c_10748])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k1_setfam_1(k1_enumset1(X2,X2,X1))) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_106,plain,
    ( ~ r1_tarski(X0_39,X1_39)
    | ~ r1_tarski(X0_39,X2_39)
    | r1_tarski(X0_39,k1_setfam_1(k1_enumset1(X2_39,X2_39,X1_39))) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_9518,plain,
    ( r1_tarski(X0_39,X1_39) != iProver_top
    | r1_tarski(X0_39,X2_39) != iProver_top
    | r1_tarski(X0_39,k1_setfam_1(k1_enumset1(X2_39,X2_39,X1_39))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_106])).

cnf(c_7,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k1_setfam_1(k1_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_100,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k1_setfam_1(k1_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_9524,plain,
    ( r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k1_setfam_1(k1_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_100])).

cnf(c_9656,plain,
    ( r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k9_relat_1(sK2,sK1)) != iProver_top
    | r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k9_relat_1(sK2,sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9518,c_9524])).

cnf(c_11232,plain,
    ( r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k9_relat_1(sK2,sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11010,c_9656])).

cnf(c_11529,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_11232,c_10748])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:23:07 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.12/0.35  % Running in FOF mode
% 3.74/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.74/1.01  
% 3.74/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.74/1.01  
% 3.74/1.01  ------  iProver source info
% 3.74/1.01  
% 3.74/1.01  git: date: 2020-06-30 10:37:57 +0100
% 3.74/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.74/1.01  git: non_committed_changes: false
% 3.74/1.01  git: last_make_outside_of_git: false
% 3.74/1.01  
% 3.74/1.01  ------ 
% 3.74/1.01  ------ Parsing...
% 3.74/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.74/1.01  
% 3.74/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.74/1.01  
% 3.74/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.74/1.01  
% 3.74/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.74/1.01  ------ Proving...
% 3.74/1.01  ------ Problem Properties 
% 3.74/1.01  
% 3.74/1.01  
% 3.74/1.01  clauses                                 9
% 3.74/1.01  conjectures                             2
% 3.74/1.01  EPR                                     1
% 3.74/1.01  Horn                                    9
% 3.74/1.01  unary                                   4
% 3.74/1.01  binary                                  3
% 3.74/1.01  lits                                    16
% 3.74/1.01  lits eq                                 3
% 3.74/1.01  fd_pure                                 0
% 3.74/1.01  fd_pseudo                               0
% 3.74/1.01  fd_cond                                 0
% 3.74/1.01  fd_pseudo_cond                          0
% 3.74/1.01  AC symbols                              0
% 3.74/1.01  
% 3.74/1.01  ------ Input Options Time Limit: Unbounded
% 3.74/1.01  
% 3.74/1.01  
% 3.74/1.01  
% 3.74/1.01  
% 3.74/1.01  ------ Preprocessing...
% 3.74/1.01  
% 3.74/1.01  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 3.74/1.01  Current options:
% 3.74/1.01  ------ 
% 3.74/1.01  
% 3.74/1.01  
% 3.74/1.01  
% 3.74/1.01  
% 3.74/1.01  ------ Proving...
% 3.74/1.01  
% 3.74/1.01  
% 3.74/1.01  ------ Preprocessing...
% 3.74/1.01  
% 3.74/1.01  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.74/1.01  
% 3.74/1.01  ------ Proving...
% 3.74/1.01  
% 3.74/1.01  
% 3.74/1.01  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.74/1.01  
% 3.74/1.01  ------ Proving...
% 3.74/1.01  
% 3.74/1.01  
% 3.74/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.74/1.01  
% 3.74/1.01  ------ Proving...
% 3.74/1.01  
% 3.74/1.01  
% 3.74/1.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.74/1.01  
% 3.74/1.01  ------ Proving...
% 3.74/1.01  
% 3.74/1.01  
% 3.74/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.74/1.01  
% 3.74/1.01  ------ Proving...
% 3.74/1.01  
% 3.74/1.01  
% 3.74/1.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.74/1.01  
% 3.74/1.01  ------ Proving...
% 3.74/1.01  
% 3.74/1.01  
% 3.74/1.01  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.74/1.01  
% 3.74/1.01  ------ Proving...
% 3.74/1.01  
% 3.74/1.01  
% 3.74/1.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.74/1.01  
% 3.74/1.01  ------ Proving...
% 3.74/1.01  
% 3.74/1.01  
% 3.74/1.01  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.74/1.01  
% 3.74/1.01  ------ Proving...
% 3.74/1.01  
% 3.74/1.01  
% 3.74/1.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.74/1.01  
% 3.74/1.01  ------ Proving...
% 3.74/1.01  
% 3.74/1.01  
% 3.74/1.01  ------ Preprocessing...
% 3.74/1.01  
% 3.74/1.01  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.74/1.01  
% 3.74/1.01  ------ Proving...
% 3.74/1.01  
% 3.74/1.01  
% 3.74/1.01  ------ Preprocessing...
% 3.74/1.01  
% 3.74/1.01  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.74/1.01  
% 3.74/1.01  ------ Proving...
% 3.74/1.01  
% 3.74/1.01  
% 3.74/1.01  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.74/1.01  
% 3.74/1.01  ------ Proving...
% 3.74/1.01  
% 3.74/1.01  
% 3.74/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.74/1.01  
% 3.74/1.01  ------ Proving...
% 3.74/1.01  
% 3.74/1.01  
% 3.74/1.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.74/1.01  
% 3.74/1.01  ------ Proving...
% 3.74/1.01  
% 3.74/1.01  
% 3.74/1.01  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.74/1.01  
% 3.74/1.01  ------ Proving...
% 3.74/1.01  
% 3.74/1.01  
% 3.74/1.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.74/1.01  
% 3.74/1.01  ------ Proving...
% 3.74/1.01  
% 3.74/1.01  
% 3.74/1.01  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.74/1.01  
% 3.74/1.01  ------ Proving...
% 3.74/1.01  
% 3.74/1.01  
% 3.74/1.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.74/1.01  
% 3.74/1.01  ------ Proving...
% 3.74/1.01  
% 3.74/1.01  
% 3.74/1.01  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.74/1.01  
% 3.74/1.01  ------ Proving...
% 3.74/1.01  
% 3.74/1.01  
% 3.74/1.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.74/1.01  
% 3.74/1.01  ------ Proving...
% 3.74/1.01  
% 3.74/1.01  
% 3.74/1.01  ------ Preprocessing...
% 3.74/1.01  
% 3.74/1.01  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.74/1.01  
% 3.74/1.01  ------ Proving...
% 3.74/1.01  
% 3.74/1.01  
% 3.74/1.01  ------ Preprocessing...
% 3.74/1.01  
% 3.74/1.01  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.74/1.01  
% 3.74/1.01  ------ Proving...
% 3.74/1.01  
% 3.74/1.01  
% 3.74/1.01  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.74/1.01  
% 3.74/1.01  ------ Proving...
% 3.74/1.01  
% 3.74/1.01  
% 3.74/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.74/1.01  
% 3.74/1.01  ------ Proving...
% 3.74/1.01  
% 3.74/1.01  
% 3.74/1.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.74/1.01  
% 3.74/1.01  ------ Proving...
% 3.74/1.01  
% 3.74/1.01  
% 3.74/1.01  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.74/1.01  
% 3.74/1.01  ------ Proving...
% 3.74/1.01  
% 3.74/1.01  
% 3.74/1.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.74/1.01  
% 3.74/1.01  ------ Proving...
% 3.74/1.01  
% 3.74/1.01  
% 3.74/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.74/1.01  
% 3.74/1.01  ------ Proving...
% 3.74/1.01  
% 3.74/1.01  
% 3.74/1.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.74/1.01  
% 3.74/1.01  ------ Proving...
% 3.74/1.01  
% 3.74/1.01  
% 3.74/1.01  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.74/1.01  
% 3.74/1.01  ------ Proving...
% 3.74/1.01  
% 3.74/1.01  
% 3.74/1.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.74/1.01  
% 3.74/1.01  ------ Proving...
% 3.74/1.01  
% 3.74/1.01  
% 3.74/1.01  % SZS status Theorem for theBenchmark.p
% 3.74/1.01  
% 3.74/1.01   Resolution empty clause
% 3.74/1.01  
% 3.74/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 3.74/1.01  
% 3.74/1.01  fof(f3,axiom,(
% 3.74/1.01    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 3.74/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.74/1.01  
% 3.74/1.01  fof(f24,plain,(
% 3.74/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 3.74/1.01    inference(cnf_transformation,[],[f3])).
% 3.74/1.01  
% 3.74/1.01  fof(f4,axiom,(
% 3.74/1.01    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.74/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.74/1.01  
% 3.74/1.01  fof(f25,plain,(
% 3.74/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.74/1.01    inference(cnf_transformation,[],[f4])).
% 3.74/1.01  
% 3.74/1.01  fof(f36,plain,(
% 3.74/1.01    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 3.74/1.01    inference(definition_unfolding,[],[f24,f25,f25])).
% 3.74/1.01  
% 3.74/1.01  fof(f10,conjecture,(
% 3.74/1.01    ! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 3.74/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.74/1.01  
% 3.74/1.01  fof(f11,negated_conjecture,(
% 3.74/1.01    ~! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 3.74/1.01    inference(negated_conjecture,[],[f10])).
% 3.74/1.01  
% 3.74/1.01  fof(f19,plain,(
% 3.74/1.01    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) & v1_relat_1(X2))),
% 3.74/1.01    inference(ennf_transformation,[],[f11])).
% 3.74/1.01  
% 3.74/1.01  fof(f20,plain,(
% 3.74/1.01    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) & v1_relat_1(X2)) => (~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) & v1_relat_1(sK2))),
% 3.74/1.01    introduced(choice_axiom,[])).
% 3.74/1.01  
% 3.74/1.01  fof(f21,plain,(
% 3.74/1.01    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) & v1_relat_1(sK2)),
% 3.74/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f20])).
% 3.74/1.01  
% 3.74/1.01  fof(f31,plain,(
% 3.74/1.01    v1_relat_1(sK2)),
% 3.74/1.01    inference(cnf_transformation,[],[f21])).
% 3.74/1.01  
% 3.74/1.01  fof(f1,axiom,(
% 3.74/1.01    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 3.74/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.74/1.01  
% 3.74/1.01  fof(f22,plain,(
% 3.74/1.01    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 3.74/1.01    inference(cnf_transformation,[],[f1])).
% 3.74/1.01  
% 3.74/1.01  fof(f5,axiom,(
% 3.74/1.01    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.74/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.74/1.01  
% 3.74/1.01  fof(f26,plain,(
% 3.74/1.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.74/1.01    inference(cnf_transformation,[],[f5])).
% 3.74/1.01  
% 3.74/1.01  fof(f33,plain,(
% 3.74/1.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 3.74/1.01    inference(definition_unfolding,[],[f26,f25])).
% 3.74/1.01  
% 3.74/1.01  fof(f34,plain,(
% 3.74/1.01    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X0)) )),
% 3.74/1.01    inference(definition_unfolding,[],[f22,f33])).
% 3.74/1.01  
% 3.74/1.01  fof(f7,axiom,(
% 3.74/1.01    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0)))),
% 3.74/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.74/1.01  
% 3.74/1.01  fof(f15,plain,(
% 3.74/1.01    ! [X0,X1,X2] : ((k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 3.74/1.01    inference(ennf_transformation,[],[f7])).
% 3.74/1.01  
% 3.74/1.01  fof(f16,plain,(
% 3.74/1.01    ! [X0,X1,X2] : (k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 3.74/1.01    inference(flattening,[],[f15])).
% 3.74/1.01  
% 3.74/1.01  fof(f28,plain,(
% 3.74/1.01    ( ! [X2,X0,X1] : (k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 3.74/1.01    inference(cnf_transformation,[],[f16])).
% 3.74/1.01  
% 3.74/1.01  fof(f6,axiom,(
% 3.74/1.01    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 3.74/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.74/1.01  
% 3.74/1.01  fof(f14,plain,(
% 3.74/1.01    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 3.74/1.01    inference(ennf_transformation,[],[f6])).
% 3.74/1.01  
% 3.74/1.01  fof(f27,plain,(
% 3.74/1.01    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 3.74/1.01    inference(cnf_transformation,[],[f14])).
% 3.74/1.01  
% 3.74/1.01  fof(f9,axiom,(
% 3.74/1.01    ! [X0,X1] : (v1_relat_1(X1) => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)))),
% 3.74/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.74/1.01  
% 3.74/1.01  fof(f18,plain,(
% 3.74/1.01    ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 3.74/1.01    inference(ennf_transformation,[],[f9])).
% 3.74/1.01  
% 3.74/1.01  fof(f30,plain,(
% 3.74/1.01    ( ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 3.74/1.01    inference(cnf_transformation,[],[f18])).
% 3.74/1.01  
% 3.74/1.01  fof(f8,axiom,(
% 3.74/1.01    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)))),
% 3.74/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.74/1.01  
% 3.74/1.01  fof(f17,plain,(
% 3.74/1.01    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 3.74/1.01    inference(ennf_transformation,[],[f8])).
% 3.74/1.01  
% 3.74/1.01  fof(f29,plain,(
% 3.74/1.01    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.74/1.01    inference(cnf_transformation,[],[f17])).
% 3.74/1.01  
% 3.74/1.01  fof(f2,axiom,(
% 3.74/1.01    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 3.74/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.74/1.01  
% 3.74/1.01  fof(f12,plain,(
% 3.74/1.01    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 3.74/1.01    inference(ennf_transformation,[],[f2])).
% 3.74/1.01  
% 3.74/1.01  fof(f13,plain,(
% 3.74/1.01    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 3.74/1.01    inference(flattening,[],[f12])).
% 3.74/1.01  
% 3.74/1.01  fof(f23,plain,(
% 3.74/1.01    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 3.74/1.01    inference(cnf_transformation,[],[f13])).
% 3.74/1.01  
% 3.74/1.01  fof(f35,plain,(
% 3.74/1.01    ( ! [X2,X0,X1] : (r1_tarski(X0,k1_setfam_1(k1_enumset1(X1,X1,X2))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 3.74/1.01    inference(definition_unfolding,[],[f23,f33])).
% 3.74/1.01  
% 3.74/1.01  fof(f32,plain,(
% 3.74/1.01    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))),
% 3.74/1.01    inference(cnf_transformation,[],[f21])).
% 3.74/1.01  
% 3.74/1.01  fof(f37,plain,(
% 3.74/1.01    ~r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k1_setfam_1(k1_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))))),
% 3.74/1.01    inference(definition_unfolding,[],[f32,f33,f33])).
% 3.74/1.01  
% 3.74/1.01  cnf(c_2,plain,
% 3.74/1.01      ( k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
% 3.74/1.01      inference(cnf_transformation,[],[f36]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_105,plain,
% 3.74/1.01      ( k1_enumset1(X0_39,X0_39,X1_39) = k1_enumset1(X1_39,X1_39,X0_39) ),
% 3.74/1.01      inference(subtyping,[status(esa)],[c_2]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_8,negated_conjecture,
% 3.74/1.01      ( v1_relat_1(sK2) ),
% 3.74/1.01      inference(cnf_transformation,[],[f31]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_99,negated_conjecture,
% 3.74/1.01      ( v1_relat_1(sK2) ),
% 3.74/1.01      inference(subtyping,[status(esa)],[c_8]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_9523,plain,
% 3.74/1.01      ( v1_relat_1(sK2) = iProver_top ),
% 3.74/1.01      inference(predicate_to_equality,[status(thm)],[c_99]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_0,plain,
% 3.74/1.01      ( r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X0) ),
% 3.74/1.01      inference(cnf_transformation,[],[f34]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_107,plain,
% 3.74/1.01      ( r1_tarski(k1_setfam_1(k1_enumset1(X0_39,X0_39,X1_39)),X0_39) ),
% 3.74/1.01      inference(subtyping,[status(esa)],[c_0]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_9517,plain,
% 3.74/1.01      ( r1_tarski(k1_setfam_1(k1_enumset1(X0_39,X0_39,X1_39)),X0_39) = iProver_top ),
% 3.74/1.01      inference(predicate_to_equality,[status(thm)],[c_107]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_4,plain,
% 3.74/1.01      ( ~ r1_tarski(X0,X1)
% 3.74/1.01      | ~ v1_relat_1(X2)
% 3.74/1.01      | k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0) ),
% 3.74/1.01      inference(cnf_transformation,[],[f28]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_103,plain,
% 3.74/1.01      ( ~ r1_tarski(X0_39,X1_39)
% 3.74/1.01      | ~ v1_relat_1(X0_38)
% 3.74/1.01      | k7_relat_1(k7_relat_1(X0_38,X1_39),X0_39) = k7_relat_1(X0_38,X0_39) ),
% 3.74/1.01      inference(subtyping,[status(esa)],[c_4]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_9520,plain,
% 3.74/1.01      ( k7_relat_1(k7_relat_1(X0_38,X0_39),X1_39) = k7_relat_1(X0_38,X1_39)
% 3.74/1.01      | r1_tarski(X1_39,X0_39) != iProver_top
% 3.74/1.01      | v1_relat_1(X0_38) != iProver_top ),
% 3.74/1.01      inference(predicate_to_equality,[status(thm)],[c_103]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_9675,plain,
% 3.74/1.01      ( k7_relat_1(k7_relat_1(X0_38,X0_39),k1_setfam_1(k1_enumset1(X0_39,X0_39,X1_39))) = k7_relat_1(X0_38,k1_setfam_1(k1_enumset1(X0_39,X0_39,X1_39)))
% 3.74/1.01      | v1_relat_1(X0_38) != iProver_top ),
% 3.74/1.01      inference(superposition,[status(thm)],[c_9517,c_9520]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_10565,plain,
% 3.74/1.01      ( k7_relat_1(k7_relat_1(sK2,X0_39),k1_setfam_1(k1_enumset1(X0_39,X0_39,X1_39))) = k7_relat_1(sK2,k1_setfam_1(k1_enumset1(X0_39,X0_39,X1_39))) ),
% 3.74/1.01      inference(superposition,[status(thm)],[c_9523,c_9675]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_3,plain,
% 3.74/1.01      ( ~ v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1)) ),
% 3.74/1.01      inference(cnf_transformation,[],[f27]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_104,plain,
% 3.74/1.01      ( ~ v1_relat_1(X0_38) | v1_relat_1(k7_relat_1(X0_38,X0_39)) ),
% 3.74/1.01      inference(subtyping,[status(esa)],[c_3]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_9519,plain,
% 3.74/1.01      ( v1_relat_1(X0_38) != iProver_top
% 3.74/1.01      | v1_relat_1(k7_relat_1(X0_38,X0_39)) = iProver_top ),
% 3.74/1.01      inference(predicate_to_equality,[status(thm)],[c_104]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_6,plain,
% 3.74/1.01      ( ~ v1_relat_1(X0) | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 3.74/1.01      inference(cnf_transformation,[],[f30]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_101,plain,
% 3.74/1.01      ( ~ v1_relat_1(X0_38)
% 3.74/1.01      | k2_relat_1(k7_relat_1(X0_38,X0_39)) = k9_relat_1(X0_38,X0_39) ),
% 3.74/1.01      inference(subtyping,[status(esa)],[c_6]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_9522,plain,
% 3.74/1.01      ( k2_relat_1(k7_relat_1(X0_38,X0_39)) = k9_relat_1(X0_38,X0_39)
% 3.74/1.01      | v1_relat_1(X0_38) != iProver_top ),
% 3.74/1.01      inference(predicate_to_equality,[status(thm)],[c_101]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_9635,plain,
% 3.74/1.01      ( k2_relat_1(k7_relat_1(k7_relat_1(X0_38,X0_39),X1_39)) = k9_relat_1(k7_relat_1(X0_38,X0_39),X1_39)
% 3.74/1.01      | v1_relat_1(X0_38) != iProver_top ),
% 3.74/1.01      inference(superposition,[status(thm)],[c_9519,c_9522]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_9729,plain,
% 3.74/1.01      ( k2_relat_1(k7_relat_1(k7_relat_1(sK2,X0_39),X1_39)) = k9_relat_1(k7_relat_1(sK2,X0_39),X1_39) ),
% 3.74/1.01      inference(superposition,[status(thm)],[c_9523,c_9635]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_10605,plain,
% 3.74/1.01      ( k9_relat_1(k7_relat_1(sK2,X0_39),k1_setfam_1(k1_enumset1(X0_39,X0_39,X1_39))) = k2_relat_1(k7_relat_1(sK2,k1_setfam_1(k1_enumset1(X0_39,X0_39,X1_39)))) ),
% 3.74/1.01      inference(superposition,[status(thm)],[c_10565,c_9729]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_9634,plain,
% 3.74/1.01      ( k2_relat_1(k7_relat_1(sK2,X0_39)) = k9_relat_1(sK2,X0_39) ),
% 3.74/1.01      inference(superposition,[status(thm)],[c_9523,c_9522]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_10615,plain,
% 3.74/1.01      ( k9_relat_1(k7_relat_1(sK2,X0_39),k1_setfam_1(k1_enumset1(X0_39,X0_39,X1_39))) = k9_relat_1(sK2,k1_setfam_1(k1_enumset1(X0_39,X0_39,X1_39))) ),
% 3.74/1.01      inference(demodulation,[status(thm)],[c_10605,c_9634]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_5,plain,
% 3.74/1.01      ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0)) | ~ v1_relat_1(X0) ),
% 3.74/1.01      inference(cnf_transformation,[],[f29]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_102,plain,
% 3.74/1.01      ( r1_tarski(k9_relat_1(X0_38,X0_39),k2_relat_1(X0_38))
% 3.74/1.01      | ~ v1_relat_1(X0_38) ),
% 3.74/1.01      inference(subtyping,[status(esa)],[c_5]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_9521,plain,
% 3.74/1.01      ( r1_tarski(k9_relat_1(X0_38,X0_39),k2_relat_1(X0_38)) = iProver_top
% 3.74/1.01      | v1_relat_1(X0_38) != iProver_top ),
% 3.74/1.01      inference(predicate_to_equality,[status(thm)],[c_102]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_9713,plain,
% 3.74/1.01      ( r1_tarski(k9_relat_1(k7_relat_1(sK2,X0_39),X1_39),k9_relat_1(sK2,X0_39)) = iProver_top
% 3.74/1.01      | v1_relat_1(k7_relat_1(sK2,X0_39)) != iProver_top ),
% 3.74/1.01      inference(superposition,[status(thm)],[c_9634,c_9521]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_9,plain,
% 3.74/1.01      ( v1_relat_1(sK2) = iProver_top ),
% 3.74/1.01      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_2498,plain,
% 3.74/1.01      ( v1_relat_1(sK2) = iProver_top ),
% 3.74/1.01      inference(predicate_to_equality,[status(thm)],[c_99]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_2497,plain,
% 3.74/1.01      ( k2_relat_1(k7_relat_1(X0_38,X0_39)) = k9_relat_1(X0_38,X0_39)
% 3.74/1.01      | v1_relat_1(X0_38) != iProver_top ),
% 3.74/1.01      inference(predicate_to_equality,[status(thm)],[c_101]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_2700,plain,
% 3.74/1.01      ( k2_relat_1(k7_relat_1(sK2,X0_39)) = k9_relat_1(sK2,X0_39) ),
% 3.74/1.01      inference(superposition,[status(thm)],[c_2498,c_2497]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_2496,plain,
% 3.74/1.01      ( r1_tarski(k9_relat_1(X0_38,X0_39),k2_relat_1(X0_38)) = iProver_top
% 3.74/1.01      | v1_relat_1(X0_38) != iProver_top ),
% 3.74/1.01      inference(predicate_to_equality,[status(thm)],[c_102]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_2721,plain,
% 3.74/1.01      ( r1_tarski(k9_relat_1(k7_relat_1(sK2,X0_39),X1_39),k9_relat_1(sK2,X0_39)) = iProver_top
% 3.74/1.01      | v1_relat_1(k7_relat_1(sK2,X0_39)) != iProver_top ),
% 3.74/1.01      inference(superposition,[status(thm)],[c_2700,c_2496]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_8617,plain,
% 3.74/1.01      ( v1_relat_1(k7_relat_1(sK2,X0_39)) | ~ v1_relat_1(sK2) ),
% 3.74/1.01      inference(instantiation,[status(thm)],[c_104]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_8618,plain,
% 3.74/1.01      ( v1_relat_1(k7_relat_1(sK2,X0_39)) = iProver_top
% 3.74/1.01      | v1_relat_1(sK2) != iProver_top ),
% 3.74/1.01      inference(predicate_to_equality,[status(thm)],[c_8617]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_9767,plain,
% 3.74/1.01      ( r1_tarski(k9_relat_1(k7_relat_1(sK2,X0_39),X1_39),k9_relat_1(sK2,X0_39)) = iProver_top ),
% 3.74/1.01      inference(global_propositional_subsumption,
% 3.74/1.01                [status(thm)],
% 3.74/1.01                [c_9713,c_9,c_2721,c_8618]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_10748,plain,
% 3.74/1.01      ( r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(X0_39,X0_39,X1_39))),k9_relat_1(sK2,X0_39)) = iProver_top ),
% 3.74/1.01      inference(superposition,[status(thm)],[c_10615,c_9767]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_11010,plain,
% 3.74/1.01      ( r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(X0_39,X0_39,X1_39))),k9_relat_1(sK2,X1_39)) = iProver_top ),
% 3.74/1.01      inference(superposition,[status(thm)],[c_105,c_10748]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_1,plain,
% 3.74/1.01      ( ~ r1_tarski(X0,X1)
% 3.74/1.01      | ~ r1_tarski(X0,X2)
% 3.74/1.01      | r1_tarski(X0,k1_setfam_1(k1_enumset1(X2,X2,X1))) ),
% 3.74/1.01      inference(cnf_transformation,[],[f35]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_106,plain,
% 3.74/1.01      ( ~ r1_tarski(X0_39,X1_39)
% 3.74/1.01      | ~ r1_tarski(X0_39,X2_39)
% 3.74/1.01      | r1_tarski(X0_39,k1_setfam_1(k1_enumset1(X2_39,X2_39,X1_39))) ),
% 3.74/1.01      inference(subtyping,[status(esa)],[c_1]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_9518,plain,
% 3.74/1.01      ( r1_tarski(X0_39,X1_39) != iProver_top
% 3.74/1.01      | r1_tarski(X0_39,X2_39) != iProver_top
% 3.74/1.01      | r1_tarski(X0_39,k1_setfam_1(k1_enumset1(X2_39,X2_39,X1_39))) = iProver_top ),
% 3.74/1.01      inference(predicate_to_equality,[status(thm)],[c_106]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_7,negated_conjecture,
% 3.74/1.01      ( ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k1_setfam_1(k1_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))) ),
% 3.74/1.01      inference(cnf_transformation,[],[f37]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_100,negated_conjecture,
% 3.74/1.01      ( ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k1_setfam_1(k1_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))) ),
% 3.74/1.01      inference(subtyping,[status(esa)],[c_7]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_9524,plain,
% 3.74/1.01      ( r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k1_setfam_1(k1_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))) != iProver_top ),
% 3.74/1.01      inference(predicate_to_equality,[status(thm)],[c_100]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_9656,plain,
% 3.74/1.01      ( r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k9_relat_1(sK2,sK1)) != iProver_top
% 3.74/1.01      | r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k9_relat_1(sK2,sK0)) != iProver_top ),
% 3.74/1.01      inference(superposition,[status(thm)],[c_9518,c_9524]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_11232,plain,
% 3.74/1.01      ( r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k9_relat_1(sK2,sK0)) != iProver_top ),
% 3.74/1.01      inference(superposition,[status(thm)],[c_11010,c_9656]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_11529,plain,
% 3.74/1.01      ( $false ),
% 3.74/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_11232,c_10748]) ).
% 3.74/1.01  
% 3.74/1.01  
% 3.74/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.74/1.01  
% 3.74/1.01  ------                               Statistics
% 3.74/1.01  
% 3.74/1.01  ------ Selected
% 3.74/1.01  
% 3.74/1.01  total_time:                             0.331
% 3.74/1.01  
%------------------------------------------------------------------------------
