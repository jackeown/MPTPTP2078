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
% DateTime   : Thu Dec  3 11:51:58 EST 2020

% Result     : Theorem 3.50s
% Output     : CNFRefutation 3.50s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 160 expanded)
%              Number of clauses        :   35 (  47 expanded)
%              Number of leaves         :   10 (  37 expanded)
%              Depth                    :   16
%              Number of atoms          :  145 ( 306 expanded)
%              Number of equality atoms :   42 (  89 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f20,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1))
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f20])).

fof(f30,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f3,axiom,(
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
    inference(ennf_transformation,[],[f3])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f12])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f33,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f27,f26])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k1_setfam_1(k1_enumset1(X1,X1,X2)))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f24,f33])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f37,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(definition_unfolding,[],[f25,f26,f26])).

fof(f32,plain,(
    ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f39,plain,(
    ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k1_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),sK1))) ),
    inference(definition_unfolding,[],[f32,f33,f33])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f34,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f22,f33])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k1_enumset1(X0,X0,k9_relat_1(X1,k1_relat_1(X1)))) = k9_relat_1(X1,k10_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f29,f33])).

fof(f31,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k1_setfam_1(k1_enumset1(X1,X1,X2))) ) ),
    inference(definition_unfolding,[],[f23,f33])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_8,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_107,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_8])).

cnf(c_108,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) ),
    inference(unflattening,[status(thm)],[c_107])).

cnf(c_163,plain,
    ( ~ r1_tarski(X0_39,X1_39)
    | r1_tarski(k9_relat_1(sK2,X0_39),k9_relat_1(sK2,X1_39)) ),
    inference(subtyping,[status(esa)],[c_108])).

cnf(c_289,plain,
    ( r1_tarski(X0_39,X1_39) != iProver_top
    | r1_tarski(k9_relat_1(sK2,X0_39),k9_relat_1(sK2,X1_39)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_163])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k1_setfam_1(k1_enumset1(X2,X2,X1))) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_167,plain,
    ( ~ r1_tarski(X0_39,X1_39)
    | ~ r1_tarski(X0_39,X2_39)
    | r1_tarski(X0_39,k1_setfam_1(k1_enumset1(X2_39,X2_39,X1_39))) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_287,plain,
    ( r1_tarski(X0_39,X1_39) != iProver_top
    | r1_tarski(X0_39,X2_39) != iProver_top
    | r1_tarski(X0_39,k1_setfam_1(k1_enumset1(X2_39,X2_39,X1_39))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_167])).

cnf(c_3,plain,
    ( k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_166,plain,
    ( k1_enumset1(X0_39,X0_39,X1_39) = k1_enumset1(X1_39,X1_39,X0_39) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_6,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k1_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),sK1))) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_165,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k1_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),sK1))) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_288,plain,
    ( r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k1_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_165])).

cnf(c_388,plain,
    ( r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0)))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_166,c_288])).

cnf(c_950,plain,
    ( r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))),k9_relat_1(sK2,sK0)) != iProver_top
    | r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))),sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_287,c_388])).

cnf(c_0,plain,
    ( r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_169,plain,
    ( r1_tarski(k1_setfam_1(k1_enumset1(X0_39,X0_39,X1_39)),X0_39) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_285,plain,
    ( r1_tarski(k1_setfam_1(k1_enumset1(X0_39,X0_39,X1_39)),X0_39) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_169])).

cnf(c_623,plain,
    ( r1_tarski(k1_setfam_1(k1_enumset1(X0_39,X0_39,X1_39)),X1_39) = iProver_top ),
    inference(superposition,[status(thm)],[c_166,c_285])).

cnf(c_5,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_setfam_1(k1_enumset1(X1,X1,k9_relat_1(X0,k1_relat_1(X0)))) = k9_relat_1(X0,k10_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_7,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_95,plain,
    ( ~ v1_relat_1(X0)
    | k1_setfam_1(k1_enumset1(X1,X1,k9_relat_1(X0,k1_relat_1(X0)))) = k9_relat_1(X0,k10_relat_1(X0,X1))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_7])).

cnf(c_96,plain,
    ( ~ v1_relat_1(sK2)
    | k1_setfam_1(k1_enumset1(X0,X0,k9_relat_1(sK2,k1_relat_1(sK2)))) = k9_relat_1(sK2,k10_relat_1(sK2,X0)) ),
    inference(unflattening,[status(thm)],[c_95])).

cnf(c_100,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,k9_relat_1(sK2,k1_relat_1(sK2)))) = k9_relat_1(sK2,k10_relat_1(sK2,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_96,c_8])).

cnf(c_164,plain,
    ( k1_setfam_1(k1_enumset1(X0_39,X0_39,k9_relat_1(sK2,k1_relat_1(sK2)))) = k9_relat_1(sK2,k10_relat_1(sK2,X0_39)) ),
    inference(subtyping,[status(esa)],[c_100])).

cnf(c_1,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(X0,k1_setfam_1(k1_enumset1(X1,X1,X2))) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_168,plain,
    ( r1_tarski(X0_39,X1_39)
    | ~ r1_tarski(X0_39,k1_setfam_1(k1_enumset1(X1_39,X1_39,X2_39))) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_286,plain,
    ( r1_tarski(X0_39,X1_39) = iProver_top
    | r1_tarski(X0_39,k1_setfam_1(k1_enumset1(X1_39,X1_39,X2_39))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_168])).

cnf(c_801,plain,
    ( r1_tarski(X0_39,X1_39) = iProver_top
    | r1_tarski(X0_39,k9_relat_1(sK2,k10_relat_1(sK2,X1_39))) != iProver_top ),
    inference(superposition,[status(thm)],[c_164,c_286])).

cnf(c_1167,plain,
    ( r1_tarski(X0_39,k10_relat_1(sK2,X1_39)) != iProver_top
    | r1_tarski(k9_relat_1(sK2,X0_39),X1_39) = iProver_top ),
    inference(superposition,[status(thm)],[c_289,c_801])).

cnf(c_1716,plain,
    ( r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(X0_39,X0_39,k10_relat_1(sK2,X1_39)))),X1_39) = iProver_top ),
    inference(superposition,[status(thm)],[c_623,c_1167])).

cnf(c_5971,plain,
    ( r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))),k9_relat_1(sK2,sK0)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_950,c_1716])).

cnf(c_5973,plain,
    ( r1_tarski(k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1))),sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_289,c_5971])).

cnf(c_6867,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5973,c_285])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:47:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.50/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.50/0.98  
% 3.50/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.50/0.98  
% 3.50/0.98  ------  iProver source info
% 3.50/0.98  
% 3.50/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.50/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.50/0.98  git: non_committed_changes: false
% 3.50/0.98  git: last_make_outside_of_git: false
% 3.50/0.98  
% 3.50/0.98  ------ 
% 3.50/0.98  
% 3.50/0.98  ------ Input Options
% 3.50/0.98  
% 3.50/0.98  --out_options                           all
% 3.50/0.98  --tptp_safe_out                         true
% 3.50/0.98  --problem_path                          ""
% 3.50/0.98  --include_path                          ""
% 3.50/0.98  --clausifier                            res/vclausify_rel
% 3.50/0.98  --clausifier_options                    --mode clausify
% 3.50/0.98  --stdin                                 false
% 3.50/0.98  --stats_out                             all
% 3.50/0.98  
% 3.50/0.98  ------ General Options
% 3.50/0.98  
% 3.50/0.98  --fof                                   false
% 3.50/0.98  --time_out_real                         305.
% 3.50/0.98  --time_out_virtual                      -1.
% 3.50/0.98  --symbol_type_check                     false
% 3.50/0.98  --clausify_out                          false
% 3.50/0.98  --sig_cnt_out                           false
% 3.50/0.98  --trig_cnt_out                          false
% 3.50/0.98  --trig_cnt_out_tolerance                1.
% 3.50/0.98  --trig_cnt_out_sk_spl                   false
% 3.50/0.98  --abstr_cl_out                          false
% 3.50/0.98  
% 3.50/0.98  ------ Global Options
% 3.50/0.98  
% 3.50/0.98  --schedule                              default
% 3.50/0.98  --add_important_lit                     false
% 3.50/0.98  --prop_solver_per_cl                    1000
% 3.50/0.98  --min_unsat_core                        false
% 3.50/0.98  --soft_assumptions                      false
% 3.50/0.98  --soft_lemma_size                       3
% 3.50/0.98  --prop_impl_unit_size                   0
% 3.50/0.98  --prop_impl_unit                        []
% 3.50/0.98  --share_sel_clauses                     true
% 3.50/0.98  --reset_solvers                         false
% 3.50/0.98  --bc_imp_inh                            [conj_cone]
% 3.50/0.98  --conj_cone_tolerance                   3.
% 3.50/0.98  --extra_neg_conj                        none
% 3.50/0.98  --large_theory_mode                     true
% 3.50/0.98  --prolific_symb_bound                   200
% 3.50/0.98  --lt_threshold                          2000
% 3.50/0.98  --clause_weak_htbl                      true
% 3.50/0.98  --gc_record_bc_elim                     false
% 3.50/0.98  
% 3.50/0.98  ------ Preprocessing Options
% 3.50/0.98  
% 3.50/0.98  --preprocessing_flag                    true
% 3.50/0.98  --time_out_prep_mult                    0.1
% 3.50/0.98  --splitting_mode                        input
% 3.50/0.98  --splitting_grd                         true
% 3.50/0.98  --splitting_cvd                         false
% 3.50/0.98  --splitting_cvd_svl                     false
% 3.50/0.98  --splitting_nvd                         32
% 3.50/0.98  --sub_typing                            true
% 3.50/0.98  --prep_gs_sim                           true
% 3.50/0.98  --prep_unflatten                        true
% 3.50/0.98  --prep_res_sim                          true
% 3.50/0.98  --prep_upred                            true
% 3.50/0.98  --prep_sem_filter                       exhaustive
% 3.50/0.98  --prep_sem_filter_out                   false
% 3.50/0.98  --pred_elim                             true
% 3.50/0.98  --res_sim_input                         true
% 3.50/0.98  --eq_ax_congr_red                       true
% 3.50/0.98  --pure_diseq_elim                       true
% 3.50/0.98  --brand_transform                       false
% 3.50/0.98  --non_eq_to_eq                          false
% 3.50/0.98  --prep_def_merge                        true
% 3.50/0.98  --prep_def_merge_prop_impl              false
% 3.50/0.98  --prep_def_merge_mbd                    true
% 3.50/0.98  --prep_def_merge_tr_red                 false
% 3.50/0.98  --prep_def_merge_tr_cl                  false
% 3.50/0.98  --smt_preprocessing                     true
% 3.50/0.98  --smt_ac_axioms                         fast
% 3.50/0.98  --preprocessed_out                      false
% 3.50/0.98  --preprocessed_stats                    false
% 3.50/0.98  
% 3.50/0.98  ------ Abstraction refinement Options
% 3.50/0.98  
% 3.50/0.98  --abstr_ref                             []
% 3.50/0.98  --abstr_ref_prep                        false
% 3.50/0.98  --abstr_ref_until_sat                   false
% 3.50/0.98  --abstr_ref_sig_restrict                funpre
% 3.50/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.50/0.98  --abstr_ref_under                       []
% 3.50/0.98  
% 3.50/0.98  ------ SAT Options
% 3.50/0.98  
% 3.50/0.98  --sat_mode                              false
% 3.50/0.98  --sat_fm_restart_options                ""
% 3.50/0.98  --sat_gr_def                            false
% 3.50/0.98  --sat_epr_types                         true
% 3.50/0.98  --sat_non_cyclic_types                  false
% 3.50/0.98  --sat_finite_models                     false
% 3.50/0.98  --sat_fm_lemmas                         false
% 3.50/0.98  --sat_fm_prep                           false
% 3.50/0.98  --sat_fm_uc_incr                        true
% 3.50/0.98  --sat_out_model                         small
% 3.50/0.98  --sat_out_clauses                       false
% 3.50/0.98  
% 3.50/0.98  ------ QBF Options
% 3.50/0.98  
% 3.50/0.98  --qbf_mode                              false
% 3.50/0.98  --qbf_elim_univ                         false
% 3.50/0.98  --qbf_dom_inst                          none
% 3.50/0.98  --qbf_dom_pre_inst                      false
% 3.50/0.98  --qbf_sk_in                             false
% 3.50/0.98  --qbf_pred_elim                         true
% 3.50/0.98  --qbf_split                             512
% 3.50/0.98  
% 3.50/0.98  ------ BMC1 Options
% 3.50/0.98  
% 3.50/0.98  --bmc1_incremental                      false
% 3.50/0.98  --bmc1_axioms                           reachable_all
% 3.50/0.98  --bmc1_min_bound                        0
% 3.50/0.98  --bmc1_max_bound                        -1
% 3.50/0.98  --bmc1_max_bound_default                -1
% 3.50/0.98  --bmc1_symbol_reachability              true
% 3.50/0.98  --bmc1_property_lemmas                  false
% 3.50/0.98  --bmc1_k_induction                      false
% 3.50/0.98  --bmc1_non_equiv_states                 false
% 3.50/0.98  --bmc1_deadlock                         false
% 3.50/0.98  --bmc1_ucm                              false
% 3.50/0.98  --bmc1_add_unsat_core                   none
% 3.50/0.98  --bmc1_unsat_core_children              false
% 3.50/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.50/0.98  --bmc1_out_stat                         full
% 3.50/0.98  --bmc1_ground_init                      false
% 3.50/0.98  --bmc1_pre_inst_next_state              false
% 3.50/0.98  --bmc1_pre_inst_state                   false
% 3.50/0.98  --bmc1_pre_inst_reach_state             false
% 3.50/0.98  --bmc1_out_unsat_core                   false
% 3.50/0.98  --bmc1_aig_witness_out                  false
% 3.50/0.98  --bmc1_verbose                          false
% 3.50/0.98  --bmc1_dump_clauses_tptp                false
% 3.50/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.50/0.98  --bmc1_dump_file                        -
% 3.50/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.50/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.50/0.98  --bmc1_ucm_extend_mode                  1
% 3.50/0.98  --bmc1_ucm_init_mode                    2
% 3.50/0.98  --bmc1_ucm_cone_mode                    none
% 3.50/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.50/0.98  --bmc1_ucm_relax_model                  4
% 3.50/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.50/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.50/0.98  --bmc1_ucm_layered_model                none
% 3.50/0.98  --bmc1_ucm_max_lemma_size               10
% 3.50/0.98  
% 3.50/0.98  ------ AIG Options
% 3.50/0.98  
% 3.50/0.98  --aig_mode                              false
% 3.50/0.98  
% 3.50/0.98  ------ Instantiation Options
% 3.50/0.98  
% 3.50/0.98  --instantiation_flag                    true
% 3.50/0.98  --inst_sos_flag                         false
% 3.50/0.98  --inst_sos_phase                        true
% 3.50/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.50/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.50/0.98  --inst_lit_sel_side                     num_symb
% 3.50/0.98  --inst_solver_per_active                1400
% 3.50/0.98  --inst_solver_calls_frac                1.
% 3.50/0.98  --inst_passive_queue_type               priority_queues
% 3.50/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.50/0.98  --inst_passive_queues_freq              [25;2]
% 3.50/0.98  --inst_dismatching                      true
% 3.50/0.98  --inst_eager_unprocessed_to_passive     true
% 3.50/0.98  --inst_prop_sim_given                   true
% 3.50/0.98  --inst_prop_sim_new                     false
% 3.50/0.98  --inst_subs_new                         false
% 3.50/0.98  --inst_eq_res_simp                      false
% 3.50/0.98  --inst_subs_given                       false
% 3.50/0.98  --inst_orphan_elimination               true
% 3.50/0.98  --inst_learning_loop_flag               true
% 3.50/0.98  --inst_learning_start                   3000
% 3.50/0.98  --inst_learning_factor                  2
% 3.50/0.98  --inst_start_prop_sim_after_learn       3
% 3.50/0.98  --inst_sel_renew                        solver
% 3.50/0.98  --inst_lit_activity_flag                true
% 3.50/0.98  --inst_restr_to_given                   false
% 3.50/0.98  --inst_activity_threshold               500
% 3.50/0.98  --inst_out_proof                        true
% 3.50/0.98  
% 3.50/0.98  ------ Resolution Options
% 3.50/0.98  
% 3.50/0.98  --resolution_flag                       true
% 3.50/0.98  --res_lit_sel                           adaptive
% 3.50/0.98  --res_lit_sel_side                      none
% 3.50/0.98  --res_ordering                          kbo
% 3.50/0.98  --res_to_prop_solver                    active
% 3.50/0.98  --res_prop_simpl_new                    false
% 3.50/0.98  --res_prop_simpl_given                  true
% 3.50/0.98  --res_passive_queue_type                priority_queues
% 3.50/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.50/0.98  --res_passive_queues_freq               [15;5]
% 3.50/0.98  --res_forward_subs                      full
% 3.50/0.98  --res_backward_subs                     full
% 3.50/0.98  --res_forward_subs_resolution           true
% 3.50/0.98  --res_backward_subs_resolution          true
% 3.50/0.98  --res_orphan_elimination                true
% 3.50/0.98  --res_time_limit                        2.
% 3.50/0.98  --res_out_proof                         true
% 3.50/0.98  
% 3.50/0.98  ------ Superposition Options
% 3.50/0.98  
% 3.50/0.98  --superposition_flag                    true
% 3.50/0.98  --sup_passive_queue_type                priority_queues
% 3.50/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.50/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.50/0.98  --demod_completeness_check              fast
% 3.50/0.98  --demod_use_ground                      true
% 3.50/0.98  --sup_to_prop_solver                    passive
% 3.50/0.98  --sup_prop_simpl_new                    true
% 3.50/0.98  --sup_prop_simpl_given                  true
% 3.50/0.98  --sup_fun_splitting                     false
% 3.50/0.98  --sup_smt_interval                      50000
% 3.50/0.98  
% 3.50/0.98  ------ Superposition Simplification Setup
% 3.50/0.98  
% 3.50/0.98  --sup_indices_passive                   []
% 3.50/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.50/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.50/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.50/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.50/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.50/0.98  --sup_full_bw                           [BwDemod]
% 3.50/0.98  --sup_immed_triv                        [TrivRules]
% 3.50/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.50/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.50/0.98  --sup_immed_bw_main                     []
% 3.50/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.50/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.50/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.50/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.50/0.98  
% 3.50/0.98  ------ Combination Options
% 3.50/0.98  
% 3.50/0.98  --comb_res_mult                         3
% 3.50/0.98  --comb_sup_mult                         2
% 3.50/0.98  --comb_inst_mult                        10
% 3.50/0.98  
% 3.50/0.98  ------ Debug Options
% 3.50/0.98  
% 3.50/0.98  --dbg_backtrace                         false
% 3.50/0.98  --dbg_dump_prop_clauses                 false
% 3.50/0.98  --dbg_dump_prop_clauses_file            -
% 3.50/0.98  --dbg_out_stat                          false
% 3.50/0.98  ------ Parsing...
% 3.50/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.50/0.98  
% 3.50/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.50/0.98  
% 3.50/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.50/0.98  
% 3.50/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.50/0.98  ------ Proving...
% 3.50/0.98  ------ Problem Properties 
% 3.50/0.98  
% 3.50/0.98  
% 3.50/0.98  clauses                                 7
% 3.50/0.98  conjectures                             1
% 3.50/0.98  EPR                                     0
% 3.50/0.98  Horn                                    7
% 3.50/0.98  unary                                   4
% 3.50/0.98  binary                                  2
% 3.50/0.98  lits                                    11
% 3.50/0.98  lits eq                                 2
% 3.50/0.98  fd_pure                                 0
% 3.50/0.98  fd_pseudo                               0
% 3.50/0.98  fd_cond                                 0
% 3.50/0.98  fd_pseudo_cond                          0
% 3.50/0.98  AC symbols                              0
% 3.50/0.98  
% 3.50/0.98  ------ Schedule dynamic 5 is on 
% 3.50/0.98  
% 3.50/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.50/0.98  
% 3.50/0.98  
% 3.50/0.98  ------ 
% 3.50/0.98  Current options:
% 3.50/0.98  ------ 
% 3.50/0.98  
% 3.50/0.98  ------ Input Options
% 3.50/0.98  
% 3.50/0.98  --out_options                           all
% 3.50/0.98  --tptp_safe_out                         true
% 3.50/0.98  --problem_path                          ""
% 3.50/0.98  --include_path                          ""
% 3.50/0.98  --clausifier                            res/vclausify_rel
% 3.50/0.98  --clausifier_options                    --mode clausify
% 3.50/0.98  --stdin                                 false
% 3.50/0.98  --stats_out                             all
% 3.50/0.98  
% 3.50/0.98  ------ General Options
% 3.50/0.98  
% 3.50/0.98  --fof                                   false
% 3.50/0.98  --time_out_real                         305.
% 3.50/0.98  --time_out_virtual                      -1.
% 3.50/0.98  --symbol_type_check                     false
% 3.50/0.98  --clausify_out                          false
% 3.50/0.98  --sig_cnt_out                           false
% 3.50/0.98  --trig_cnt_out                          false
% 3.50/0.98  --trig_cnt_out_tolerance                1.
% 3.50/0.98  --trig_cnt_out_sk_spl                   false
% 3.50/0.98  --abstr_cl_out                          false
% 3.50/0.98  
% 3.50/0.98  ------ Global Options
% 3.50/0.98  
% 3.50/0.98  --schedule                              default
% 3.50/0.98  --add_important_lit                     false
% 3.50/0.98  --prop_solver_per_cl                    1000
% 3.50/0.98  --min_unsat_core                        false
% 3.50/0.98  --soft_assumptions                      false
% 3.50/0.98  --soft_lemma_size                       3
% 3.50/0.98  --prop_impl_unit_size                   0
% 3.50/0.98  --prop_impl_unit                        []
% 3.50/0.98  --share_sel_clauses                     true
% 3.50/0.98  --reset_solvers                         false
% 3.50/0.98  --bc_imp_inh                            [conj_cone]
% 3.50/0.98  --conj_cone_tolerance                   3.
% 3.50/0.98  --extra_neg_conj                        none
% 3.50/0.98  --large_theory_mode                     true
% 3.50/0.98  --prolific_symb_bound                   200
% 3.50/0.98  --lt_threshold                          2000
% 3.50/0.98  --clause_weak_htbl                      true
% 3.50/0.98  --gc_record_bc_elim                     false
% 3.50/0.98  
% 3.50/0.98  ------ Preprocessing Options
% 3.50/0.98  
% 3.50/0.98  --preprocessing_flag                    true
% 3.50/0.98  --time_out_prep_mult                    0.1
% 3.50/0.98  --splitting_mode                        input
% 3.50/0.98  --splitting_grd                         true
% 3.50/0.98  --splitting_cvd                         false
% 3.50/0.98  --splitting_cvd_svl                     false
% 3.50/0.98  --splitting_nvd                         32
% 3.50/0.98  --sub_typing                            true
% 3.50/0.98  --prep_gs_sim                           true
% 3.50/0.98  --prep_unflatten                        true
% 3.50/0.98  --prep_res_sim                          true
% 3.50/0.98  --prep_upred                            true
% 3.50/0.98  --prep_sem_filter                       exhaustive
% 3.50/0.98  --prep_sem_filter_out                   false
% 3.50/0.98  --pred_elim                             true
% 3.50/0.98  --res_sim_input                         true
% 3.50/0.98  --eq_ax_congr_red                       true
% 3.50/0.98  --pure_diseq_elim                       true
% 3.50/0.98  --brand_transform                       false
% 3.50/0.98  --non_eq_to_eq                          false
% 3.50/0.98  --prep_def_merge                        true
% 3.50/0.98  --prep_def_merge_prop_impl              false
% 3.50/0.98  --prep_def_merge_mbd                    true
% 3.50/0.98  --prep_def_merge_tr_red                 false
% 3.50/0.98  --prep_def_merge_tr_cl                  false
% 3.50/0.98  --smt_preprocessing                     true
% 3.50/0.98  --smt_ac_axioms                         fast
% 3.50/0.98  --preprocessed_out                      false
% 3.50/0.98  --preprocessed_stats                    false
% 3.50/0.98  
% 3.50/0.98  ------ Abstraction refinement Options
% 3.50/0.98  
% 3.50/0.98  --abstr_ref                             []
% 3.50/0.98  --abstr_ref_prep                        false
% 3.50/0.98  --abstr_ref_until_sat                   false
% 3.50/0.98  --abstr_ref_sig_restrict                funpre
% 3.50/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.50/0.98  --abstr_ref_under                       []
% 3.50/0.98  
% 3.50/0.98  ------ SAT Options
% 3.50/0.98  
% 3.50/0.98  --sat_mode                              false
% 3.50/0.98  --sat_fm_restart_options                ""
% 3.50/0.98  --sat_gr_def                            false
% 3.50/0.98  --sat_epr_types                         true
% 3.50/0.98  --sat_non_cyclic_types                  false
% 3.50/0.98  --sat_finite_models                     false
% 3.50/0.98  --sat_fm_lemmas                         false
% 3.50/0.98  --sat_fm_prep                           false
% 3.50/0.98  --sat_fm_uc_incr                        true
% 3.50/0.98  --sat_out_model                         small
% 3.50/0.98  --sat_out_clauses                       false
% 3.50/0.98  
% 3.50/0.98  ------ QBF Options
% 3.50/0.98  
% 3.50/0.98  --qbf_mode                              false
% 3.50/0.98  --qbf_elim_univ                         false
% 3.50/0.98  --qbf_dom_inst                          none
% 3.50/0.98  --qbf_dom_pre_inst                      false
% 3.50/0.98  --qbf_sk_in                             false
% 3.50/0.98  --qbf_pred_elim                         true
% 3.50/0.98  --qbf_split                             512
% 3.50/0.98  
% 3.50/0.98  ------ BMC1 Options
% 3.50/0.98  
% 3.50/0.98  --bmc1_incremental                      false
% 3.50/0.98  --bmc1_axioms                           reachable_all
% 3.50/0.98  --bmc1_min_bound                        0
% 3.50/0.98  --bmc1_max_bound                        -1
% 3.50/0.98  --bmc1_max_bound_default                -1
% 3.50/0.98  --bmc1_symbol_reachability              true
% 3.50/0.98  --bmc1_property_lemmas                  false
% 3.50/0.98  --bmc1_k_induction                      false
% 3.50/0.98  --bmc1_non_equiv_states                 false
% 3.50/0.98  --bmc1_deadlock                         false
% 3.50/0.98  --bmc1_ucm                              false
% 3.50/0.98  --bmc1_add_unsat_core                   none
% 3.50/0.98  --bmc1_unsat_core_children              false
% 3.50/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.50/0.98  --bmc1_out_stat                         full
% 3.50/0.98  --bmc1_ground_init                      false
% 3.50/0.98  --bmc1_pre_inst_next_state              false
% 3.50/0.98  --bmc1_pre_inst_state                   false
% 3.50/0.98  --bmc1_pre_inst_reach_state             false
% 3.50/0.98  --bmc1_out_unsat_core                   false
% 3.50/0.98  --bmc1_aig_witness_out                  false
% 3.50/0.98  --bmc1_verbose                          false
% 3.50/0.98  --bmc1_dump_clauses_tptp                false
% 3.50/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.50/0.98  --bmc1_dump_file                        -
% 3.50/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.50/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.50/0.98  --bmc1_ucm_extend_mode                  1
% 3.50/0.98  --bmc1_ucm_init_mode                    2
% 3.50/0.98  --bmc1_ucm_cone_mode                    none
% 3.50/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.50/0.98  --bmc1_ucm_relax_model                  4
% 3.50/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.50/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.50/0.98  --bmc1_ucm_layered_model                none
% 3.50/0.98  --bmc1_ucm_max_lemma_size               10
% 3.50/0.98  
% 3.50/0.98  ------ AIG Options
% 3.50/0.98  
% 3.50/0.98  --aig_mode                              false
% 3.50/0.98  
% 3.50/0.98  ------ Instantiation Options
% 3.50/0.98  
% 3.50/0.98  --instantiation_flag                    true
% 3.50/0.98  --inst_sos_flag                         false
% 3.50/0.98  --inst_sos_phase                        true
% 3.50/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.50/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.50/0.98  --inst_lit_sel_side                     none
% 3.50/0.98  --inst_solver_per_active                1400
% 3.50/0.98  --inst_solver_calls_frac                1.
% 3.50/0.98  --inst_passive_queue_type               priority_queues
% 3.50/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.50/0.98  --inst_passive_queues_freq              [25;2]
% 3.50/0.98  --inst_dismatching                      true
% 3.50/0.98  --inst_eager_unprocessed_to_passive     true
% 3.50/0.98  --inst_prop_sim_given                   true
% 3.50/0.98  --inst_prop_sim_new                     false
% 3.50/0.98  --inst_subs_new                         false
% 3.50/0.98  --inst_eq_res_simp                      false
% 3.50/0.98  --inst_subs_given                       false
% 3.50/0.98  --inst_orphan_elimination               true
% 3.50/0.98  --inst_learning_loop_flag               true
% 3.50/0.98  --inst_learning_start                   3000
% 3.50/0.98  --inst_learning_factor                  2
% 3.50/0.98  --inst_start_prop_sim_after_learn       3
% 3.50/0.98  --inst_sel_renew                        solver
% 3.50/0.98  --inst_lit_activity_flag                true
% 3.50/0.98  --inst_restr_to_given                   false
% 3.50/0.98  --inst_activity_threshold               500
% 3.50/0.98  --inst_out_proof                        true
% 3.50/0.98  
% 3.50/0.98  ------ Resolution Options
% 3.50/0.98  
% 3.50/0.98  --resolution_flag                       false
% 3.50/0.98  --res_lit_sel                           adaptive
% 3.50/0.98  --res_lit_sel_side                      none
% 3.50/0.98  --res_ordering                          kbo
% 3.50/0.98  --res_to_prop_solver                    active
% 3.50/0.98  --res_prop_simpl_new                    false
% 3.50/0.98  --res_prop_simpl_given                  true
% 3.50/0.98  --res_passive_queue_type                priority_queues
% 3.50/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.50/0.98  --res_passive_queues_freq               [15;5]
% 3.50/0.98  --res_forward_subs                      full
% 3.50/0.98  --res_backward_subs                     full
% 3.50/0.98  --res_forward_subs_resolution           true
% 3.50/0.98  --res_backward_subs_resolution          true
% 3.50/0.98  --res_orphan_elimination                true
% 3.50/0.98  --res_time_limit                        2.
% 3.50/0.98  --res_out_proof                         true
% 3.50/0.98  
% 3.50/0.98  ------ Superposition Options
% 3.50/0.98  
% 3.50/0.98  --superposition_flag                    true
% 3.50/0.98  --sup_passive_queue_type                priority_queues
% 3.50/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.50/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.50/0.98  --demod_completeness_check              fast
% 3.50/0.98  --demod_use_ground                      true
% 3.50/0.98  --sup_to_prop_solver                    passive
% 3.50/0.98  --sup_prop_simpl_new                    true
% 3.50/0.98  --sup_prop_simpl_given                  true
% 3.50/0.98  --sup_fun_splitting                     false
% 3.50/0.98  --sup_smt_interval                      50000
% 3.50/0.98  
% 3.50/0.98  ------ Superposition Simplification Setup
% 3.50/0.98  
% 3.50/0.98  --sup_indices_passive                   []
% 3.50/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.50/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.50/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.50/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.50/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.50/0.98  --sup_full_bw                           [BwDemod]
% 3.50/0.98  --sup_immed_triv                        [TrivRules]
% 3.50/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.50/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.50/0.98  --sup_immed_bw_main                     []
% 3.50/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.50/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.50/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.50/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.50/0.98  
% 3.50/0.98  ------ Combination Options
% 3.50/0.98  
% 3.50/0.98  --comb_res_mult                         3
% 3.50/0.98  --comb_sup_mult                         2
% 3.50/0.98  --comb_inst_mult                        10
% 3.50/0.98  
% 3.50/0.98  ------ Debug Options
% 3.50/0.98  
% 3.50/0.98  --dbg_backtrace                         false
% 3.50/0.98  --dbg_dump_prop_clauses                 false
% 3.50/0.98  --dbg_dump_prop_clauses_file            -
% 3.50/0.98  --dbg_out_stat                          false
% 3.50/0.98  
% 3.50/0.98  
% 3.50/0.98  
% 3.50/0.98  
% 3.50/0.98  ------ Proving...
% 3.50/0.98  
% 3.50/0.98  
% 3.50/0.98  % SZS status Theorem for theBenchmark.p
% 3.50/0.98  
% 3.50/0.98   Resolution empty clause
% 3.50/0.98  
% 3.50/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.50/0.98  
% 3.50/0.98  fof(f7,axiom,(
% 3.50/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 3.50/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.50/0.99  
% 3.50/0.99  fof(f14,plain,(
% 3.50/0.99    ! [X0,X1,X2] : ((r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 3.50/0.99    inference(ennf_transformation,[],[f7])).
% 3.50/0.99  
% 3.50/0.99  fof(f15,plain,(
% 3.50/0.99    ! [X0,X1,X2] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 3.50/0.99    inference(flattening,[],[f14])).
% 3.50/0.99  
% 3.50/0.99  fof(f28,plain,(
% 3.50/0.99    ( ! [X2,X0,X1] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 3.50/0.99    inference(cnf_transformation,[],[f15])).
% 3.50/0.99  
% 3.50/0.99  fof(f9,conjecture,(
% 3.50/0.99    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)))),
% 3.50/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.50/0.99  
% 3.50/0.99  fof(f10,negated_conjecture,(
% 3.50/0.99    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)))),
% 3.50/0.99    inference(negated_conjecture,[],[f9])).
% 3.50/0.99  
% 3.50/0.99  fof(f18,plain,(
% 3.50/0.99    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 3.50/0.99    inference(ennf_transformation,[],[f10])).
% 3.50/0.99  
% 3.50/0.99  fof(f19,plain,(
% 3.50/0.99    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 3.50/0.99    inference(flattening,[],[f18])).
% 3.50/0.99  
% 3.50/0.99  fof(f20,plain,(
% 3.50/0.99    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 3.50/0.99    introduced(choice_axiom,[])).
% 3.50/0.99  
% 3.50/0.99  fof(f21,plain,(
% 3.50/0.99    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 3.50/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f20])).
% 3.50/0.99  
% 3.50/0.99  fof(f30,plain,(
% 3.50/0.99    v1_relat_1(sK2)),
% 3.50/0.99    inference(cnf_transformation,[],[f21])).
% 3.50/0.99  
% 3.50/0.99  fof(f3,axiom,(
% 3.50/0.99    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 3.50/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.50/0.99  
% 3.50/0.99  fof(f12,plain,(
% 3.50/0.99    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 3.50/0.99    inference(ennf_transformation,[],[f3])).
% 3.50/0.99  
% 3.50/0.99  fof(f13,plain,(
% 3.50/0.99    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 3.50/0.99    inference(flattening,[],[f12])).
% 3.50/0.99  
% 3.50/0.99  fof(f24,plain,(
% 3.50/0.99    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 3.50/0.99    inference(cnf_transformation,[],[f13])).
% 3.50/0.99  
% 3.50/0.99  fof(f6,axiom,(
% 3.50/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.50/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.50/0.99  
% 3.50/0.99  fof(f27,plain,(
% 3.50/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.50/0.99    inference(cnf_transformation,[],[f6])).
% 3.50/0.99  
% 3.50/0.99  fof(f5,axiom,(
% 3.50/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.50/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.50/0.99  
% 3.50/0.99  fof(f26,plain,(
% 3.50/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.50/0.99    inference(cnf_transformation,[],[f5])).
% 3.50/0.99  
% 3.50/0.99  fof(f33,plain,(
% 3.50/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 3.50/0.99    inference(definition_unfolding,[],[f27,f26])).
% 3.50/0.99  
% 3.50/0.99  fof(f36,plain,(
% 3.50/0.99    ( ! [X2,X0,X1] : (r1_tarski(X0,k1_setfam_1(k1_enumset1(X1,X1,X2))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 3.50/0.99    inference(definition_unfolding,[],[f24,f33])).
% 3.50/0.99  
% 3.50/0.99  fof(f4,axiom,(
% 3.50/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 3.50/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.50/0.99  
% 3.50/0.99  fof(f25,plain,(
% 3.50/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 3.50/0.99    inference(cnf_transformation,[],[f4])).
% 3.50/0.99  
% 3.50/0.99  fof(f37,plain,(
% 3.50/0.99    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 3.50/0.99    inference(definition_unfolding,[],[f25,f26,f26])).
% 3.50/0.99  
% 3.50/0.99  fof(f32,plain,(
% 3.50/0.99    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1))),
% 3.50/0.99    inference(cnf_transformation,[],[f21])).
% 3.50/0.99  
% 3.50/0.99  fof(f39,plain,(
% 3.50/0.99    ~r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k1_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),sK1)))),
% 3.50/0.99    inference(definition_unfolding,[],[f32,f33,f33])).
% 3.50/0.99  
% 3.50/0.99  fof(f1,axiom,(
% 3.50/0.99    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 3.50/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.50/0.99  
% 3.50/0.99  fof(f22,plain,(
% 3.50/0.99    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 3.50/0.99    inference(cnf_transformation,[],[f1])).
% 3.50/0.99  
% 3.50/0.99  fof(f34,plain,(
% 3.50/0.99    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X0)) )),
% 3.50/0.99    inference(definition_unfolding,[],[f22,f33])).
% 3.50/0.99  
% 3.50/0.99  fof(f8,axiom,(
% 3.50/0.99    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0)))),
% 3.50/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.50/0.99  
% 3.50/0.99  fof(f16,plain,(
% 3.50/0.99    ! [X0,X1] : (k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.50/0.99    inference(ennf_transformation,[],[f8])).
% 3.50/0.99  
% 3.50/0.99  fof(f17,plain,(
% 3.50/0.99    ! [X0,X1] : (k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.50/0.99    inference(flattening,[],[f16])).
% 3.50/0.99  
% 3.50/0.99  fof(f29,plain,(
% 3.50/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.50/0.99    inference(cnf_transformation,[],[f17])).
% 3.50/0.99  
% 3.50/0.99  fof(f38,plain,(
% 3.50/0.99    ( ! [X0,X1] : (k1_setfam_1(k1_enumset1(X0,X0,k9_relat_1(X1,k1_relat_1(X1)))) = k9_relat_1(X1,k10_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.50/0.99    inference(definition_unfolding,[],[f29,f33])).
% 3.50/0.99  
% 3.50/0.99  fof(f31,plain,(
% 3.50/0.99    v1_funct_1(sK2)),
% 3.50/0.99    inference(cnf_transformation,[],[f21])).
% 3.50/0.99  
% 3.50/0.99  fof(f2,axiom,(
% 3.50/0.99    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) => r1_tarski(X0,X1))),
% 3.50/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.50/0.99  
% 3.50/0.99  fof(f11,plain,(
% 3.50/0.99    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 3.50/0.99    inference(ennf_transformation,[],[f2])).
% 3.50/0.99  
% 3.50/0.99  fof(f23,plain,(
% 3.50/0.99    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2))) )),
% 3.50/0.99    inference(cnf_transformation,[],[f11])).
% 3.50/0.99  
% 3.50/0.99  fof(f35,plain,(
% 3.50/0.99    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k1_setfam_1(k1_enumset1(X1,X1,X2)))) )),
% 3.50/0.99    inference(definition_unfolding,[],[f23,f33])).
% 3.50/0.99  
% 3.50/0.99  cnf(c_4,plain,
% 3.50/0.99      ( ~ r1_tarski(X0,X1)
% 3.50/0.99      | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
% 3.50/0.99      | ~ v1_relat_1(X2) ),
% 3.50/0.99      inference(cnf_transformation,[],[f28]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_8,negated_conjecture,
% 3.50/0.99      ( v1_relat_1(sK2) ),
% 3.50/0.99      inference(cnf_transformation,[],[f30]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_107,plain,
% 3.50/0.99      ( ~ r1_tarski(X0,X1)
% 3.50/0.99      | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
% 3.50/0.99      | sK2 != X2 ),
% 3.50/0.99      inference(resolution_lifted,[status(thm)],[c_4,c_8]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_108,plain,
% 3.50/0.99      ( ~ r1_tarski(X0,X1) | r1_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) ),
% 3.50/0.99      inference(unflattening,[status(thm)],[c_107]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_163,plain,
% 3.50/0.99      ( ~ r1_tarski(X0_39,X1_39)
% 3.50/0.99      | r1_tarski(k9_relat_1(sK2,X0_39),k9_relat_1(sK2,X1_39)) ),
% 3.50/0.99      inference(subtyping,[status(esa)],[c_108]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_289,plain,
% 3.50/0.99      ( r1_tarski(X0_39,X1_39) != iProver_top
% 3.50/0.99      | r1_tarski(k9_relat_1(sK2,X0_39),k9_relat_1(sK2,X1_39)) = iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_163]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_2,plain,
% 3.50/0.99      ( ~ r1_tarski(X0,X1)
% 3.50/0.99      | ~ r1_tarski(X0,X2)
% 3.50/0.99      | r1_tarski(X0,k1_setfam_1(k1_enumset1(X2,X2,X1))) ),
% 3.50/0.99      inference(cnf_transformation,[],[f36]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_167,plain,
% 3.50/0.99      ( ~ r1_tarski(X0_39,X1_39)
% 3.50/0.99      | ~ r1_tarski(X0_39,X2_39)
% 3.50/0.99      | r1_tarski(X0_39,k1_setfam_1(k1_enumset1(X2_39,X2_39,X1_39))) ),
% 3.50/0.99      inference(subtyping,[status(esa)],[c_2]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_287,plain,
% 3.50/0.99      ( r1_tarski(X0_39,X1_39) != iProver_top
% 3.50/0.99      | r1_tarski(X0_39,X2_39) != iProver_top
% 3.50/0.99      | r1_tarski(X0_39,k1_setfam_1(k1_enumset1(X2_39,X2_39,X1_39))) = iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_167]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_3,plain,
% 3.50/0.99      ( k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
% 3.50/0.99      inference(cnf_transformation,[],[f37]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_166,plain,
% 3.50/0.99      ( k1_enumset1(X0_39,X0_39,X1_39) = k1_enumset1(X1_39,X1_39,X0_39) ),
% 3.50/0.99      inference(subtyping,[status(esa)],[c_3]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_6,negated_conjecture,
% 3.50/0.99      ( ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k1_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),sK1))) ),
% 3.50/0.99      inference(cnf_transformation,[],[f39]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_165,negated_conjecture,
% 3.50/0.99      ( ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k1_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),sK1))) ),
% 3.50/0.99      inference(subtyping,[status(esa)],[c_6]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_288,plain,
% 3.50/0.99      ( r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k1_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),sK1))) != iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_165]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_388,plain,
% 3.50/0.99      ( r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0)))) != iProver_top ),
% 3.50/0.99      inference(demodulation,[status(thm)],[c_166,c_288]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_950,plain,
% 3.50/0.99      ( r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))),k9_relat_1(sK2,sK0)) != iProver_top
% 3.50/0.99      | r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))),sK1) != iProver_top ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_287,c_388]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_0,plain,
% 3.50/0.99      ( r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X0) ),
% 3.50/0.99      inference(cnf_transformation,[],[f34]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_169,plain,
% 3.50/0.99      ( r1_tarski(k1_setfam_1(k1_enumset1(X0_39,X0_39,X1_39)),X0_39) ),
% 3.50/0.99      inference(subtyping,[status(esa)],[c_0]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_285,plain,
% 3.50/0.99      ( r1_tarski(k1_setfam_1(k1_enumset1(X0_39,X0_39,X1_39)),X0_39) = iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_169]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_623,plain,
% 3.50/0.99      ( r1_tarski(k1_setfam_1(k1_enumset1(X0_39,X0_39,X1_39)),X1_39) = iProver_top ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_166,c_285]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_5,plain,
% 3.50/0.99      ( ~ v1_funct_1(X0)
% 3.50/0.99      | ~ v1_relat_1(X0)
% 3.50/0.99      | k1_setfam_1(k1_enumset1(X1,X1,k9_relat_1(X0,k1_relat_1(X0)))) = k9_relat_1(X0,k10_relat_1(X0,X1)) ),
% 3.50/0.99      inference(cnf_transformation,[],[f38]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_7,negated_conjecture,
% 3.50/0.99      ( v1_funct_1(sK2) ),
% 3.50/0.99      inference(cnf_transformation,[],[f31]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_95,plain,
% 3.50/0.99      ( ~ v1_relat_1(X0)
% 3.50/0.99      | k1_setfam_1(k1_enumset1(X1,X1,k9_relat_1(X0,k1_relat_1(X0)))) = k9_relat_1(X0,k10_relat_1(X0,X1))
% 3.50/0.99      | sK2 != X0 ),
% 3.50/0.99      inference(resolution_lifted,[status(thm)],[c_5,c_7]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_96,plain,
% 3.50/0.99      ( ~ v1_relat_1(sK2)
% 3.50/0.99      | k1_setfam_1(k1_enumset1(X0,X0,k9_relat_1(sK2,k1_relat_1(sK2)))) = k9_relat_1(sK2,k10_relat_1(sK2,X0)) ),
% 3.50/0.99      inference(unflattening,[status(thm)],[c_95]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_100,plain,
% 3.50/0.99      ( k1_setfam_1(k1_enumset1(X0,X0,k9_relat_1(sK2,k1_relat_1(sK2)))) = k9_relat_1(sK2,k10_relat_1(sK2,X0)) ),
% 3.50/0.99      inference(global_propositional_subsumption,[status(thm)],[c_96,c_8]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_164,plain,
% 3.50/0.99      ( k1_setfam_1(k1_enumset1(X0_39,X0_39,k9_relat_1(sK2,k1_relat_1(sK2)))) = k9_relat_1(sK2,k10_relat_1(sK2,X0_39)) ),
% 3.50/0.99      inference(subtyping,[status(esa)],[c_100]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1,plain,
% 3.50/0.99      ( r1_tarski(X0,X1) | ~ r1_tarski(X0,k1_setfam_1(k1_enumset1(X1,X1,X2))) ),
% 3.50/0.99      inference(cnf_transformation,[],[f35]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_168,plain,
% 3.50/0.99      ( r1_tarski(X0_39,X1_39)
% 3.50/0.99      | ~ r1_tarski(X0_39,k1_setfam_1(k1_enumset1(X1_39,X1_39,X2_39))) ),
% 3.50/0.99      inference(subtyping,[status(esa)],[c_1]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_286,plain,
% 3.50/0.99      ( r1_tarski(X0_39,X1_39) = iProver_top
% 3.50/0.99      | r1_tarski(X0_39,k1_setfam_1(k1_enumset1(X1_39,X1_39,X2_39))) != iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_168]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_801,plain,
% 3.50/0.99      ( r1_tarski(X0_39,X1_39) = iProver_top
% 3.50/0.99      | r1_tarski(X0_39,k9_relat_1(sK2,k10_relat_1(sK2,X1_39))) != iProver_top ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_164,c_286]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1167,plain,
% 3.50/0.99      ( r1_tarski(X0_39,k10_relat_1(sK2,X1_39)) != iProver_top
% 3.50/0.99      | r1_tarski(k9_relat_1(sK2,X0_39),X1_39) = iProver_top ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_289,c_801]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1716,plain,
% 3.50/0.99      ( r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(X0_39,X0_39,k10_relat_1(sK2,X1_39)))),X1_39) = iProver_top ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_623,c_1167]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_5971,plain,
% 3.50/0.99      ( r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))),k9_relat_1(sK2,sK0)) != iProver_top ),
% 3.50/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_950,c_1716]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_5973,plain,
% 3.50/0.99      ( r1_tarski(k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1))),sK0) != iProver_top ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_289,c_5971]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_6867,plain,
% 3.50/0.99      ( $false ),
% 3.50/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_5973,c_285]) ).
% 3.50/0.99  
% 3.50/0.99  
% 3.50/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.50/0.99  
% 3.50/0.99  ------                               Statistics
% 3.50/0.99  
% 3.50/0.99  ------ General
% 3.50/0.99  
% 3.50/0.99  abstr_ref_over_cycles:                  0
% 3.50/0.99  abstr_ref_under_cycles:                 0
% 3.50/0.99  gc_basic_clause_elim:                   0
% 3.50/0.99  forced_gc_time:                         0
% 3.50/0.99  parsing_time:                           0.012
% 3.50/0.99  unif_index_cands_time:                  0.
% 3.50/0.99  unif_index_add_time:                    0.
% 3.50/0.99  orderings_time:                         0.
% 3.50/0.99  out_proof_time:                         0.006
% 3.50/0.99  total_time:                             0.315
% 3.50/0.99  num_of_symbols:                         42
% 3.50/0.99  num_of_terms:                           13394
% 3.50/0.99  
% 3.50/0.99  ------ Preprocessing
% 3.50/0.99  
% 3.50/0.99  num_of_splits:                          0
% 3.50/0.99  num_of_split_atoms:                     0
% 3.50/0.99  num_of_reused_defs:                     0
% 3.50/0.99  num_eq_ax_congr_red:                    4
% 3.50/0.99  num_of_sem_filtered_clauses:            1
% 3.50/0.99  num_of_subtypes:                        3
% 3.50/0.99  monotx_restored_types:                  0
% 3.50/0.99  sat_num_of_epr_types:                   0
% 3.50/0.99  sat_num_of_non_cyclic_types:            0
% 3.50/0.99  sat_guarded_non_collapsed_types:        0
% 3.50/0.99  num_pure_diseq_elim:                    0
% 3.50/0.99  simp_replaced_by:                       0
% 3.50/0.99  res_preprocessed:                       49
% 3.50/0.99  prep_upred:                             0
% 3.50/0.99  prep_unflattend:                        2
% 3.50/0.99  smt_new_axioms:                         0
% 3.50/0.99  pred_elim_cands:                        1
% 3.50/0.99  pred_elim:                              2
% 3.50/0.99  pred_elim_cl:                           2
% 3.50/0.99  pred_elim_cycles:                       4
% 3.50/0.99  merged_defs:                            0
% 3.50/0.99  merged_defs_ncl:                        0
% 3.50/0.99  bin_hyper_res:                          0
% 3.50/0.99  prep_cycles:                            4
% 3.50/0.99  pred_elim_time:                         0.
% 3.50/0.99  splitting_time:                         0.
% 3.50/0.99  sem_filter_time:                        0.
% 3.50/0.99  monotx_time:                            0.
% 3.50/0.99  subtype_inf_time:                       0.
% 3.50/0.99  
% 3.50/0.99  ------ Problem properties
% 3.50/0.99  
% 3.50/0.99  clauses:                                7
% 3.50/0.99  conjectures:                            1
% 3.50/0.99  epr:                                    0
% 3.50/0.99  horn:                                   7
% 3.50/0.99  ground:                                 1
% 3.50/0.99  unary:                                  4
% 3.50/0.99  binary:                                 2
% 3.50/0.99  lits:                                   11
% 3.50/0.99  lits_eq:                                2
% 3.50/0.99  fd_pure:                                0
% 3.50/0.99  fd_pseudo:                              0
% 3.50/0.99  fd_cond:                                0
% 3.50/0.99  fd_pseudo_cond:                         0
% 3.50/0.99  ac_symbols:                             0
% 3.50/0.99  
% 3.50/0.99  ------ Propositional Solver
% 3.50/0.99  
% 3.50/0.99  prop_solver_calls:                      28
% 3.50/0.99  prop_fast_solver_calls:                 259
% 3.50/0.99  smt_solver_calls:                       0
% 3.50/0.99  smt_fast_solver_calls:                  0
% 3.50/0.99  prop_num_of_clauses:                    3611
% 3.50/0.99  prop_preprocess_simplified:             7725
% 3.50/0.99  prop_fo_subsumed:                       1
% 3.50/0.99  prop_solver_time:                       0.
% 3.50/0.99  smt_solver_time:                        0.
% 3.50/0.99  smt_fast_solver_time:                   0.
% 3.50/0.99  prop_fast_solver_time:                  0.
% 3.50/0.99  prop_unsat_core_time:                   0.
% 3.50/0.99  
% 3.50/0.99  ------ QBF
% 3.50/0.99  
% 3.50/0.99  qbf_q_res:                              0
% 3.50/0.99  qbf_num_tautologies:                    0
% 3.50/0.99  qbf_prep_cycles:                        0
% 3.50/0.99  
% 3.50/0.99  ------ BMC1
% 3.50/0.99  
% 3.50/0.99  bmc1_current_bound:                     -1
% 3.50/0.99  bmc1_last_solved_bound:                 -1
% 3.50/0.99  bmc1_unsat_core_size:                   -1
% 3.50/0.99  bmc1_unsat_core_parents_size:           -1
% 3.50/0.99  bmc1_merge_next_fun:                    0
% 3.50/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.50/0.99  
% 3.50/0.99  ------ Instantiation
% 3.50/0.99  
% 3.50/0.99  inst_num_of_clauses:                    915
% 3.50/0.99  inst_num_in_passive:                    452
% 3.50/0.99  inst_num_in_active:                     256
% 3.50/0.99  inst_num_in_unprocessed:                208
% 3.50/0.99  inst_num_of_loops:                      270
% 3.50/0.99  inst_num_of_learning_restarts:          0
% 3.50/0.99  inst_num_moves_active_passive:          12
% 3.50/0.99  inst_lit_activity:                      0
% 3.50/0.99  inst_lit_activity_moves:                0
% 3.50/0.99  inst_num_tautologies:                   0
% 3.50/0.99  inst_num_prop_implied:                  0
% 3.50/0.99  inst_num_existing_simplified:           0
% 3.50/0.99  inst_num_eq_res_simplified:             0
% 3.50/0.99  inst_num_child_elim:                    0
% 3.50/0.99  inst_num_of_dismatching_blockings:      464
% 3.50/0.99  inst_num_of_non_proper_insts:           713
% 3.50/0.99  inst_num_of_duplicates:                 0
% 3.50/0.99  inst_inst_num_from_inst_to_res:         0
% 3.50/0.99  inst_dismatching_checking_time:         0.
% 3.50/0.99  
% 3.50/0.99  ------ Resolution
% 3.50/0.99  
% 3.50/0.99  res_num_of_clauses:                     0
% 3.50/0.99  res_num_in_passive:                     0
% 3.50/0.99  res_num_in_active:                      0
% 3.50/0.99  res_num_of_loops:                       53
% 3.50/0.99  res_forward_subset_subsumed:            42
% 3.50/0.99  res_backward_subset_subsumed:           2
% 3.50/0.99  res_forward_subsumed:                   0
% 3.50/0.99  res_backward_subsumed:                  0
% 3.50/0.99  res_forward_subsumption_resolution:     0
% 3.50/0.99  res_backward_subsumption_resolution:    0
% 3.50/0.99  res_clause_to_clause_subsumption:       1033
% 3.50/0.99  res_orphan_elimination:                 0
% 3.50/0.99  res_tautology_del:                      37
% 3.50/0.99  res_num_eq_res_simplified:              0
% 3.50/0.99  res_num_sel_changes:                    0
% 3.50/0.99  res_moves_from_active_to_pass:          0
% 3.50/0.99  
% 3.50/0.99  ------ Superposition
% 3.50/0.99  
% 3.50/0.99  sup_time_total:                         0.
% 3.50/0.99  sup_time_generating:                    0.
% 3.50/0.99  sup_time_sim_full:                      0.
% 3.50/0.99  sup_time_sim_immed:                     0.
% 3.50/0.99  
% 3.50/0.99  sup_num_of_clauses:                     193
% 3.50/0.99  sup_num_in_active:                      51
% 3.50/0.99  sup_num_in_passive:                     142
% 3.50/0.99  sup_num_of_loops:                       52
% 3.50/0.99  sup_fw_superposition:                   214
% 3.50/0.99  sup_bw_superposition:                   139
% 3.50/0.99  sup_immediate_simplified:               21
% 3.50/0.99  sup_given_eliminated:                   0
% 3.50/0.99  comparisons_done:                       0
% 3.50/0.99  comparisons_avoided:                    0
% 3.50/0.99  
% 3.50/0.99  ------ Simplifications
% 3.50/0.99  
% 3.50/0.99  
% 3.50/0.99  sim_fw_subset_subsumed:                 0
% 3.50/0.99  sim_bw_subset_subsumed:                 0
% 3.50/0.99  sim_fw_subsumed:                        18
% 3.50/0.99  sim_bw_subsumed:                        3
% 3.50/0.99  sim_fw_subsumption_res:                 2
% 3.50/0.99  sim_bw_subsumption_res:                 0
% 3.50/0.99  sim_tautology_del:                      3
% 3.50/0.99  sim_eq_tautology_del:                   0
% 3.50/0.99  sim_eq_res_simp:                        0
% 3.50/0.99  sim_fw_demodulated:                     0
% 3.50/0.99  sim_bw_demodulated:                     1
% 3.50/0.99  sim_light_normalised:                   0
% 3.50/0.99  sim_joinable_taut:                      0
% 3.50/0.99  sim_joinable_simp:                      0
% 3.50/0.99  sim_ac_normalised:                      0
% 3.50/0.99  sim_smt_subsumption:                    0
% 3.50/0.99  
%------------------------------------------------------------------------------
