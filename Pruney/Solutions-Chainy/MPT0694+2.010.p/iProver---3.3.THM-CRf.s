%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:51:57 EST 2020

% Result     : Theorem 3.55s
% Output     : CNFRefutation 3.55s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 189 expanded)
%              Number of clauses        :   31 (  44 expanded)
%              Number of leaves         :   10 (  49 expanded)
%              Depth                    :   13
%              Number of atoms          :  139 ( 337 expanded)
%              Number of equality atoms :   52 ( 132 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f15])).

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

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k9_relat_1(X2,k1_setfam_1(k1_enumset1(X0,X0,X1))),k1_setfam_1(k1_enumset1(k9_relat_1(X2,X0),k9_relat_1(X2,X0),k9_relat_1(X2,X1))))
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f28,f33,f33])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f37,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(definition_unfolding,[],[f25,f26,f26])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k1_setfam_1(k1_enumset1(X1,X1,X2))) ) ),
    inference(definition_unfolding,[],[f22,f33])).

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

fof(f31,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f8,axiom,(
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
    inference(ennf_transformation,[],[f8])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f24,f33])).

fof(f30,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f21])).

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
    ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f39,plain,(
    ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k1_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),sK1))) ),
    inference(definition_unfolding,[],[f32,f33,f33])).

cnf(c_4,plain,
    ( r1_tarski(k9_relat_1(X0,k1_setfam_1(k1_enumset1(X1,X1,X2))),k1_setfam_1(k1_enumset1(k9_relat_1(X0,X1),k9_relat_1(X0,X1),k9_relat_1(X0,X2))))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_249,plain,
    ( r1_tarski(k9_relat_1(X0,k1_setfam_1(k1_enumset1(X1,X1,X2))),k1_setfam_1(k1_enumset1(k9_relat_1(X0,X1),k9_relat_1(X0,X1),k9_relat_1(X0,X2)))) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3,plain,
    ( k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_0,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(X0,k1_setfam_1(k1_enumset1(X1,X1,X2))) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_252,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(X0,k1_setfam_1(k1_enumset1(X1,X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_665,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(X0,k1_setfam_1(k1_enumset1(X2,X2,X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_252])).

cnf(c_978,plain,
    ( r1_tarski(k9_relat_1(X0,k1_setfam_1(k1_enumset1(X1,X1,X2))),k9_relat_1(X0,X2)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_249,c_665])).

cnf(c_7,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_246,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_5,plain,
    ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_248,plain,
    ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | k1_setfam_1(k1_enumset1(X0,X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_250,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_751,plain,
    ( k1_setfam_1(k1_enumset1(k9_relat_1(X0,k10_relat_1(X0,X1)),k9_relat_1(X0,k10_relat_1(X0,X1)),X1)) = k9_relat_1(X0,k10_relat_1(X0,X1))
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_248,c_250])).

cnf(c_1913,plain,
    ( k1_setfam_1(k1_enumset1(k9_relat_1(sK2,k10_relat_1(sK2,X0)),k9_relat_1(sK2,k10_relat_1(sK2,X0)),X0)) = k9_relat_1(sK2,k10_relat_1(sK2,X0))
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_246,c_751])).

cnf(c_8,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_9,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2087,plain,
    ( k1_setfam_1(k1_enumset1(k9_relat_1(sK2,k10_relat_1(sK2,X0)),k9_relat_1(sK2,k10_relat_1(sK2,X0)),X0)) = k9_relat_1(sK2,k10_relat_1(sK2,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1913,c_9])).

cnf(c_2101,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(X0,k9_relat_1(sK2,k10_relat_1(sK2,X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2087,c_665])).

cnf(c_2436,plain,
    ( r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(X0,X0,k10_relat_1(sK2,X1)))),X1) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_978,c_2101])).

cnf(c_3672,plain,
    ( r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(X0,X0,k10_relat_1(sK2,X1)))),X1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2436,c_9])).

cnf(c_976,plain,
    ( r1_tarski(k9_relat_1(X0,k1_setfam_1(k1_enumset1(X1,X1,X2))),k9_relat_1(X0,X1)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_249,c_252])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k1_setfam_1(k1_enumset1(X2,X2,X1))) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_251,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X0,k1_setfam_1(k1_enumset1(X2,X2,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_6,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k1_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),sK1))) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_247,plain,
    ( r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k1_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_394,plain,
    ( r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0)))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3,c_247])).

cnf(c_785,plain,
    ( r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))),k9_relat_1(sK2,sK0)) != iProver_top
    | r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))),sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_251,c_394])).

cnf(c_1124,plain,
    ( r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))),sK1) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_976,c_785])).

cnf(c_1293,plain,
    ( r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))),sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1124,c_9])).

cnf(c_3686,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_3672,c_1293])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:09:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.55/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.55/0.98  
% 3.55/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.55/0.98  
% 3.55/0.98  ------  iProver source info
% 3.55/0.98  
% 3.55/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.55/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.55/0.98  git: non_committed_changes: false
% 3.55/0.98  git: last_make_outside_of_git: false
% 3.55/0.98  
% 3.55/0.98  ------ 
% 3.55/0.98  ------ Parsing...
% 3.55/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.55/0.98  
% 3.55/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.55/0.98  
% 3.55/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.55/0.98  
% 3.55/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.55/0.98  ------ Proving...
% 3.55/0.98  ------ Problem Properties 
% 3.55/0.98  
% 3.55/0.98  
% 3.55/0.98  clauses                                 9
% 3.55/0.98  conjectures                             3
% 3.55/0.98  EPR                                     2
% 3.55/0.98  Horn                                    9
% 3.55/0.98  unary                                   4
% 3.55/0.98  binary                                  3
% 3.55/0.98  lits                                    16
% 3.55/0.98  lits eq                                 2
% 3.55/0.98  fd_pure                                 0
% 3.55/0.98  fd_pseudo                               0
% 3.55/0.98  fd_cond                                 0
% 3.55/0.98  fd_pseudo_cond                          0
% 3.55/0.98  AC symbols                              0
% 3.55/0.98  
% 3.55/0.98  ------ Input Options Time Limit: Unbounded
% 3.55/0.98  
% 3.55/0.98  
% 3.55/0.98  ------ 
% 3.55/0.98  Current options:
% 3.55/0.98  ------ 
% 3.55/0.98  
% 3.55/0.98  
% 3.55/0.98  
% 3.55/0.98  
% 3.55/0.98  ------ Proving...
% 3.55/0.98  
% 3.55/0.98  
% 3.55/0.98  % SZS status Theorem for theBenchmark.p
% 3.55/0.98  
% 3.55/0.98   Resolution empty clause
% 3.55/0.98  
% 3.55/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.55/0.98  
% 3.55/0.98  fof(f7,axiom,(
% 3.55/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 3.55/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.55/0.98  
% 3.55/0.98  fof(f15,plain,(
% 3.55/0.98    ! [X0,X1,X2] : (r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) | ~v1_relat_1(X2))),
% 3.55/0.98    inference(ennf_transformation,[],[f7])).
% 3.55/0.98  
% 3.55/0.98  fof(f28,plain,(
% 3.55/0.98    ( ! [X2,X0,X1] : (r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) | ~v1_relat_1(X2)) )),
% 3.55/0.98    inference(cnf_transformation,[],[f15])).
% 3.55/0.98  
% 3.55/0.98  fof(f6,axiom,(
% 3.55/0.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.55/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.55/0.98  
% 3.55/0.98  fof(f27,plain,(
% 3.55/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.55/0.98    inference(cnf_transformation,[],[f6])).
% 3.55/0.98  
% 3.55/0.98  fof(f5,axiom,(
% 3.55/0.98    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.55/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.55/0.98  
% 3.55/0.98  fof(f26,plain,(
% 3.55/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.55/0.98    inference(cnf_transformation,[],[f5])).
% 3.55/0.98  
% 3.55/0.98  fof(f33,plain,(
% 3.55/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 3.55/0.98    inference(definition_unfolding,[],[f27,f26])).
% 3.55/0.98  
% 3.55/0.98  fof(f38,plain,(
% 3.55/0.98    ( ! [X2,X0,X1] : (r1_tarski(k9_relat_1(X2,k1_setfam_1(k1_enumset1(X0,X0,X1))),k1_setfam_1(k1_enumset1(k9_relat_1(X2,X0),k9_relat_1(X2,X0),k9_relat_1(X2,X1)))) | ~v1_relat_1(X2)) )),
% 3.55/0.98    inference(definition_unfolding,[],[f28,f33,f33])).
% 3.55/0.98  
% 3.55/0.98  fof(f4,axiom,(
% 3.55/0.98    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 3.55/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.55/0.98  
% 3.55/0.98  fof(f25,plain,(
% 3.55/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 3.55/0.98    inference(cnf_transformation,[],[f4])).
% 3.55/0.98  
% 3.55/0.98  fof(f37,plain,(
% 3.55/0.98    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 3.55/0.98    inference(definition_unfolding,[],[f25,f26,f26])).
% 3.55/0.98  
% 3.55/0.98  fof(f1,axiom,(
% 3.55/0.98    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) => r1_tarski(X0,X1))),
% 3.55/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.55/0.98  
% 3.55/0.98  fof(f11,plain,(
% 3.55/0.98    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 3.55/0.98    inference(ennf_transformation,[],[f1])).
% 3.55/0.98  
% 3.55/0.98  fof(f22,plain,(
% 3.55/0.98    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2))) )),
% 3.55/0.98    inference(cnf_transformation,[],[f11])).
% 3.55/0.98  
% 3.55/0.98  fof(f34,plain,(
% 3.55/0.98    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k1_setfam_1(k1_enumset1(X1,X1,X2)))) )),
% 3.55/0.98    inference(definition_unfolding,[],[f22,f33])).
% 3.55/0.98  
% 3.55/0.98  fof(f9,conjecture,(
% 3.55/0.98    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)))),
% 3.55/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.55/0.98  
% 3.55/0.98  fof(f10,negated_conjecture,(
% 3.55/0.98    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)))),
% 3.55/0.98    inference(negated_conjecture,[],[f9])).
% 3.55/0.98  
% 3.55/0.98  fof(f18,plain,(
% 3.55/0.98    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 3.55/0.98    inference(ennf_transformation,[],[f10])).
% 3.55/0.98  
% 3.55/0.98  fof(f19,plain,(
% 3.55/0.98    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 3.55/0.98    inference(flattening,[],[f18])).
% 3.55/0.98  
% 3.55/0.98  fof(f20,plain,(
% 3.55/0.98    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 3.55/0.98    introduced(choice_axiom,[])).
% 3.55/0.98  
% 3.55/0.98  fof(f21,plain,(
% 3.55/0.98    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 3.55/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f20])).
% 3.55/0.98  
% 3.55/0.98  fof(f31,plain,(
% 3.55/0.98    v1_funct_1(sK2)),
% 3.55/0.98    inference(cnf_transformation,[],[f21])).
% 3.55/0.98  
% 3.55/0.98  fof(f8,axiom,(
% 3.55/0.98    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 3.55/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.55/0.98  
% 3.55/0.98  fof(f16,plain,(
% 3.55/0.98    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.55/0.98    inference(ennf_transformation,[],[f8])).
% 3.55/0.98  
% 3.55/0.98  fof(f17,plain,(
% 3.55/0.98    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.55/0.98    inference(flattening,[],[f16])).
% 3.55/0.98  
% 3.55/0.98  fof(f29,plain,(
% 3.55/0.98    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.55/0.98    inference(cnf_transformation,[],[f17])).
% 3.55/0.98  
% 3.55/0.98  fof(f3,axiom,(
% 3.55/0.98    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.55/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.55/0.98  
% 3.55/0.98  fof(f14,plain,(
% 3.55/0.98    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.55/0.98    inference(ennf_transformation,[],[f3])).
% 3.55/0.98  
% 3.55/0.98  fof(f24,plain,(
% 3.55/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 3.55/0.98    inference(cnf_transformation,[],[f14])).
% 3.55/0.98  
% 3.55/0.98  fof(f36,plain,(
% 3.55/0.98    ( ! [X0,X1] : (k1_setfam_1(k1_enumset1(X0,X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 3.55/0.98    inference(definition_unfolding,[],[f24,f33])).
% 3.55/0.98  
% 3.55/0.98  fof(f30,plain,(
% 3.55/0.98    v1_relat_1(sK2)),
% 3.55/0.98    inference(cnf_transformation,[],[f21])).
% 3.55/0.98  
% 3.55/0.98  fof(f2,axiom,(
% 3.55/0.98    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 3.55/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.55/0.98  
% 3.55/0.98  fof(f12,plain,(
% 3.55/0.98    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 3.55/0.98    inference(ennf_transformation,[],[f2])).
% 3.55/0.98  
% 3.55/0.98  fof(f13,plain,(
% 3.55/0.98    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 3.55/0.98    inference(flattening,[],[f12])).
% 3.55/0.98  
% 3.55/0.98  fof(f23,plain,(
% 3.55/0.98    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 3.55/0.98    inference(cnf_transformation,[],[f13])).
% 3.55/0.98  
% 3.55/0.98  fof(f35,plain,(
% 3.55/0.98    ( ! [X2,X0,X1] : (r1_tarski(X0,k1_setfam_1(k1_enumset1(X1,X1,X2))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 3.55/0.98    inference(definition_unfolding,[],[f23,f33])).
% 3.55/0.98  
% 3.55/0.98  fof(f32,plain,(
% 3.55/0.98    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1))),
% 3.55/0.98    inference(cnf_transformation,[],[f21])).
% 3.55/0.98  
% 3.55/0.98  fof(f39,plain,(
% 3.55/0.98    ~r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k1_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),sK1)))),
% 3.55/0.98    inference(definition_unfolding,[],[f32,f33,f33])).
% 3.55/0.98  
% 3.55/0.98  cnf(c_4,plain,
% 3.55/0.98      ( r1_tarski(k9_relat_1(X0,k1_setfam_1(k1_enumset1(X1,X1,X2))),k1_setfam_1(k1_enumset1(k9_relat_1(X0,X1),k9_relat_1(X0,X1),k9_relat_1(X0,X2))))
% 3.55/0.98      | ~ v1_relat_1(X0) ),
% 3.55/0.98      inference(cnf_transformation,[],[f38]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_249,plain,
% 3.55/0.98      ( r1_tarski(k9_relat_1(X0,k1_setfam_1(k1_enumset1(X1,X1,X2))),k1_setfam_1(k1_enumset1(k9_relat_1(X0,X1),k9_relat_1(X0,X1),k9_relat_1(X0,X2)))) = iProver_top
% 3.55/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.55/0.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_3,plain,
% 3.55/0.98      ( k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
% 3.55/0.98      inference(cnf_transformation,[],[f37]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_0,plain,
% 3.55/0.98      ( r1_tarski(X0,X1) | ~ r1_tarski(X0,k1_setfam_1(k1_enumset1(X1,X1,X2))) ),
% 3.55/0.98      inference(cnf_transformation,[],[f34]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_252,plain,
% 3.55/0.98      ( r1_tarski(X0,X1) = iProver_top
% 3.55/0.98      | r1_tarski(X0,k1_setfam_1(k1_enumset1(X1,X1,X2))) != iProver_top ),
% 3.55/0.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_665,plain,
% 3.55/0.98      ( r1_tarski(X0,X1) = iProver_top
% 3.55/0.98      | r1_tarski(X0,k1_setfam_1(k1_enumset1(X2,X2,X1))) != iProver_top ),
% 3.55/0.98      inference(superposition,[status(thm)],[c_3,c_252]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_978,plain,
% 3.55/0.98      ( r1_tarski(k9_relat_1(X0,k1_setfam_1(k1_enumset1(X1,X1,X2))),k9_relat_1(X0,X2)) = iProver_top
% 3.55/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.55/0.98      inference(superposition,[status(thm)],[c_249,c_665]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_7,negated_conjecture,
% 3.55/0.98      ( v1_funct_1(sK2) ),
% 3.55/0.98      inference(cnf_transformation,[],[f31]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_246,plain,
% 3.55/0.98      ( v1_funct_1(sK2) = iProver_top ),
% 3.55/0.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_5,plain,
% 3.55/0.98      ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
% 3.55/0.98      | ~ v1_funct_1(X0)
% 3.55/0.98      | ~ v1_relat_1(X0) ),
% 3.55/0.98      inference(cnf_transformation,[],[f29]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_248,plain,
% 3.55/0.98      ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1) = iProver_top
% 3.55/0.98      | v1_funct_1(X0) != iProver_top
% 3.55/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.55/0.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_2,plain,
% 3.55/0.98      ( ~ r1_tarski(X0,X1) | k1_setfam_1(k1_enumset1(X0,X0,X1)) = X0 ),
% 3.55/0.98      inference(cnf_transformation,[],[f36]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_250,plain,
% 3.55/0.98      ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = X0
% 3.55/0.98      | r1_tarski(X0,X1) != iProver_top ),
% 3.55/0.98      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_751,plain,
% 3.55/0.98      ( k1_setfam_1(k1_enumset1(k9_relat_1(X0,k10_relat_1(X0,X1)),k9_relat_1(X0,k10_relat_1(X0,X1)),X1)) = k9_relat_1(X0,k10_relat_1(X0,X1))
% 3.55/0.98      | v1_funct_1(X0) != iProver_top
% 3.55/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.55/0.98      inference(superposition,[status(thm)],[c_248,c_250]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_1913,plain,
% 3.55/0.98      ( k1_setfam_1(k1_enumset1(k9_relat_1(sK2,k10_relat_1(sK2,X0)),k9_relat_1(sK2,k10_relat_1(sK2,X0)),X0)) = k9_relat_1(sK2,k10_relat_1(sK2,X0))
% 3.55/0.98      | v1_relat_1(sK2) != iProver_top ),
% 3.55/0.98      inference(superposition,[status(thm)],[c_246,c_751]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_8,negated_conjecture,
% 3.55/0.98      ( v1_relat_1(sK2) ),
% 3.55/0.98      inference(cnf_transformation,[],[f30]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_9,plain,
% 3.55/0.98      ( v1_relat_1(sK2) = iProver_top ),
% 3.55/0.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_2087,plain,
% 3.55/0.98      ( k1_setfam_1(k1_enumset1(k9_relat_1(sK2,k10_relat_1(sK2,X0)),k9_relat_1(sK2,k10_relat_1(sK2,X0)),X0)) = k9_relat_1(sK2,k10_relat_1(sK2,X0)) ),
% 3.55/0.98      inference(global_propositional_subsumption,[status(thm)],[c_1913,c_9]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_2101,plain,
% 3.55/0.98      ( r1_tarski(X0,X1) = iProver_top
% 3.55/0.98      | r1_tarski(X0,k9_relat_1(sK2,k10_relat_1(sK2,X1))) != iProver_top ),
% 3.55/0.98      inference(superposition,[status(thm)],[c_2087,c_665]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_2436,plain,
% 3.55/0.98      ( r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(X0,X0,k10_relat_1(sK2,X1)))),X1) = iProver_top
% 3.55/0.98      | v1_relat_1(sK2) != iProver_top ),
% 3.55/0.98      inference(superposition,[status(thm)],[c_978,c_2101]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_3672,plain,
% 3.55/0.98      ( r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(X0,X0,k10_relat_1(sK2,X1)))),X1) = iProver_top ),
% 3.55/0.98      inference(global_propositional_subsumption,[status(thm)],[c_2436,c_9]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_976,plain,
% 3.55/0.98      ( r1_tarski(k9_relat_1(X0,k1_setfam_1(k1_enumset1(X1,X1,X2))),k9_relat_1(X0,X1)) = iProver_top
% 3.55/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.55/0.98      inference(superposition,[status(thm)],[c_249,c_252]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_1,plain,
% 3.55/0.98      ( ~ r1_tarski(X0,X1)
% 3.55/0.98      | ~ r1_tarski(X0,X2)
% 3.55/0.98      | r1_tarski(X0,k1_setfam_1(k1_enumset1(X2,X2,X1))) ),
% 3.55/0.98      inference(cnf_transformation,[],[f35]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_251,plain,
% 3.55/0.98      ( r1_tarski(X0,X1) != iProver_top
% 3.55/0.98      | r1_tarski(X0,X2) != iProver_top
% 3.55/0.98      | r1_tarski(X0,k1_setfam_1(k1_enumset1(X2,X2,X1))) = iProver_top ),
% 3.55/0.98      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_6,negated_conjecture,
% 3.55/0.98      ( ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k1_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),sK1))) ),
% 3.55/0.98      inference(cnf_transformation,[],[f39]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_247,plain,
% 3.55/0.98      ( r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k1_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),sK1))) != iProver_top ),
% 3.55/0.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_394,plain,
% 3.55/0.98      ( r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0)))) != iProver_top ),
% 3.55/0.98      inference(demodulation,[status(thm)],[c_3,c_247]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_785,plain,
% 3.55/0.98      ( r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))),k9_relat_1(sK2,sK0)) != iProver_top
% 3.55/0.98      | r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))),sK1) != iProver_top ),
% 3.55/0.98      inference(superposition,[status(thm)],[c_251,c_394]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_1124,plain,
% 3.55/0.98      ( r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))),sK1) != iProver_top
% 3.55/0.98      | v1_relat_1(sK2) != iProver_top ),
% 3.55/0.98      inference(superposition,[status(thm)],[c_976,c_785]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_1293,plain,
% 3.55/0.98      ( r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))),sK1) != iProver_top ),
% 3.55/0.98      inference(global_propositional_subsumption,[status(thm)],[c_1124,c_9]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_3686,plain,
% 3.55/0.98      ( $false ),
% 3.55/0.98      inference(superposition,[status(thm)],[c_3672,c_1293]) ).
% 3.55/0.98  
% 3.55/0.98  
% 3.55/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.55/0.98  
% 3.55/0.98  ------                               Statistics
% 3.55/0.98  
% 3.55/0.98  ------ Selected
% 3.55/0.98  
% 3.55/0.98  total_time:                             0.16
% 3.55/0.98  
%------------------------------------------------------------------------------
