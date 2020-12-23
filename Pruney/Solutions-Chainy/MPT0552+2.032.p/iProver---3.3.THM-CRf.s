%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:46:40 EST 2020

% Result     : Theorem 27.84s
% Output     : CNFRefutation 27.84s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 236 expanded)
%              Number of clauses        :   38 (  88 expanded)
%              Number of leaves         :    9 (  50 expanded)
%              Depth                    :   17
%              Number of atoms          :  122 ( 429 expanded)
%              Number of equality atoms :   59 ( 144 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f37,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f25,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f25])).

fof(f41,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f44,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f27,f33,f33])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f38,f33])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f32,f33])).

fof(f42,plain,(
    ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f26])).

fof(f48,plain,(
    ~ r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k9_relat_1(sK2,sK0),k4_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))) ),
    inference(definition_unfolding,[],[f42,f33,f33])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_395,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k7_relat_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_12,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_390,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_393,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_758,plain,
    ( k2_relat_1(k7_relat_1(k7_relat_1(X0,X1),X2)) = k9_relat_1(k7_relat_1(X0,X1),X2)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_395,c_393])).

cnf(c_2278,plain,
    ( k2_relat_1(k7_relat_1(k7_relat_1(sK2,X0),X1)) = k9_relat_1(k7_relat_1(sK2,X0),X1) ),
    inference(superposition,[status(thm)],[c_390,c_758])).

cnf(c_759,plain,
    ( k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0) ),
    inference(superposition,[status(thm)],[c_390,c_393])).

cnf(c_10,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(X0,X1)),k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_392,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(X0,X1)),k2_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_856,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(sK2,X0),X1)),k9_relat_1(sK2,X0)) = iProver_top
    | v1_relat_1(k7_relat_1(sK2,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_759,c_392])).

cnf(c_2652,plain,
    ( r1_tarski(k9_relat_1(k7_relat_1(sK2,X0),X1),k9_relat_1(sK2,X0)) = iProver_top
    | v1_relat_1(k7_relat_1(sK2,X0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2278,c_856])).

cnf(c_0,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k7_relat_1(k7_relat_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_394,plain,
    ( k7_relat_1(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k7_relat_1(k7_relat_1(X0,X1),X2)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1022,plain,
    ( k7_relat_1(sK2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k7_relat_1(k7_relat_1(sK2,X0),X1) ),
    inference(superposition,[status(thm)],[c_390,c_394])).

cnf(c_1027,plain,
    ( k7_relat_1(sK2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k7_relat_1(k7_relat_1(sK2,X1),X0) ),
    inference(superposition,[status(thm)],[c_0,c_1022])).

cnf(c_1137,plain,
    ( k7_relat_1(k7_relat_1(sK2,X0),X1) = k7_relat_1(k7_relat_1(sK2,X1),X0) ),
    inference(superposition,[status(thm)],[c_1027,c_1022])).

cnf(c_1147,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(sK2,X0),X1)),k2_relat_1(k7_relat_1(sK2,X1))) = iProver_top
    | v1_relat_1(k7_relat_1(sK2,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1137,c_392])).

cnf(c_1149,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(sK2,X0),X1)),k9_relat_1(sK2,X1)) = iProver_top
    | v1_relat_1(k7_relat_1(sK2,X1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1147,c_759])).

cnf(c_2651,plain,
    ( r1_tarski(k9_relat_1(k7_relat_1(sK2,X0),X1),k9_relat_1(sK2,X1)) = iProver_top
    | v1_relat_1(k7_relat_1(sK2,X1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2278,c_1149])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_396,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1033,plain,
    ( k9_relat_1(sK2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k2_relat_1(k7_relat_1(k7_relat_1(sK2,X0),X1)) ),
    inference(superposition,[status(thm)],[c_1022,c_759])).

cnf(c_11,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k9_relat_1(sK2,sK0),k4_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_391,plain,
    ( r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k9_relat_1(sK2,sK0),k4_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1382,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(sK2,sK0),sK1)),k4_xboole_0(k9_relat_1(sK2,sK0),k4_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1033,c_391])).

cnf(c_1469,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(sK2,sK0),sK1)),k9_relat_1(sK2,sK1)) != iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(sK2,sK0),sK1)),k9_relat_1(sK2,sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_396,c_1382])).

cnf(c_2655,plain,
    ( r1_tarski(k9_relat_1(k7_relat_1(sK2,sK0),sK1),k9_relat_1(sK2,sK1)) != iProver_top
    | r1_tarski(k9_relat_1(k7_relat_1(sK2,sK0),sK1),k9_relat_1(sK2,sK0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2278,c_1469])).

cnf(c_3508,plain,
    ( r1_tarski(k9_relat_1(k7_relat_1(sK2,sK0),sK1),k9_relat_1(sK2,sK0)) != iProver_top
    | v1_relat_1(k7_relat_1(sK2,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2651,c_2655])).

cnf(c_13,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_7461,plain,
    ( v1_relat_1(k7_relat_1(sK2,sK1))
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_7462,plain,
    ( v1_relat_1(k7_relat_1(sK2,sK1)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7461])).

cnf(c_60682,plain,
    ( r1_tarski(k9_relat_1(k7_relat_1(sK2,sK0),sK1),k9_relat_1(sK2,sK0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3508,c_13,c_7462])).

cnf(c_60686,plain,
    ( v1_relat_1(k7_relat_1(sK2,sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2652,c_60682])).

cnf(c_60689,plain,
    ( v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_395,c_60686])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_60689,c_13])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n009.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:17:11 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 27.84/3.92  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 27.84/3.92  
% 27.84/3.92  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 27.84/3.92  
% 27.84/3.92  ------  iProver source info
% 27.84/3.92  
% 27.84/3.92  git: date: 2020-06-30 10:37:57 +0100
% 27.84/3.92  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 27.84/3.92  git: non_committed_changes: false
% 27.84/3.92  git: last_make_outside_of_git: false
% 27.84/3.92  
% 27.84/3.92  ------ 
% 27.84/3.92  
% 27.84/3.92  ------ Input Options
% 27.84/3.92  
% 27.84/3.92  --out_options                           all
% 27.84/3.92  --tptp_safe_out                         true
% 27.84/3.92  --problem_path                          ""
% 27.84/3.92  --include_path                          ""
% 27.84/3.92  --clausifier                            res/vclausify_rel
% 27.84/3.92  --clausifier_options                    ""
% 27.84/3.92  --stdin                                 false
% 27.84/3.92  --stats_out                             all
% 27.84/3.92  
% 27.84/3.92  ------ General Options
% 27.84/3.92  
% 27.84/3.92  --fof                                   false
% 27.84/3.92  --time_out_real                         305.
% 27.84/3.92  --time_out_virtual                      -1.
% 27.84/3.92  --symbol_type_check                     false
% 27.84/3.92  --clausify_out                          false
% 27.84/3.92  --sig_cnt_out                           false
% 27.84/3.92  --trig_cnt_out                          false
% 27.84/3.92  --trig_cnt_out_tolerance                1.
% 27.84/3.92  --trig_cnt_out_sk_spl                   false
% 27.84/3.92  --abstr_cl_out                          false
% 27.84/3.92  
% 27.84/3.92  ------ Global Options
% 27.84/3.92  
% 27.84/3.92  --schedule                              default
% 27.84/3.92  --add_important_lit                     false
% 27.84/3.92  --prop_solver_per_cl                    1000
% 27.84/3.92  --min_unsat_core                        false
% 27.84/3.92  --soft_assumptions                      false
% 27.84/3.92  --soft_lemma_size                       3
% 27.84/3.92  --prop_impl_unit_size                   0
% 27.84/3.92  --prop_impl_unit                        []
% 27.84/3.92  --share_sel_clauses                     true
% 27.84/3.92  --reset_solvers                         false
% 27.84/3.92  --bc_imp_inh                            [conj_cone]
% 27.84/3.92  --conj_cone_tolerance                   3.
% 27.84/3.92  --extra_neg_conj                        none
% 27.84/3.92  --large_theory_mode                     true
% 27.84/3.92  --prolific_symb_bound                   200
% 27.84/3.92  --lt_threshold                          2000
% 27.84/3.92  --clause_weak_htbl                      true
% 27.84/3.92  --gc_record_bc_elim                     false
% 27.84/3.92  
% 27.84/3.92  ------ Preprocessing Options
% 27.84/3.92  
% 27.84/3.92  --preprocessing_flag                    true
% 27.84/3.92  --time_out_prep_mult                    0.1
% 27.84/3.92  --splitting_mode                        input
% 27.84/3.92  --splitting_grd                         true
% 27.84/3.92  --splitting_cvd                         false
% 27.84/3.92  --splitting_cvd_svl                     false
% 27.84/3.92  --splitting_nvd                         32
% 27.84/3.92  --sub_typing                            true
% 27.84/3.92  --prep_gs_sim                           true
% 27.84/3.92  --prep_unflatten                        true
% 27.84/3.92  --prep_res_sim                          true
% 27.84/3.92  --prep_upred                            true
% 27.84/3.92  --prep_sem_filter                       exhaustive
% 27.84/3.92  --prep_sem_filter_out                   false
% 27.84/3.92  --pred_elim                             true
% 27.84/3.92  --res_sim_input                         true
% 27.84/3.92  --eq_ax_congr_red                       true
% 27.84/3.92  --pure_diseq_elim                       true
% 27.84/3.92  --brand_transform                       false
% 27.84/3.92  --non_eq_to_eq                          false
% 27.84/3.92  --prep_def_merge                        true
% 27.84/3.92  --prep_def_merge_prop_impl              false
% 27.84/3.92  --prep_def_merge_mbd                    true
% 27.84/3.92  --prep_def_merge_tr_red                 false
% 27.84/3.92  --prep_def_merge_tr_cl                  false
% 27.84/3.92  --smt_preprocessing                     true
% 27.84/3.92  --smt_ac_axioms                         fast
% 27.84/3.92  --preprocessed_out                      false
% 27.84/3.92  --preprocessed_stats                    false
% 27.84/3.92  
% 27.84/3.92  ------ Abstraction refinement Options
% 27.84/3.92  
% 27.84/3.92  --abstr_ref                             []
% 27.84/3.92  --abstr_ref_prep                        false
% 27.84/3.92  --abstr_ref_until_sat                   false
% 27.84/3.92  --abstr_ref_sig_restrict                funpre
% 27.84/3.92  --abstr_ref_af_restrict_to_split_sk     false
% 27.84/3.92  --abstr_ref_under                       []
% 27.84/3.92  
% 27.84/3.92  ------ SAT Options
% 27.84/3.92  
% 27.84/3.92  --sat_mode                              false
% 27.84/3.92  --sat_fm_restart_options                ""
% 27.84/3.92  --sat_gr_def                            false
% 27.84/3.92  --sat_epr_types                         true
% 27.84/3.92  --sat_non_cyclic_types                  false
% 27.84/3.92  --sat_finite_models                     false
% 27.84/3.92  --sat_fm_lemmas                         false
% 27.84/3.92  --sat_fm_prep                           false
% 27.84/3.92  --sat_fm_uc_incr                        true
% 27.84/3.92  --sat_out_model                         small
% 27.84/3.92  --sat_out_clauses                       false
% 27.84/3.92  
% 27.84/3.92  ------ QBF Options
% 27.84/3.92  
% 27.84/3.92  --qbf_mode                              false
% 27.84/3.92  --qbf_elim_univ                         false
% 27.84/3.92  --qbf_dom_inst                          none
% 27.84/3.92  --qbf_dom_pre_inst                      false
% 27.84/3.92  --qbf_sk_in                             false
% 27.84/3.92  --qbf_pred_elim                         true
% 27.84/3.92  --qbf_split                             512
% 27.84/3.92  
% 27.84/3.92  ------ BMC1 Options
% 27.84/3.92  
% 27.84/3.92  --bmc1_incremental                      false
% 27.84/3.92  --bmc1_axioms                           reachable_all
% 27.84/3.92  --bmc1_min_bound                        0
% 27.84/3.92  --bmc1_max_bound                        -1
% 27.84/3.92  --bmc1_max_bound_default                -1
% 27.84/3.92  --bmc1_symbol_reachability              true
% 27.84/3.92  --bmc1_property_lemmas                  false
% 27.84/3.92  --bmc1_k_induction                      false
% 27.84/3.92  --bmc1_non_equiv_states                 false
% 27.84/3.92  --bmc1_deadlock                         false
% 27.84/3.92  --bmc1_ucm                              false
% 27.84/3.92  --bmc1_add_unsat_core                   none
% 27.84/3.92  --bmc1_unsat_core_children              false
% 27.84/3.92  --bmc1_unsat_core_extrapolate_axioms    false
% 27.84/3.92  --bmc1_out_stat                         full
% 27.84/3.92  --bmc1_ground_init                      false
% 27.84/3.92  --bmc1_pre_inst_next_state              false
% 27.84/3.92  --bmc1_pre_inst_state                   false
% 27.84/3.92  --bmc1_pre_inst_reach_state             false
% 27.84/3.92  --bmc1_out_unsat_core                   false
% 27.84/3.92  --bmc1_aig_witness_out                  false
% 27.84/3.92  --bmc1_verbose                          false
% 27.84/3.92  --bmc1_dump_clauses_tptp                false
% 27.84/3.92  --bmc1_dump_unsat_core_tptp             false
% 27.84/3.92  --bmc1_dump_file                        -
% 27.84/3.92  --bmc1_ucm_expand_uc_limit              128
% 27.84/3.92  --bmc1_ucm_n_expand_iterations          6
% 27.84/3.92  --bmc1_ucm_extend_mode                  1
% 27.84/3.92  --bmc1_ucm_init_mode                    2
% 27.84/3.92  --bmc1_ucm_cone_mode                    none
% 27.84/3.92  --bmc1_ucm_reduced_relation_type        0
% 27.84/3.92  --bmc1_ucm_relax_model                  4
% 27.84/3.92  --bmc1_ucm_full_tr_after_sat            true
% 27.84/3.92  --bmc1_ucm_expand_neg_assumptions       false
% 27.84/3.92  --bmc1_ucm_layered_model                none
% 27.84/3.92  --bmc1_ucm_max_lemma_size               10
% 27.84/3.92  
% 27.84/3.92  ------ AIG Options
% 27.84/3.92  
% 27.84/3.92  --aig_mode                              false
% 27.84/3.92  
% 27.84/3.92  ------ Instantiation Options
% 27.84/3.92  
% 27.84/3.92  --instantiation_flag                    true
% 27.84/3.92  --inst_sos_flag                         true
% 27.84/3.92  --inst_sos_phase                        true
% 27.84/3.92  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 27.84/3.92  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 27.84/3.92  --inst_lit_sel_side                     num_symb
% 27.84/3.92  --inst_solver_per_active                1400
% 27.84/3.92  --inst_solver_calls_frac                1.
% 27.84/3.92  --inst_passive_queue_type               priority_queues
% 27.84/3.92  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 27.84/3.92  --inst_passive_queues_freq              [25;2]
% 27.84/3.92  --inst_dismatching                      true
% 27.84/3.92  --inst_eager_unprocessed_to_passive     true
% 27.84/3.92  --inst_prop_sim_given                   true
% 27.84/3.92  --inst_prop_sim_new                     false
% 27.84/3.92  --inst_subs_new                         false
% 27.84/3.92  --inst_eq_res_simp                      false
% 27.84/3.92  --inst_subs_given                       false
% 27.84/3.92  --inst_orphan_elimination               true
% 27.84/3.92  --inst_learning_loop_flag               true
% 27.84/3.92  --inst_learning_start                   3000
% 27.84/3.92  --inst_learning_factor                  2
% 27.84/3.92  --inst_start_prop_sim_after_learn       3
% 27.84/3.92  --inst_sel_renew                        solver
% 27.84/3.92  --inst_lit_activity_flag                true
% 27.84/3.92  --inst_restr_to_given                   false
% 27.84/3.92  --inst_activity_threshold               500
% 27.84/3.92  --inst_out_proof                        true
% 27.84/3.92  
% 27.84/3.92  ------ Resolution Options
% 27.84/3.92  
% 27.84/3.92  --resolution_flag                       true
% 27.84/3.92  --res_lit_sel                           adaptive
% 27.84/3.92  --res_lit_sel_side                      none
% 27.84/3.92  --res_ordering                          kbo
% 27.84/3.92  --res_to_prop_solver                    active
% 27.84/3.92  --res_prop_simpl_new                    false
% 27.84/3.92  --res_prop_simpl_given                  true
% 27.84/3.92  --res_passive_queue_type                priority_queues
% 27.84/3.92  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 27.84/3.92  --res_passive_queues_freq               [15;5]
% 27.84/3.92  --res_forward_subs                      full
% 27.84/3.92  --res_backward_subs                     full
% 27.84/3.92  --res_forward_subs_resolution           true
% 27.84/3.92  --res_backward_subs_resolution          true
% 27.84/3.92  --res_orphan_elimination                true
% 27.84/3.92  --res_time_limit                        2.
% 27.84/3.92  --res_out_proof                         true
% 27.84/3.92  
% 27.84/3.92  ------ Superposition Options
% 27.84/3.92  
% 27.84/3.92  --superposition_flag                    true
% 27.84/3.92  --sup_passive_queue_type                priority_queues
% 27.84/3.92  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 27.84/3.92  --sup_passive_queues_freq               [8;1;4]
% 27.84/3.92  --demod_completeness_check              fast
% 27.84/3.92  --demod_use_ground                      true
% 27.84/3.92  --sup_to_prop_solver                    passive
% 27.84/3.92  --sup_prop_simpl_new                    true
% 27.84/3.92  --sup_prop_simpl_given                  true
% 27.84/3.92  --sup_fun_splitting                     true
% 27.84/3.92  --sup_smt_interval                      50000
% 27.84/3.92  
% 27.84/3.92  ------ Superposition Simplification Setup
% 27.84/3.92  
% 27.84/3.92  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 27.84/3.92  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 27.84/3.92  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 27.84/3.92  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 27.84/3.92  --sup_full_triv                         [TrivRules;PropSubs]
% 27.84/3.92  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 27.84/3.92  --sup_full_bw                           [BwDemod;BwSubsumption]
% 27.84/3.92  --sup_immed_triv                        [TrivRules]
% 27.84/3.92  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 27.84/3.92  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 27.84/3.92  --sup_immed_bw_main                     []
% 27.84/3.92  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 27.84/3.92  --sup_input_triv                        [Unflattening;TrivRules]
% 27.84/3.92  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 27.84/3.92  --sup_input_bw                          []
% 27.84/3.92  
% 27.84/3.92  ------ Combination Options
% 27.84/3.92  
% 27.84/3.92  --comb_res_mult                         3
% 27.84/3.92  --comb_sup_mult                         2
% 27.84/3.92  --comb_inst_mult                        10
% 27.84/3.92  
% 27.84/3.92  ------ Debug Options
% 27.84/3.92  
% 27.84/3.92  --dbg_backtrace                         false
% 27.84/3.92  --dbg_dump_prop_clauses                 false
% 27.84/3.92  --dbg_dump_prop_clauses_file            -
% 27.84/3.92  --dbg_out_stat                          false
% 27.84/3.92  ------ Parsing...
% 27.84/3.92  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 27.84/3.92  
% 27.84/3.92  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 27.84/3.92  
% 27.84/3.92  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 27.84/3.92  
% 27.84/3.92  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.84/3.92  ------ Proving...
% 27.84/3.92  ------ Problem Properties 
% 27.84/3.92  
% 27.84/3.92  
% 27.84/3.92  clauses                                 12
% 27.84/3.92  conjectures                             2
% 27.84/3.92  EPR                                     3
% 27.84/3.92  Horn                                    12
% 27.84/3.92  unary                                   5
% 27.84/3.92  binary                                  5
% 27.84/3.92  lits                                    21
% 27.84/3.92  lits eq                                 5
% 27.84/3.92  fd_pure                                 0
% 27.84/3.92  fd_pseudo                               0
% 27.84/3.92  fd_cond                                 0
% 27.84/3.92  fd_pseudo_cond                          1
% 27.84/3.92  AC symbols                              0
% 27.84/3.92  
% 27.84/3.92  ------ Schedule dynamic 5 is on 
% 27.84/3.92  
% 27.84/3.92  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 27.84/3.92  
% 27.84/3.92  
% 27.84/3.92  ------ 
% 27.84/3.92  Current options:
% 27.84/3.92  ------ 
% 27.84/3.92  
% 27.84/3.92  ------ Input Options
% 27.84/3.92  
% 27.84/3.92  --out_options                           all
% 27.84/3.92  --tptp_safe_out                         true
% 27.84/3.92  --problem_path                          ""
% 27.84/3.92  --include_path                          ""
% 27.84/3.92  --clausifier                            res/vclausify_rel
% 27.84/3.92  --clausifier_options                    ""
% 27.84/3.92  --stdin                                 false
% 27.84/3.92  --stats_out                             all
% 27.84/3.92  
% 27.84/3.92  ------ General Options
% 27.84/3.92  
% 27.84/3.92  --fof                                   false
% 27.84/3.92  --time_out_real                         305.
% 27.84/3.92  --time_out_virtual                      -1.
% 27.84/3.92  --symbol_type_check                     false
% 27.84/3.92  --clausify_out                          false
% 27.84/3.92  --sig_cnt_out                           false
% 27.84/3.92  --trig_cnt_out                          false
% 27.84/3.92  --trig_cnt_out_tolerance                1.
% 27.84/3.92  --trig_cnt_out_sk_spl                   false
% 27.84/3.92  --abstr_cl_out                          false
% 27.84/3.92  
% 27.84/3.92  ------ Global Options
% 27.84/3.92  
% 27.84/3.92  --schedule                              default
% 27.84/3.92  --add_important_lit                     false
% 27.84/3.92  --prop_solver_per_cl                    1000
% 27.84/3.92  --min_unsat_core                        false
% 27.84/3.92  --soft_assumptions                      false
% 27.84/3.92  --soft_lemma_size                       3
% 27.84/3.92  --prop_impl_unit_size                   0
% 27.84/3.92  --prop_impl_unit                        []
% 27.84/3.92  --share_sel_clauses                     true
% 27.84/3.92  --reset_solvers                         false
% 27.84/3.92  --bc_imp_inh                            [conj_cone]
% 27.84/3.92  --conj_cone_tolerance                   3.
% 27.84/3.92  --extra_neg_conj                        none
% 27.84/3.92  --large_theory_mode                     true
% 27.84/3.92  --prolific_symb_bound                   200
% 27.84/3.92  --lt_threshold                          2000
% 27.84/3.92  --clause_weak_htbl                      true
% 27.84/3.92  --gc_record_bc_elim                     false
% 27.84/3.92  
% 27.84/3.92  ------ Preprocessing Options
% 27.84/3.92  
% 27.84/3.92  --preprocessing_flag                    true
% 27.84/3.92  --time_out_prep_mult                    0.1
% 27.84/3.92  --splitting_mode                        input
% 27.84/3.92  --splitting_grd                         true
% 27.84/3.92  --splitting_cvd                         false
% 27.84/3.92  --splitting_cvd_svl                     false
% 27.84/3.92  --splitting_nvd                         32
% 27.84/3.92  --sub_typing                            true
% 27.84/3.92  --prep_gs_sim                           true
% 27.84/3.92  --prep_unflatten                        true
% 27.84/3.92  --prep_res_sim                          true
% 27.84/3.92  --prep_upred                            true
% 27.84/3.92  --prep_sem_filter                       exhaustive
% 27.84/3.92  --prep_sem_filter_out                   false
% 27.84/3.92  --pred_elim                             true
% 27.84/3.92  --res_sim_input                         true
% 27.84/3.92  --eq_ax_congr_red                       true
% 27.84/3.92  --pure_diseq_elim                       true
% 27.84/3.92  --brand_transform                       false
% 27.84/3.92  --non_eq_to_eq                          false
% 27.84/3.92  --prep_def_merge                        true
% 27.84/3.92  --prep_def_merge_prop_impl              false
% 27.84/3.92  --prep_def_merge_mbd                    true
% 27.84/3.92  --prep_def_merge_tr_red                 false
% 27.84/3.92  --prep_def_merge_tr_cl                  false
% 27.84/3.92  --smt_preprocessing                     true
% 27.84/3.92  --smt_ac_axioms                         fast
% 27.84/3.92  --preprocessed_out                      false
% 27.84/3.92  --preprocessed_stats                    false
% 27.84/3.92  
% 27.84/3.92  ------ Abstraction refinement Options
% 27.84/3.92  
% 27.84/3.92  --abstr_ref                             []
% 27.84/3.92  --abstr_ref_prep                        false
% 27.84/3.92  --abstr_ref_until_sat                   false
% 27.84/3.92  --abstr_ref_sig_restrict                funpre
% 27.84/3.92  --abstr_ref_af_restrict_to_split_sk     false
% 27.84/3.92  --abstr_ref_under                       []
% 27.84/3.92  
% 27.84/3.92  ------ SAT Options
% 27.84/3.92  
% 27.84/3.92  --sat_mode                              false
% 27.84/3.92  --sat_fm_restart_options                ""
% 27.84/3.92  --sat_gr_def                            false
% 27.84/3.92  --sat_epr_types                         true
% 27.84/3.92  --sat_non_cyclic_types                  false
% 27.84/3.92  --sat_finite_models                     false
% 27.84/3.92  --sat_fm_lemmas                         false
% 27.84/3.92  --sat_fm_prep                           false
% 27.84/3.92  --sat_fm_uc_incr                        true
% 27.84/3.92  --sat_out_model                         small
% 27.84/3.92  --sat_out_clauses                       false
% 27.84/3.92  
% 27.84/3.92  ------ QBF Options
% 27.84/3.92  
% 27.84/3.92  --qbf_mode                              false
% 27.84/3.92  --qbf_elim_univ                         false
% 27.84/3.92  --qbf_dom_inst                          none
% 27.84/3.92  --qbf_dom_pre_inst                      false
% 27.84/3.92  --qbf_sk_in                             false
% 27.84/3.92  --qbf_pred_elim                         true
% 27.84/3.92  --qbf_split                             512
% 27.84/3.92  
% 27.84/3.92  ------ BMC1 Options
% 27.84/3.92  
% 27.84/3.92  --bmc1_incremental                      false
% 27.84/3.92  --bmc1_axioms                           reachable_all
% 27.84/3.92  --bmc1_min_bound                        0
% 27.84/3.92  --bmc1_max_bound                        -1
% 27.84/3.92  --bmc1_max_bound_default                -1
% 27.84/3.92  --bmc1_symbol_reachability              true
% 27.84/3.92  --bmc1_property_lemmas                  false
% 27.84/3.92  --bmc1_k_induction                      false
% 27.84/3.92  --bmc1_non_equiv_states                 false
% 27.84/3.92  --bmc1_deadlock                         false
% 27.84/3.92  --bmc1_ucm                              false
% 27.84/3.92  --bmc1_add_unsat_core                   none
% 27.84/3.92  --bmc1_unsat_core_children              false
% 27.84/3.92  --bmc1_unsat_core_extrapolate_axioms    false
% 27.84/3.92  --bmc1_out_stat                         full
% 27.84/3.92  --bmc1_ground_init                      false
% 27.84/3.92  --bmc1_pre_inst_next_state              false
% 27.84/3.92  --bmc1_pre_inst_state                   false
% 27.84/3.92  --bmc1_pre_inst_reach_state             false
% 27.84/3.92  --bmc1_out_unsat_core                   false
% 27.84/3.92  --bmc1_aig_witness_out                  false
% 27.84/3.92  --bmc1_verbose                          false
% 27.84/3.92  --bmc1_dump_clauses_tptp                false
% 27.84/3.92  --bmc1_dump_unsat_core_tptp             false
% 27.84/3.92  --bmc1_dump_file                        -
% 27.84/3.92  --bmc1_ucm_expand_uc_limit              128
% 27.84/3.92  --bmc1_ucm_n_expand_iterations          6
% 27.84/3.92  --bmc1_ucm_extend_mode                  1
% 27.84/3.92  --bmc1_ucm_init_mode                    2
% 27.84/3.92  --bmc1_ucm_cone_mode                    none
% 27.84/3.92  --bmc1_ucm_reduced_relation_type        0
% 27.84/3.92  --bmc1_ucm_relax_model                  4
% 27.84/3.92  --bmc1_ucm_full_tr_after_sat            true
% 27.84/3.92  --bmc1_ucm_expand_neg_assumptions       false
% 27.84/3.92  --bmc1_ucm_layered_model                none
% 27.84/3.92  --bmc1_ucm_max_lemma_size               10
% 27.84/3.92  
% 27.84/3.92  ------ AIG Options
% 27.84/3.92  
% 27.84/3.92  --aig_mode                              false
% 27.84/3.92  
% 27.84/3.92  ------ Instantiation Options
% 27.84/3.92  
% 27.84/3.92  --instantiation_flag                    true
% 27.84/3.92  --inst_sos_flag                         true
% 27.84/3.92  --inst_sos_phase                        true
% 27.84/3.92  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 27.84/3.92  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 27.84/3.92  --inst_lit_sel_side                     none
% 27.84/3.92  --inst_solver_per_active                1400
% 27.84/3.92  --inst_solver_calls_frac                1.
% 27.84/3.92  --inst_passive_queue_type               priority_queues
% 27.84/3.92  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 27.84/3.92  --inst_passive_queues_freq              [25;2]
% 27.84/3.92  --inst_dismatching                      true
% 27.84/3.92  --inst_eager_unprocessed_to_passive     true
% 27.84/3.92  --inst_prop_sim_given                   true
% 27.84/3.92  --inst_prop_sim_new                     false
% 27.84/3.92  --inst_subs_new                         false
% 27.84/3.92  --inst_eq_res_simp                      false
% 27.84/3.92  --inst_subs_given                       false
% 27.84/3.92  --inst_orphan_elimination               true
% 27.84/3.92  --inst_learning_loop_flag               true
% 27.84/3.92  --inst_learning_start                   3000
% 27.84/3.92  --inst_learning_factor                  2
% 27.84/3.92  --inst_start_prop_sim_after_learn       3
% 27.84/3.92  --inst_sel_renew                        solver
% 27.84/3.92  --inst_lit_activity_flag                true
% 27.84/3.92  --inst_restr_to_given                   false
% 27.84/3.92  --inst_activity_threshold               500
% 27.84/3.92  --inst_out_proof                        true
% 27.84/3.92  
% 27.84/3.92  ------ Resolution Options
% 27.84/3.92  
% 27.84/3.92  --resolution_flag                       false
% 27.84/3.92  --res_lit_sel                           adaptive
% 27.84/3.92  --res_lit_sel_side                      none
% 27.84/3.92  --res_ordering                          kbo
% 27.84/3.92  --res_to_prop_solver                    active
% 27.84/3.92  --res_prop_simpl_new                    false
% 27.84/3.92  --res_prop_simpl_given                  true
% 27.84/3.92  --res_passive_queue_type                priority_queues
% 27.84/3.92  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 27.84/3.92  --res_passive_queues_freq               [15;5]
% 27.84/3.92  --res_forward_subs                      full
% 27.84/3.92  --res_backward_subs                     full
% 27.84/3.92  --res_forward_subs_resolution           true
% 27.84/3.92  --res_backward_subs_resolution          true
% 27.84/3.92  --res_orphan_elimination                true
% 27.84/3.92  --res_time_limit                        2.
% 27.84/3.92  --res_out_proof                         true
% 27.84/3.92  
% 27.84/3.92  ------ Superposition Options
% 27.84/3.92  
% 27.84/3.92  --superposition_flag                    true
% 27.84/3.92  --sup_passive_queue_type                priority_queues
% 27.84/3.92  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 27.84/3.92  --sup_passive_queues_freq               [8;1;4]
% 27.84/3.92  --demod_completeness_check              fast
% 27.84/3.92  --demod_use_ground                      true
% 27.84/3.92  --sup_to_prop_solver                    passive
% 27.84/3.92  --sup_prop_simpl_new                    true
% 27.84/3.92  --sup_prop_simpl_given                  true
% 27.84/3.92  --sup_fun_splitting                     true
% 27.84/3.92  --sup_smt_interval                      50000
% 27.84/3.92  
% 27.84/3.92  ------ Superposition Simplification Setup
% 27.84/3.92  
% 27.84/3.92  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 27.84/3.92  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 27.84/3.92  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 27.84/3.92  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 27.84/3.92  --sup_full_triv                         [TrivRules;PropSubs]
% 27.84/3.92  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 27.84/3.92  --sup_full_bw                           [BwDemod;BwSubsumption]
% 27.84/3.92  --sup_immed_triv                        [TrivRules]
% 27.84/3.92  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 27.84/3.92  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 27.84/3.92  --sup_immed_bw_main                     []
% 27.84/3.92  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 27.84/3.92  --sup_input_triv                        [Unflattening;TrivRules]
% 27.84/3.92  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 27.84/3.92  --sup_input_bw                          []
% 27.84/3.92  
% 27.84/3.92  ------ Combination Options
% 27.84/3.92  
% 27.84/3.92  --comb_res_mult                         3
% 27.84/3.92  --comb_sup_mult                         2
% 27.84/3.92  --comb_inst_mult                        10
% 27.84/3.92  
% 27.84/3.92  ------ Debug Options
% 27.84/3.92  
% 27.84/3.92  --dbg_backtrace                         false
% 27.84/3.92  --dbg_dump_prop_clauses                 false
% 27.84/3.92  --dbg_dump_prop_clauses_file            -
% 27.84/3.92  --dbg_out_stat                          false
% 27.84/3.92  
% 27.84/3.92  
% 27.84/3.92  
% 27.84/3.92  
% 27.84/3.92  ------ Proving...
% 27.84/3.92  
% 27.84/3.92  
% 27.84/3.92  % SZS status Theorem for theBenchmark.p
% 27.84/3.92  
% 27.84/3.92  % SZS output start CNFRefutation for theBenchmark.p
% 27.84/3.92  
% 27.84/3.92  fof(f9,axiom,(
% 27.84/3.92    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 27.84/3.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.84/3.92  
% 27.84/3.92  fof(f18,plain,(
% 27.84/3.92    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 27.84/3.92    inference(ennf_transformation,[],[f9])).
% 27.84/3.92  
% 27.84/3.92  fof(f37,plain,(
% 27.84/3.92    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 27.84/3.92    inference(cnf_transformation,[],[f18])).
% 27.84/3.92  
% 27.84/3.92  fof(f13,conjecture,(
% 27.84/3.92    ! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 27.84/3.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.84/3.92  
% 27.84/3.92  fof(f14,negated_conjecture,(
% 27.84/3.92    ~! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 27.84/3.92    inference(negated_conjecture,[],[f13])).
% 27.84/3.92  
% 27.84/3.92  fof(f22,plain,(
% 27.84/3.92    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) & v1_relat_1(X2))),
% 27.84/3.92    inference(ennf_transformation,[],[f14])).
% 27.84/3.92  
% 27.84/3.92  fof(f25,plain,(
% 27.84/3.92    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) & v1_relat_1(X2)) => (~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) & v1_relat_1(sK2))),
% 27.84/3.92    introduced(choice_axiom,[])).
% 27.84/3.92  
% 27.84/3.92  fof(f26,plain,(
% 27.84/3.92    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) & v1_relat_1(sK2)),
% 27.84/3.92    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f25])).
% 27.84/3.92  
% 27.84/3.92  fof(f41,plain,(
% 27.84/3.92    v1_relat_1(sK2)),
% 27.84/3.92    inference(cnf_transformation,[],[f26])).
% 27.84/3.92  
% 27.84/3.92  fof(f11,axiom,(
% 27.84/3.92    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 27.84/3.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.84/3.92  
% 27.84/3.92  fof(f20,plain,(
% 27.84/3.92    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 27.84/3.92    inference(ennf_transformation,[],[f11])).
% 27.84/3.92  
% 27.84/3.92  fof(f39,plain,(
% 27.84/3.92    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 27.84/3.92    inference(cnf_transformation,[],[f20])).
% 27.84/3.92  
% 27.84/3.92  fof(f12,axiom,(
% 27.84/3.92    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)))),
% 27.84/3.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.84/3.92  
% 27.84/3.92  fof(f21,plain,(
% 27.84/3.92    ! [X0,X1] : (r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 27.84/3.92    inference(ennf_transformation,[],[f12])).
% 27.84/3.92  
% 27.84/3.92  fof(f40,plain,(
% 27.84/3.92    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 27.84/3.92    inference(cnf_transformation,[],[f21])).
% 27.84/3.92  
% 27.84/3.92  fof(f1,axiom,(
% 27.84/3.92    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 27.84/3.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.84/3.92  
% 27.84/3.92  fof(f27,plain,(
% 27.84/3.92    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 27.84/3.92    inference(cnf_transformation,[],[f1])).
% 27.84/3.92  
% 27.84/3.92  fof(f5,axiom,(
% 27.84/3.92    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 27.84/3.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.84/3.92  
% 27.84/3.92  fof(f33,plain,(
% 27.84/3.92    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 27.84/3.92    inference(cnf_transformation,[],[f5])).
% 27.84/3.92  
% 27.84/3.92  fof(f44,plain,(
% 27.84/3.92    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 27.84/3.92    inference(definition_unfolding,[],[f27,f33,f33])).
% 27.84/3.92  
% 27.84/3.92  fof(f10,axiom,(
% 27.84/3.92    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1))),
% 27.84/3.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.84/3.92  
% 27.84/3.92  fof(f19,plain,(
% 27.84/3.92    ! [X0,X1,X2] : (k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2))),
% 27.84/3.92    inference(ennf_transformation,[],[f10])).
% 27.84/3.92  
% 27.84/3.92  fof(f38,plain,(
% 27.84/3.92    ( ! [X2,X0,X1] : (k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 27.84/3.92    inference(cnf_transformation,[],[f19])).
% 27.84/3.92  
% 27.84/3.92  fof(f47,plain,(
% 27.84/3.92    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) | ~v1_relat_1(X2)) )),
% 27.84/3.92    inference(definition_unfolding,[],[f38,f33])).
% 27.84/3.92  
% 27.84/3.92  fof(f4,axiom,(
% 27.84/3.92    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 27.84/3.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.84/3.92  
% 27.84/3.92  fof(f16,plain,(
% 27.84/3.92    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 27.84/3.92    inference(ennf_transformation,[],[f4])).
% 27.84/3.92  
% 27.84/3.92  fof(f17,plain,(
% 27.84/3.92    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 27.84/3.92    inference(flattening,[],[f16])).
% 27.84/3.92  
% 27.84/3.92  fof(f32,plain,(
% 27.84/3.92    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 27.84/3.92    inference(cnf_transformation,[],[f17])).
% 27.84/3.92  
% 27.84/3.92  fof(f45,plain,(
% 27.84/3.92    ( ! [X2,X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 27.84/3.92    inference(definition_unfolding,[],[f32,f33])).
% 27.84/3.92  
% 27.84/3.92  fof(f42,plain,(
% 27.84/3.92    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))),
% 27.84/3.92    inference(cnf_transformation,[],[f26])).
% 27.84/3.92  
% 27.84/3.92  fof(f48,plain,(
% 27.84/3.92    ~r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k9_relat_1(sK2,sK0),k4_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))))),
% 27.84/3.92    inference(definition_unfolding,[],[f42,f33,f33])).
% 27.84/3.92  
% 27.84/3.92  cnf(c_7,plain,
% 27.84/3.92      ( ~ v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1)) ),
% 27.84/3.92      inference(cnf_transformation,[],[f37]) ).
% 27.84/3.92  
% 27.84/3.92  cnf(c_395,plain,
% 27.84/3.92      ( v1_relat_1(X0) != iProver_top
% 27.84/3.92      | v1_relat_1(k7_relat_1(X0,X1)) = iProver_top ),
% 27.84/3.92      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 27.84/3.92  
% 27.84/3.92  cnf(c_12,negated_conjecture,
% 27.84/3.92      ( v1_relat_1(sK2) ),
% 27.84/3.92      inference(cnf_transformation,[],[f41]) ).
% 27.84/3.92  
% 27.84/3.92  cnf(c_390,plain,
% 27.84/3.92      ( v1_relat_1(sK2) = iProver_top ),
% 27.84/3.92      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 27.84/3.92  
% 27.84/3.92  cnf(c_9,plain,
% 27.84/3.92      ( ~ v1_relat_1(X0)
% 27.84/3.92      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 27.84/3.92      inference(cnf_transformation,[],[f39]) ).
% 27.84/3.92  
% 27.84/3.92  cnf(c_393,plain,
% 27.84/3.92      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 27.84/3.92      | v1_relat_1(X0) != iProver_top ),
% 27.84/3.92      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 27.84/3.92  
% 27.84/3.92  cnf(c_758,plain,
% 27.84/3.92      ( k2_relat_1(k7_relat_1(k7_relat_1(X0,X1),X2)) = k9_relat_1(k7_relat_1(X0,X1),X2)
% 27.84/3.92      | v1_relat_1(X0) != iProver_top ),
% 27.84/3.92      inference(superposition,[status(thm)],[c_395,c_393]) ).
% 27.84/3.92  
% 27.84/3.92  cnf(c_2278,plain,
% 27.84/3.92      ( k2_relat_1(k7_relat_1(k7_relat_1(sK2,X0),X1)) = k9_relat_1(k7_relat_1(sK2,X0),X1) ),
% 27.84/3.92      inference(superposition,[status(thm)],[c_390,c_758]) ).
% 27.84/3.92  
% 27.84/3.92  cnf(c_759,plain,
% 27.84/3.92      ( k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0) ),
% 27.84/3.92      inference(superposition,[status(thm)],[c_390,c_393]) ).
% 27.84/3.92  
% 27.84/3.92  cnf(c_10,plain,
% 27.84/3.92      ( r1_tarski(k2_relat_1(k7_relat_1(X0,X1)),k2_relat_1(X0))
% 27.84/3.92      | ~ v1_relat_1(X0) ),
% 27.84/3.92      inference(cnf_transformation,[],[f40]) ).
% 27.84/3.92  
% 27.84/3.92  cnf(c_392,plain,
% 27.84/3.92      ( r1_tarski(k2_relat_1(k7_relat_1(X0,X1)),k2_relat_1(X0)) = iProver_top
% 27.84/3.92      | v1_relat_1(X0) != iProver_top ),
% 27.84/3.92      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 27.84/3.92  
% 27.84/3.92  cnf(c_856,plain,
% 27.84/3.92      ( r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(sK2,X0),X1)),k9_relat_1(sK2,X0)) = iProver_top
% 27.84/3.92      | v1_relat_1(k7_relat_1(sK2,X0)) != iProver_top ),
% 27.84/3.92      inference(superposition,[status(thm)],[c_759,c_392]) ).
% 27.84/3.92  
% 27.84/3.92  cnf(c_2652,plain,
% 27.84/3.92      ( r1_tarski(k9_relat_1(k7_relat_1(sK2,X0),X1),k9_relat_1(sK2,X0)) = iProver_top
% 27.84/3.92      | v1_relat_1(k7_relat_1(sK2,X0)) != iProver_top ),
% 27.84/3.92      inference(demodulation,[status(thm)],[c_2278,c_856]) ).
% 27.84/3.92  
% 27.84/3.92  cnf(c_0,plain,
% 27.84/3.92      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 27.84/3.92      inference(cnf_transformation,[],[f44]) ).
% 27.84/3.92  
% 27.84/3.92  cnf(c_8,plain,
% 27.84/3.92      ( ~ v1_relat_1(X0)
% 27.84/3.92      | k7_relat_1(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k7_relat_1(k7_relat_1(X0,X1),X2) ),
% 27.84/3.92      inference(cnf_transformation,[],[f47]) ).
% 27.84/3.92  
% 27.84/3.92  cnf(c_394,plain,
% 27.84/3.92      ( k7_relat_1(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k7_relat_1(k7_relat_1(X0,X1),X2)
% 27.84/3.92      | v1_relat_1(X0) != iProver_top ),
% 27.84/3.92      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 27.84/3.92  
% 27.84/3.92  cnf(c_1022,plain,
% 27.84/3.92      ( k7_relat_1(sK2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k7_relat_1(k7_relat_1(sK2,X0),X1) ),
% 27.84/3.92      inference(superposition,[status(thm)],[c_390,c_394]) ).
% 27.84/3.92  
% 27.84/3.92  cnf(c_1027,plain,
% 27.84/3.92      ( k7_relat_1(sK2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k7_relat_1(k7_relat_1(sK2,X1),X0) ),
% 27.84/3.92      inference(superposition,[status(thm)],[c_0,c_1022]) ).
% 27.84/3.92  
% 27.84/3.92  cnf(c_1137,plain,
% 27.84/3.92      ( k7_relat_1(k7_relat_1(sK2,X0),X1) = k7_relat_1(k7_relat_1(sK2,X1),X0) ),
% 27.84/3.92      inference(superposition,[status(thm)],[c_1027,c_1022]) ).
% 27.84/3.92  
% 27.84/3.92  cnf(c_1147,plain,
% 27.84/3.92      ( r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(sK2,X0),X1)),k2_relat_1(k7_relat_1(sK2,X1))) = iProver_top
% 27.84/3.92      | v1_relat_1(k7_relat_1(sK2,X1)) != iProver_top ),
% 27.84/3.92      inference(superposition,[status(thm)],[c_1137,c_392]) ).
% 27.84/3.92  
% 27.84/3.92  cnf(c_1149,plain,
% 27.84/3.92      ( r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(sK2,X0),X1)),k9_relat_1(sK2,X1)) = iProver_top
% 27.84/3.92      | v1_relat_1(k7_relat_1(sK2,X1)) != iProver_top ),
% 27.84/3.92      inference(demodulation,[status(thm)],[c_1147,c_759]) ).
% 27.84/3.92  
% 27.84/3.92  cnf(c_2651,plain,
% 27.84/3.92      ( r1_tarski(k9_relat_1(k7_relat_1(sK2,X0),X1),k9_relat_1(sK2,X1)) = iProver_top
% 27.84/3.92      | v1_relat_1(k7_relat_1(sK2,X1)) != iProver_top ),
% 27.84/3.92      inference(demodulation,[status(thm)],[c_2278,c_1149]) ).
% 27.84/3.92  
% 27.84/3.92  cnf(c_5,plain,
% 27.84/3.92      ( ~ r1_tarski(X0,X1)
% 27.84/3.92      | ~ r1_tarski(X0,X2)
% 27.84/3.92      | r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
% 27.84/3.92      inference(cnf_transformation,[],[f45]) ).
% 27.84/3.92  
% 27.84/3.92  cnf(c_396,plain,
% 27.84/3.92      ( r1_tarski(X0,X1) != iProver_top
% 27.84/3.92      | r1_tarski(X0,X2) != iProver_top
% 27.84/3.92      | r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = iProver_top ),
% 27.84/3.92      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 27.84/3.92  
% 27.84/3.92  cnf(c_1033,plain,
% 27.84/3.92      ( k9_relat_1(sK2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k2_relat_1(k7_relat_1(k7_relat_1(sK2,X0),X1)) ),
% 27.84/3.92      inference(superposition,[status(thm)],[c_1022,c_759]) ).
% 27.84/3.92  
% 27.84/3.92  cnf(c_11,negated_conjecture,
% 27.84/3.92      ( ~ r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k9_relat_1(sK2,sK0),k4_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))) ),
% 27.84/3.92      inference(cnf_transformation,[],[f48]) ).
% 27.84/3.92  
% 27.84/3.92  cnf(c_391,plain,
% 27.84/3.92      ( r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k9_relat_1(sK2,sK0),k4_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))) != iProver_top ),
% 27.84/3.92      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 27.84/3.92  
% 27.84/3.92  cnf(c_1382,plain,
% 27.84/3.92      ( r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(sK2,sK0),sK1)),k4_xboole_0(k9_relat_1(sK2,sK0),k4_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))) != iProver_top ),
% 27.84/3.92      inference(demodulation,[status(thm)],[c_1033,c_391]) ).
% 27.84/3.92  
% 27.84/3.92  cnf(c_1469,plain,
% 27.84/3.92      ( r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(sK2,sK0),sK1)),k9_relat_1(sK2,sK1)) != iProver_top
% 27.84/3.92      | r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(sK2,sK0),sK1)),k9_relat_1(sK2,sK0)) != iProver_top ),
% 27.84/3.92      inference(superposition,[status(thm)],[c_396,c_1382]) ).
% 27.84/3.92  
% 27.84/3.92  cnf(c_2655,plain,
% 27.84/3.92      ( r1_tarski(k9_relat_1(k7_relat_1(sK2,sK0),sK1),k9_relat_1(sK2,sK1)) != iProver_top
% 27.84/3.92      | r1_tarski(k9_relat_1(k7_relat_1(sK2,sK0),sK1),k9_relat_1(sK2,sK0)) != iProver_top ),
% 27.84/3.92      inference(demodulation,[status(thm)],[c_2278,c_1469]) ).
% 27.84/3.92  
% 27.84/3.92  cnf(c_3508,plain,
% 27.84/3.92      ( r1_tarski(k9_relat_1(k7_relat_1(sK2,sK0),sK1),k9_relat_1(sK2,sK0)) != iProver_top
% 27.84/3.92      | v1_relat_1(k7_relat_1(sK2,sK1)) != iProver_top ),
% 27.84/3.92      inference(superposition,[status(thm)],[c_2651,c_2655]) ).
% 27.84/3.92  
% 27.84/3.92  cnf(c_13,plain,
% 27.84/3.92      ( v1_relat_1(sK2) = iProver_top ),
% 27.84/3.92      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 27.84/3.92  
% 27.84/3.92  cnf(c_7461,plain,
% 27.84/3.92      ( v1_relat_1(k7_relat_1(sK2,sK1)) | ~ v1_relat_1(sK2) ),
% 27.84/3.92      inference(instantiation,[status(thm)],[c_7]) ).
% 27.84/3.92  
% 27.84/3.92  cnf(c_7462,plain,
% 27.84/3.92      ( v1_relat_1(k7_relat_1(sK2,sK1)) = iProver_top
% 27.84/3.92      | v1_relat_1(sK2) != iProver_top ),
% 27.84/3.92      inference(predicate_to_equality,[status(thm)],[c_7461]) ).
% 27.84/3.92  
% 27.84/3.92  cnf(c_60682,plain,
% 27.84/3.92      ( r1_tarski(k9_relat_1(k7_relat_1(sK2,sK0),sK1),k9_relat_1(sK2,sK0)) != iProver_top ),
% 27.84/3.92      inference(global_propositional_subsumption,
% 27.84/3.92                [status(thm)],
% 27.84/3.92                [c_3508,c_13,c_7462]) ).
% 27.84/3.92  
% 27.84/3.92  cnf(c_60686,plain,
% 27.84/3.92      ( v1_relat_1(k7_relat_1(sK2,sK0)) != iProver_top ),
% 27.84/3.92      inference(superposition,[status(thm)],[c_2652,c_60682]) ).
% 27.84/3.92  
% 27.84/3.92  cnf(c_60689,plain,
% 27.84/3.92      ( v1_relat_1(sK2) != iProver_top ),
% 27.84/3.92      inference(superposition,[status(thm)],[c_395,c_60686]) ).
% 27.84/3.92  
% 27.84/3.92  cnf(contradiction,plain,
% 27.84/3.92      ( $false ),
% 27.84/3.92      inference(minisat,[status(thm)],[c_60689,c_13]) ).
% 27.84/3.92  
% 27.84/3.92  
% 27.84/3.92  % SZS output end CNFRefutation for theBenchmark.p
% 27.84/3.92  
% 27.84/3.92  ------                               Statistics
% 27.84/3.92  
% 27.84/3.92  ------ General
% 27.84/3.92  
% 27.84/3.92  abstr_ref_over_cycles:                  0
% 27.84/3.92  abstr_ref_under_cycles:                 0
% 27.84/3.92  gc_basic_clause_elim:                   0
% 27.84/3.92  forced_gc_time:                         0
% 27.84/3.92  parsing_time:                           0.008
% 27.84/3.92  unif_index_cands_time:                  0.
% 27.84/3.92  unif_index_add_time:                    0.
% 27.84/3.92  orderings_time:                         0.
% 27.84/3.92  out_proof_time:                         0.011
% 27.84/3.92  total_time:                             3.351
% 27.84/3.92  num_of_symbols:                         42
% 27.84/3.92  num_of_terms:                           176306
% 27.84/3.92  
% 27.84/3.92  ------ Preprocessing
% 27.84/3.92  
% 27.84/3.92  num_of_splits:                          0
% 27.84/3.92  num_of_split_atoms:                     0
% 27.84/3.92  num_of_reused_defs:                     0
% 27.84/3.92  num_eq_ax_congr_red:                    12
% 27.84/3.92  num_of_sem_filtered_clauses:            1
% 27.84/3.92  num_of_subtypes:                        0
% 27.84/3.92  monotx_restored_types:                  0
% 27.84/3.92  sat_num_of_epr_types:                   0
% 27.84/3.92  sat_num_of_non_cyclic_types:            0
% 27.84/3.92  sat_guarded_non_collapsed_types:        0
% 27.84/3.92  num_pure_diseq_elim:                    0
% 27.84/3.92  simp_replaced_by:                       0
% 27.84/3.92  res_preprocessed:                       67
% 27.84/3.92  prep_upred:                             0
% 27.84/3.92  prep_unflattend:                        0
% 27.84/3.92  smt_new_axioms:                         0
% 27.84/3.92  pred_elim_cands:                        2
% 27.84/3.92  pred_elim:                              0
% 27.84/3.92  pred_elim_cl:                           0
% 27.84/3.92  pred_elim_cycles:                       2
% 27.84/3.92  merged_defs:                            0
% 27.84/3.92  merged_defs_ncl:                        0
% 27.84/3.92  bin_hyper_res:                          0
% 27.84/3.92  prep_cycles:                            4
% 27.84/3.92  pred_elim_time:                         0.
% 27.84/3.92  splitting_time:                         0.
% 27.84/3.92  sem_filter_time:                        0.
% 27.84/3.92  monotx_time:                            0.
% 27.84/3.92  subtype_inf_time:                       0.
% 27.84/3.92  
% 27.84/3.92  ------ Problem properties
% 27.84/3.92  
% 27.84/3.92  clauses:                                12
% 27.84/3.92  conjectures:                            2
% 27.84/3.92  epr:                                    3
% 27.84/3.92  horn:                                   12
% 27.84/3.92  ground:                                 2
% 27.84/3.92  unary:                                  5
% 27.84/3.92  binary:                                 5
% 27.84/3.92  lits:                                   21
% 27.84/3.92  lits_eq:                                5
% 27.84/3.92  fd_pure:                                0
% 27.84/3.92  fd_pseudo:                              0
% 27.84/3.92  fd_cond:                                0
% 27.84/3.92  fd_pseudo_cond:                         1
% 27.84/3.92  ac_symbols:                             0
% 27.84/3.92  
% 27.84/3.92  ------ Propositional Solver
% 27.84/3.92  
% 27.84/3.92  prop_solver_calls:                      36
% 27.84/3.92  prop_fast_solver_calls:                 686
% 27.84/3.92  smt_solver_calls:                       0
% 27.84/3.92  smt_fast_solver_calls:                  0
% 27.84/3.92  prop_num_of_clauses:                    18809
% 27.84/3.92  prop_preprocess_simplified:             28958
% 27.84/3.92  prop_fo_subsumed:                       6
% 27.84/3.92  prop_solver_time:                       0.
% 27.84/3.92  smt_solver_time:                        0.
% 27.84/3.92  smt_fast_solver_time:                   0.
% 27.84/3.92  prop_fast_solver_time:                  0.
% 27.84/3.92  prop_unsat_core_time:                   0.002
% 27.84/3.92  
% 27.84/3.92  ------ QBF
% 27.84/3.92  
% 27.84/3.92  qbf_q_res:                              0
% 27.84/3.92  qbf_num_tautologies:                    0
% 27.84/3.92  qbf_prep_cycles:                        0
% 27.84/3.92  
% 27.84/3.92  ------ BMC1
% 27.84/3.92  
% 27.84/3.92  bmc1_current_bound:                     -1
% 27.84/3.92  bmc1_last_solved_bound:                 -1
% 27.84/3.92  bmc1_unsat_core_size:                   -1
% 27.84/3.92  bmc1_unsat_core_parents_size:           -1
% 27.84/3.92  bmc1_merge_next_fun:                    0
% 27.84/3.92  bmc1_unsat_core_clauses_time:           0.
% 27.84/3.92  
% 27.84/3.92  ------ Instantiation
% 27.84/3.92  
% 27.84/3.92  inst_num_of_clauses:                    3659
% 27.84/3.92  inst_num_in_passive:                    1977
% 27.84/3.92  inst_num_in_active:                     1297
% 27.84/3.92  inst_num_in_unprocessed:                389
% 27.84/3.92  inst_num_of_loops:                      1380
% 27.84/3.92  inst_num_of_learning_restarts:          0
% 27.84/3.92  inst_num_moves_active_passive:          79
% 27.84/3.92  inst_lit_activity:                      0
% 27.84/3.92  inst_lit_activity_moves:                1
% 27.84/3.92  inst_num_tautologies:                   0
% 27.84/3.92  inst_num_prop_implied:                  0
% 27.84/3.92  inst_num_existing_simplified:           0
% 27.84/3.92  inst_num_eq_res_simplified:             0
% 27.84/3.92  inst_num_child_elim:                    0
% 27.84/3.92  inst_num_of_dismatching_blockings:      3457
% 27.84/3.92  inst_num_of_non_proper_insts:           5215
% 27.84/3.92  inst_num_of_duplicates:                 0
% 27.84/3.92  inst_inst_num_from_inst_to_res:         0
% 27.84/3.92  inst_dismatching_checking_time:         0.
% 27.84/3.92  
% 27.84/3.92  ------ Resolution
% 27.84/3.92  
% 27.84/3.92  res_num_of_clauses:                     0
% 27.84/3.92  res_num_in_passive:                     0
% 27.84/3.92  res_num_in_active:                      0
% 27.84/3.92  res_num_of_loops:                       71
% 27.84/3.92  res_forward_subset_subsumed:            925
% 27.84/3.92  res_backward_subset_subsumed:           8
% 27.84/3.92  res_forward_subsumed:                   0
% 27.84/3.92  res_backward_subsumed:                  0
% 27.84/3.92  res_forward_subsumption_resolution:     0
% 27.84/3.92  res_backward_subsumption_resolution:    0
% 27.84/3.92  res_clause_to_clause_subsumption:       46692
% 27.84/3.92  res_orphan_elimination:                 0
% 27.84/3.92  res_tautology_del:                      396
% 27.84/3.92  res_num_eq_res_simplified:              0
% 27.84/3.92  res_num_sel_changes:                    0
% 27.84/3.92  res_moves_from_active_to_pass:          0
% 27.84/3.92  
% 27.84/3.92  ------ Superposition
% 27.84/3.92  
% 27.84/3.92  sup_time_total:                         0.
% 27.84/3.92  sup_time_generating:                    0.
% 27.84/3.92  sup_time_sim_full:                      0.
% 27.84/3.92  sup_time_sim_immed:                     0.
% 27.84/3.92  
% 27.84/3.92  sup_num_of_clauses:                     6069
% 27.84/3.92  sup_num_in_active:                      237
% 27.84/3.92  sup_num_in_passive:                     5832
% 27.84/3.92  sup_num_of_loops:                       275
% 27.84/3.92  sup_fw_superposition:                   14747
% 27.84/3.92  sup_bw_superposition:                   8366
% 27.84/3.92  sup_immediate_simplified:               7740
% 27.84/3.92  sup_given_eliminated:                   11
% 27.84/3.92  comparisons_done:                       0
% 27.84/3.92  comparisons_avoided:                    0
% 27.84/3.92  
% 27.84/3.92  ------ Simplifications
% 27.84/3.92  
% 27.84/3.92  
% 27.84/3.92  sim_fw_subset_subsumed:                 39
% 27.84/3.92  sim_bw_subset_subsumed:                 45
% 27.84/3.92  sim_fw_subsumed:                        182
% 27.84/3.92  sim_bw_subsumed:                        563
% 27.84/3.92  sim_fw_subsumption_res:                 0
% 27.84/3.92  sim_bw_subsumption_res:                 0
% 27.84/3.92  sim_tautology_del:                      0
% 27.84/3.92  sim_eq_tautology_del:                   352
% 27.84/3.92  sim_eq_res_simp:                        0
% 27.84/3.92  sim_fw_demodulated:                     5835
% 27.84/3.92  sim_bw_demodulated:                     155
% 27.84/3.92  sim_light_normalised:                   3995
% 27.84/3.92  sim_joinable_taut:                      0
% 27.84/3.92  sim_joinable_simp:                      0
% 27.84/3.92  sim_ac_normalised:                      0
% 27.84/3.92  sim_smt_subsumption:                    0
% 27.84/3.92  
%------------------------------------------------------------------------------
