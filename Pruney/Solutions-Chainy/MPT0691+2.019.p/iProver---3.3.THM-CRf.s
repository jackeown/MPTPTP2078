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
% DateTime   : Thu Dec  3 11:51:42 EST 2020

% Result     : Theorem 6.92s
% Output     : CNFRefutation 6.92s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 271 expanded)
%              Number of clauses        :   41 (  93 expanded)
%              Number of leaves         :   11 (  53 expanded)
%              Depth                    :   13
%              Number of atoms          :  149 ( 643 expanded)
%              Number of equality atoms :   68 ( 145 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r1_tarski(X0,k1_relat_1(X1))
         => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f20,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f22,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
        & r1_tarski(X0,k1_relat_1(X1))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
      & r1_tarski(sK0,k1_relat_1(sK1))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
    & r1_tarski(sK0,k1_relat_1(sK1))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f22])).

fof(f33,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f27,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f29,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k1_setfam_1(k2_tarski(X0,k10_relat_1(X2,X1))) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f32,f26])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k1_setfam_1(k2_tarski(X1,X2))) ) ),
    inference(definition_unfolding,[],[f24,f26])).

fof(f35,plain,(
    ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f23])).

fof(f34,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1)))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1)))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_10,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_321,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_329,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k7_relat_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_327,plain,
    ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_465,plain,
    ( k10_relat_1(k7_relat_1(X0,X1),k2_relat_1(k7_relat_1(X0,X1))) = k1_relat_1(k7_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_329,c_327])).

cnf(c_1495,plain,
    ( k10_relat_1(k7_relat_1(sK1,X0),k2_relat_1(k7_relat_1(sK1,X0))) = k1_relat_1(k7_relat_1(sK1,X0)) ),
    inference(superposition,[status(thm)],[c_321,c_465])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_328,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_541,plain,
    ( k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0) ),
    inference(superposition,[status(thm)],[c_321,c_328])).

cnf(c_1497,plain,
    ( k10_relat_1(k7_relat_1(sK1,X0),k9_relat_1(sK1,X0)) = k1_relat_1(k7_relat_1(sK1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_1495,c_541])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | k1_setfam_1(k2_tarski(X1,k10_relat_1(X0,X2))) = k10_relat_1(k7_relat_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_324,plain,
    ( k1_setfam_1(k2_tarski(X0,k10_relat_1(X1,X2))) = k10_relat_1(k7_relat_1(X1,X0),X2)
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_638,plain,
    ( k1_setfam_1(k2_tarski(X0,k10_relat_1(sK1,X1))) = k10_relat_1(k7_relat_1(sK1,X0),X1) ),
    inference(superposition,[status(thm)],[c_321,c_324])).

cnf(c_1,plain,
    ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_0,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(X0,k1_setfam_1(k2_tarski(X1,X2))) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_330,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(X0,k1_setfam_1(k2_tarski(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_652,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(X0,k1_setfam_1(k2_tarski(X2,X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_330])).

cnf(c_1094,plain,
    ( r1_tarski(X0,k10_relat_1(k7_relat_1(sK1,X1),X2)) != iProver_top
    | r1_tarski(X0,k10_relat_1(sK1,X2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_638,c_652])).

cnf(c_2140,plain,
    ( r1_tarski(X0,k10_relat_1(sK1,k9_relat_1(sK1,X1))) = iProver_top
    | r1_tarski(X0,k1_relat_1(k7_relat_1(sK1,X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1497,c_1094])).

cnf(c_8,negated_conjecture,
    ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_323,plain,
    ( r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_24064,plain,
    ( r1_tarski(sK0,k1_relat_1(k7_relat_1(sK1,sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2140,c_323])).

cnf(c_9,negated_conjecture,
    ( r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_322,plain,
    ( r1_tarski(sK0,k1_relat_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_325,plain,
    ( k1_relat_1(k7_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_912,plain,
    ( k1_relat_1(k7_relat_1(sK1,sK0)) = sK0
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_322,c_325])).

cnf(c_395,plain,
    ( ~ r1_tarski(sK0,k1_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | k1_relat_1(k7_relat_1(sK1,sK0)) = sK0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1116,plain,
    ( k1_relat_1(k7_relat_1(sK1,sK0)) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_912,c_10,c_9,c_395])).

cnf(c_24071,plain,
    ( r1_tarski(sK0,sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_24064,c_1116])).

cnf(c_5,plain,
    ( r1_tarski(k10_relat_1(X0,X1),k10_relat_1(X0,k2_relat_1(X0)))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_326,plain,
    ( r1_tarski(k10_relat_1(X0,X1),k10_relat_1(X0,k2_relat_1(X0))) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1913,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),k10_relat_1(k7_relat_1(sK1,X0),k2_relat_1(k7_relat_1(sK1,X0)))) = iProver_top
    | v1_relat_1(k7_relat_1(sK1,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1497,c_326])).

cnf(c_1921,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),k1_relat_1(k7_relat_1(sK1,X0))) = iProver_top
    | v1_relat_1(k7_relat_1(sK1,X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1913,c_541,c_1497])).

cnf(c_2178,plain,
    ( r1_tarski(sK0,sK0) = iProver_top
    | v1_relat_1(k7_relat_1(sK1,sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1116,c_1921])).

cnf(c_1572,plain,
    ( v1_relat_1(k7_relat_1(sK1,sK0))
    | ~ v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1573,plain,
    ( v1_relat_1(k7_relat_1(sK1,sK0)) = iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1572])).

cnf(c_11,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_24071,c_2178,c_1573,c_11])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:47:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 6.92/1.50  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.92/1.50  
% 6.92/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 6.92/1.50  
% 6.92/1.50  ------  iProver source info
% 6.92/1.50  
% 6.92/1.50  git: date: 2020-06-30 10:37:57 +0100
% 6.92/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 6.92/1.50  git: non_committed_changes: false
% 6.92/1.50  git: last_make_outside_of_git: false
% 6.92/1.50  
% 6.92/1.50  ------ 
% 6.92/1.50  
% 6.92/1.50  ------ Input Options
% 6.92/1.50  
% 6.92/1.50  --out_options                           all
% 6.92/1.50  --tptp_safe_out                         true
% 6.92/1.50  --problem_path                          ""
% 6.92/1.50  --include_path                          ""
% 6.92/1.50  --clausifier                            res/vclausify_rel
% 6.92/1.50  --clausifier_options                    --mode clausify
% 6.92/1.50  --stdin                                 false
% 6.92/1.50  --stats_out                             all
% 6.92/1.50  
% 6.92/1.50  ------ General Options
% 6.92/1.50  
% 6.92/1.50  --fof                                   false
% 6.92/1.50  --time_out_real                         305.
% 6.92/1.50  --time_out_virtual                      -1.
% 6.92/1.50  --symbol_type_check                     false
% 6.92/1.50  --clausify_out                          false
% 6.92/1.50  --sig_cnt_out                           false
% 6.92/1.50  --trig_cnt_out                          false
% 6.92/1.50  --trig_cnt_out_tolerance                1.
% 6.92/1.50  --trig_cnt_out_sk_spl                   false
% 6.92/1.50  --abstr_cl_out                          false
% 6.92/1.50  
% 6.92/1.50  ------ Global Options
% 6.92/1.50  
% 6.92/1.50  --schedule                              default
% 6.92/1.50  --add_important_lit                     false
% 6.92/1.50  --prop_solver_per_cl                    1000
% 6.92/1.50  --min_unsat_core                        false
% 6.92/1.50  --soft_assumptions                      false
% 6.92/1.50  --soft_lemma_size                       3
% 6.92/1.50  --prop_impl_unit_size                   0
% 6.92/1.50  --prop_impl_unit                        []
% 6.92/1.50  --share_sel_clauses                     true
% 6.92/1.50  --reset_solvers                         false
% 6.92/1.50  --bc_imp_inh                            [conj_cone]
% 6.92/1.50  --conj_cone_tolerance                   3.
% 6.92/1.50  --extra_neg_conj                        none
% 6.92/1.50  --large_theory_mode                     true
% 6.92/1.50  --prolific_symb_bound                   200
% 6.92/1.50  --lt_threshold                          2000
% 6.92/1.50  --clause_weak_htbl                      true
% 6.92/1.50  --gc_record_bc_elim                     false
% 6.92/1.50  
% 6.92/1.50  ------ Preprocessing Options
% 6.92/1.50  
% 6.92/1.50  --preprocessing_flag                    true
% 6.92/1.50  --time_out_prep_mult                    0.1
% 6.92/1.50  --splitting_mode                        input
% 6.92/1.50  --splitting_grd                         true
% 6.92/1.50  --splitting_cvd                         false
% 6.92/1.50  --splitting_cvd_svl                     false
% 6.92/1.50  --splitting_nvd                         32
% 6.92/1.50  --sub_typing                            true
% 6.92/1.50  --prep_gs_sim                           true
% 6.92/1.50  --prep_unflatten                        true
% 6.92/1.50  --prep_res_sim                          true
% 6.92/1.50  --prep_upred                            true
% 6.92/1.50  --prep_sem_filter                       exhaustive
% 6.92/1.50  --prep_sem_filter_out                   false
% 6.92/1.50  --pred_elim                             true
% 6.92/1.50  --res_sim_input                         true
% 6.92/1.50  --eq_ax_congr_red                       true
% 6.92/1.50  --pure_diseq_elim                       true
% 6.92/1.50  --brand_transform                       false
% 6.92/1.50  --non_eq_to_eq                          false
% 6.92/1.50  --prep_def_merge                        true
% 6.92/1.50  --prep_def_merge_prop_impl              false
% 6.92/1.50  --prep_def_merge_mbd                    true
% 6.92/1.50  --prep_def_merge_tr_red                 false
% 6.92/1.50  --prep_def_merge_tr_cl                  false
% 6.92/1.50  --smt_preprocessing                     true
% 6.92/1.50  --smt_ac_axioms                         fast
% 6.92/1.50  --preprocessed_out                      false
% 6.92/1.50  --preprocessed_stats                    false
% 6.92/1.50  
% 6.92/1.50  ------ Abstraction refinement Options
% 6.92/1.50  
% 6.92/1.50  --abstr_ref                             []
% 6.92/1.50  --abstr_ref_prep                        false
% 6.92/1.50  --abstr_ref_until_sat                   false
% 6.92/1.50  --abstr_ref_sig_restrict                funpre
% 6.92/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 6.92/1.50  --abstr_ref_under                       []
% 6.92/1.50  
% 6.92/1.50  ------ SAT Options
% 6.92/1.50  
% 6.92/1.50  --sat_mode                              false
% 6.92/1.50  --sat_fm_restart_options                ""
% 6.92/1.50  --sat_gr_def                            false
% 6.92/1.50  --sat_epr_types                         true
% 6.92/1.50  --sat_non_cyclic_types                  false
% 6.92/1.50  --sat_finite_models                     false
% 6.92/1.50  --sat_fm_lemmas                         false
% 6.92/1.50  --sat_fm_prep                           false
% 6.92/1.50  --sat_fm_uc_incr                        true
% 6.92/1.50  --sat_out_model                         small
% 6.92/1.50  --sat_out_clauses                       false
% 6.92/1.50  
% 6.92/1.50  ------ QBF Options
% 6.92/1.50  
% 6.92/1.50  --qbf_mode                              false
% 6.92/1.50  --qbf_elim_univ                         false
% 6.92/1.50  --qbf_dom_inst                          none
% 6.92/1.50  --qbf_dom_pre_inst                      false
% 6.92/1.50  --qbf_sk_in                             false
% 6.92/1.50  --qbf_pred_elim                         true
% 6.92/1.50  --qbf_split                             512
% 6.92/1.50  
% 6.92/1.50  ------ BMC1 Options
% 6.92/1.50  
% 6.92/1.50  --bmc1_incremental                      false
% 6.92/1.50  --bmc1_axioms                           reachable_all
% 6.92/1.50  --bmc1_min_bound                        0
% 6.92/1.50  --bmc1_max_bound                        -1
% 6.92/1.50  --bmc1_max_bound_default                -1
% 6.92/1.50  --bmc1_symbol_reachability              true
% 6.92/1.50  --bmc1_property_lemmas                  false
% 6.92/1.50  --bmc1_k_induction                      false
% 6.92/1.50  --bmc1_non_equiv_states                 false
% 6.92/1.50  --bmc1_deadlock                         false
% 6.92/1.50  --bmc1_ucm                              false
% 6.92/1.50  --bmc1_add_unsat_core                   none
% 6.92/1.50  --bmc1_unsat_core_children              false
% 6.92/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 6.92/1.50  --bmc1_out_stat                         full
% 6.92/1.50  --bmc1_ground_init                      false
% 6.92/1.50  --bmc1_pre_inst_next_state              false
% 6.92/1.50  --bmc1_pre_inst_state                   false
% 6.92/1.50  --bmc1_pre_inst_reach_state             false
% 6.92/1.50  --bmc1_out_unsat_core                   false
% 6.92/1.50  --bmc1_aig_witness_out                  false
% 6.92/1.50  --bmc1_verbose                          false
% 6.92/1.50  --bmc1_dump_clauses_tptp                false
% 6.92/1.50  --bmc1_dump_unsat_core_tptp             false
% 6.92/1.50  --bmc1_dump_file                        -
% 6.92/1.50  --bmc1_ucm_expand_uc_limit              128
% 6.92/1.50  --bmc1_ucm_n_expand_iterations          6
% 6.92/1.50  --bmc1_ucm_extend_mode                  1
% 6.92/1.50  --bmc1_ucm_init_mode                    2
% 6.92/1.50  --bmc1_ucm_cone_mode                    none
% 6.92/1.50  --bmc1_ucm_reduced_relation_type        0
% 6.92/1.50  --bmc1_ucm_relax_model                  4
% 6.92/1.50  --bmc1_ucm_full_tr_after_sat            true
% 6.92/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 6.92/1.50  --bmc1_ucm_layered_model                none
% 6.92/1.50  --bmc1_ucm_max_lemma_size               10
% 6.92/1.50  
% 6.92/1.50  ------ AIG Options
% 6.92/1.50  
% 6.92/1.50  --aig_mode                              false
% 6.92/1.50  
% 6.92/1.50  ------ Instantiation Options
% 6.92/1.50  
% 6.92/1.50  --instantiation_flag                    true
% 6.92/1.50  --inst_sos_flag                         false
% 6.92/1.50  --inst_sos_phase                        true
% 6.92/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.92/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.92/1.50  --inst_lit_sel_side                     num_symb
% 6.92/1.50  --inst_solver_per_active                1400
% 6.92/1.50  --inst_solver_calls_frac                1.
% 6.92/1.50  --inst_passive_queue_type               priority_queues
% 6.92/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.92/1.50  --inst_passive_queues_freq              [25;2]
% 6.92/1.50  --inst_dismatching                      true
% 6.92/1.50  --inst_eager_unprocessed_to_passive     true
% 6.92/1.50  --inst_prop_sim_given                   true
% 6.92/1.50  --inst_prop_sim_new                     false
% 6.92/1.50  --inst_subs_new                         false
% 6.92/1.50  --inst_eq_res_simp                      false
% 6.92/1.50  --inst_subs_given                       false
% 6.92/1.50  --inst_orphan_elimination               true
% 6.92/1.50  --inst_learning_loop_flag               true
% 6.92/1.50  --inst_learning_start                   3000
% 6.92/1.50  --inst_learning_factor                  2
% 6.92/1.50  --inst_start_prop_sim_after_learn       3
% 6.92/1.50  --inst_sel_renew                        solver
% 6.92/1.50  --inst_lit_activity_flag                true
% 6.92/1.50  --inst_restr_to_given                   false
% 6.92/1.50  --inst_activity_threshold               500
% 6.92/1.50  --inst_out_proof                        true
% 6.92/1.50  
% 6.92/1.50  ------ Resolution Options
% 6.92/1.50  
% 6.92/1.50  --resolution_flag                       true
% 6.92/1.50  --res_lit_sel                           adaptive
% 6.92/1.50  --res_lit_sel_side                      none
% 6.92/1.50  --res_ordering                          kbo
% 6.92/1.50  --res_to_prop_solver                    active
% 6.92/1.50  --res_prop_simpl_new                    false
% 6.92/1.50  --res_prop_simpl_given                  true
% 6.92/1.50  --res_passive_queue_type                priority_queues
% 6.92/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.92/1.50  --res_passive_queues_freq               [15;5]
% 6.92/1.50  --res_forward_subs                      full
% 6.92/1.50  --res_backward_subs                     full
% 6.92/1.50  --res_forward_subs_resolution           true
% 6.92/1.50  --res_backward_subs_resolution          true
% 6.92/1.50  --res_orphan_elimination                true
% 6.92/1.50  --res_time_limit                        2.
% 6.92/1.50  --res_out_proof                         true
% 6.92/1.50  
% 6.92/1.50  ------ Superposition Options
% 6.92/1.50  
% 6.92/1.50  --superposition_flag                    true
% 6.92/1.50  --sup_passive_queue_type                priority_queues
% 6.92/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.92/1.50  --sup_passive_queues_freq               [8;1;4]
% 6.92/1.50  --demod_completeness_check              fast
% 6.92/1.50  --demod_use_ground                      true
% 6.92/1.50  --sup_to_prop_solver                    passive
% 6.92/1.50  --sup_prop_simpl_new                    true
% 6.92/1.50  --sup_prop_simpl_given                  true
% 6.92/1.50  --sup_fun_splitting                     false
% 6.92/1.50  --sup_smt_interval                      50000
% 6.92/1.50  
% 6.92/1.50  ------ Superposition Simplification Setup
% 6.92/1.50  
% 6.92/1.50  --sup_indices_passive                   []
% 6.92/1.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.92/1.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.92/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.92/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 6.92/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.92/1.50  --sup_full_bw                           [BwDemod]
% 6.92/1.50  --sup_immed_triv                        [TrivRules]
% 6.92/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.92/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.92/1.50  --sup_immed_bw_main                     []
% 6.92/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.92/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 6.92/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.92/1.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.92/1.50  
% 6.92/1.50  ------ Combination Options
% 6.92/1.50  
% 6.92/1.50  --comb_res_mult                         3
% 6.92/1.50  --comb_sup_mult                         2
% 6.92/1.50  --comb_inst_mult                        10
% 6.92/1.50  
% 6.92/1.50  ------ Debug Options
% 6.92/1.50  
% 6.92/1.50  --dbg_backtrace                         false
% 6.92/1.50  --dbg_dump_prop_clauses                 false
% 6.92/1.50  --dbg_dump_prop_clauses_file            -
% 6.92/1.50  --dbg_out_stat                          false
% 6.92/1.50  ------ Parsing...
% 6.92/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 6.92/1.50  
% 6.92/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 6.92/1.50  
% 6.92/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 6.92/1.50  
% 6.92/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 6.92/1.50  ------ Proving...
% 6.92/1.50  ------ Problem Properties 
% 6.92/1.50  
% 6.92/1.50  
% 6.92/1.50  clauses                                 11
% 6.92/1.50  conjectures                             3
% 6.92/1.50  EPR                                     1
% 6.92/1.50  Horn                                    11
% 6.92/1.50  unary                                   4
% 6.92/1.50  binary                                  6
% 6.92/1.50  lits                                    19
% 6.92/1.50  lits eq                                 5
% 6.92/1.50  fd_pure                                 0
% 6.92/1.50  fd_pseudo                               0
% 6.92/1.50  fd_cond                                 0
% 6.92/1.50  fd_pseudo_cond                          0
% 6.92/1.50  AC symbols                              0
% 6.92/1.50  
% 6.92/1.50  ------ Schedule dynamic 5 is on 
% 6.92/1.50  
% 6.92/1.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 6.92/1.50  
% 6.92/1.50  
% 6.92/1.50  ------ 
% 6.92/1.50  Current options:
% 6.92/1.50  ------ 
% 6.92/1.50  
% 6.92/1.50  ------ Input Options
% 6.92/1.50  
% 6.92/1.50  --out_options                           all
% 6.92/1.50  --tptp_safe_out                         true
% 6.92/1.50  --problem_path                          ""
% 6.92/1.50  --include_path                          ""
% 6.92/1.50  --clausifier                            res/vclausify_rel
% 6.92/1.50  --clausifier_options                    --mode clausify
% 6.92/1.50  --stdin                                 false
% 6.92/1.50  --stats_out                             all
% 6.92/1.50  
% 6.92/1.50  ------ General Options
% 6.92/1.50  
% 6.92/1.50  --fof                                   false
% 6.92/1.50  --time_out_real                         305.
% 6.92/1.50  --time_out_virtual                      -1.
% 6.92/1.50  --symbol_type_check                     false
% 6.92/1.50  --clausify_out                          false
% 6.92/1.50  --sig_cnt_out                           false
% 6.92/1.50  --trig_cnt_out                          false
% 6.92/1.50  --trig_cnt_out_tolerance                1.
% 6.92/1.50  --trig_cnt_out_sk_spl                   false
% 6.92/1.50  --abstr_cl_out                          false
% 6.92/1.50  
% 6.92/1.50  ------ Global Options
% 6.92/1.50  
% 6.92/1.50  --schedule                              default
% 6.92/1.50  --add_important_lit                     false
% 6.92/1.50  --prop_solver_per_cl                    1000
% 6.92/1.50  --min_unsat_core                        false
% 6.92/1.50  --soft_assumptions                      false
% 6.92/1.50  --soft_lemma_size                       3
% 6.92/1.50  --prop_impl_unit_size                   0
% 6.92/1.50  --prop_impl_unit                        []
% 6.92/1.50  --share_sel_clauses                     true
% 6.92/1.50  --reset_solvers                         false
% 6.92/1.50  --bc_imp_inh                            [conj_cone]
% 6.92/1.50  --conj_cone_tolerance                   3.
% 6.92/1.50  --extra_neg_conj                        none
% 6.92/1.50  --large_theory_mode                     true
% 6.92/1.50  --prolific_symb_bound                   200
% 6.92/1.50  --lt_threshold                          2000
% 6.92/1.50  --clause_weak_htbl                      true
% 6.92/1.50  --gc_record_bc_elim                     false
% 6.92/1.50  
% 6.92/1.50  ------ Preprocessing Options
% 6.92/1.50  
% 6.92/1.50  --preprocessing_flag                    true
% 6.92/1.50  --time_out_prep_mult                    0.1
% 6.92/1.50  --splitting_mode                        input
% 6.92/1.50  --splitting_grd                         true
% 6.92/1.50  --splitting_cvd                         false
% 6.92/1.50  --splitting_cvd_svl                     false
% 6.92/1.50  --splitting_nvd                         32
% 6.92/1.50  --sub_typing                            true
% 6.92/1.50  --prep_gs_sim                           true
% 6.92/1.50  --prep_unflatten                        true
% 6.92/1.50  --prep_res_sim                          true
% 6.92/1.50  --prep_upred                            true
% 6.92/1.50  --prep_sem_filter                       exhaustive
% 6.92/1.50  --prep_sem_filter_out                   false
% 6.92/1.50  --pred_elim                             true
% 6.92/1.50  --res_sim_input                         true
% 6.92/1.50  --eq_ax_congr_red                       true
% 6.92/1.50  --pure_diseq_elim                       true
% 6.92/1.50  --brand_transform                       false
% 6.92/1.50  --non_eq_to_eq                          false
% 6.92/1.50  --prep_def_merge                        true
% 6.92/1.50  --prep_def_merge_prop_impl              false
% 6.92/1.50  --prep_def_merge_mbd                    true
% 6.92/1.50  --prep_def_merge_tr_red                 false
% 6.92/1.50  --prep_def_merge_tr_cl                  false
% 6.92/1.50  --smt_preprocessing                     true
% 6.92/1.50  --smt_ac_axioms                         fast
% 6.92/1.50  --preprocessed_out                      false
% 6.92/1.50  --preprocessed_stats                    false
% 6.92/1.50  
% 6.92/1.50  ------ Abstraction refinement Options
% 6.92/1.50  
% 6.92/1.50  --abstr_ref                             []
% 6.92/1.50  --abstr_ref_prep                        false
% 6.92/1.50  --abstr_ref_until_sat                   false
% 6.92/1.50  --abstr_ref_sig_restrict                funpre
% 6.92/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 6.92/1.50  --abstr_ref_under                       []
% 6.92/1.50  
% 6.92/1.50  ------ SAT Options
% 6.92/1.50  
% 6.92/1.50  --sat_mode                              false
% 6.92/1.50  --sat_fm_restart_options                ""
% 6.92/1.50  --sat_gr_def                            false
% 6.92/1.50  --sat_epr_types                         true
% 6.92/1.50  --sat_non_cyclic_types                  false
% 6.92/1.50  --sat_finite_models                     false
% 6.92/1.50  --sat_fm_lemmas                         false
% 6.92/1.50  --sat_fm_prep                           false
% 6.92/1.50  --sat_fm_uc_incr                        true
% 6.92/1.50  --sat_out_model                         small
% 6.92/1.50  --sat_out_clauses                       false
% 6.92/1.50  
% 6.92/1.50  ------ QBF Options
% 6.92/1.50  
% 6.92/1.50  --qbf_mode                              false
% 6.92/1.50  --qbf_elim_univ                         false
% 6.92/1.50  --qbf_dom_inst                          none
% 6.92/1.50  --qbf_dom_pre_inst                      false
% 6.92/1.50  --qbf_sk_in                             false
% 6.92/1.50  --qbf_pred_elim                         true
% 6.92/1.50  --qbf_split                             512
% 6.92/1.50  
% 6.92/1.50  ------ BMC1 Options
% 6.92/1.50  
% 6.92/1.50  --bmc1_incremental                      false
% 6.92/1.50  --bmc1_axioms                           reachable_all
% 6.92/1.50  --bmc1_min_bound                        0
% 6.92/1.50  --bmc1_max_bound                        -1
% 6.92/1.50  --bmc1_max_bound_default                -1
% 6.92/1.50  --bmc1_symbol_reachability              true
% 6.92/1.50  --bmc1_property_lemmas                  false
% 6.92/1.50  --bmc1_k_induction                      false
% 6.92/1.50  --bmc1_non_equiv_states                 false
% 6.92/1.50  --bmc1_deadlock                         false
% 6.92/1.50  --bmc1_ucm                              false
% 6.92/1.50  --bmc1_add_unsat_core                   none
% 6.92/1.50  --bmc1_unsat_core_children              false
% 6.92/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 6.92/1.50  --bmc1_out_stat                         full
% 6.92/1.50  --bmc1_ground_init                      false
% 6.92/1.50  --bmc1_pre_inst_next_state              false
% 6.92/1.50  --bmc1_pre_inst_state                   false
% 6.92/1.50  --bmc1_pre_inst_reach_state             false
% 6.92/1.50  --bmc1_out_unsat_core                   false
% 6.92/1.50  --bmc1_aig_witness_out                  false
% 6.92/1.50  --bmc1_verbose                          false
% 6.92/1.50  --bmc1_dump_clauses_tptp                false
% 6.92/1.50  --bmc1_dump_unsat_core_tptp             false
% 6.92/1.50  --bmc1_dump_file                        -
% 6.92/1.50  --bmc1_ucm_expand_uc_limit              128
% 6.92/1.50  --bmc1_ucm_n_expand_iterations          6
% 6.92/1.50  --bmc1_ucm_extend_mode                  1
% 6.92/1.50  --bmc1_ucm_init_mode                    2
% 6.92/1.50  --bmc1_ucm_cone_mode                    none
% 6.92/1.50  --bmc1_ucm_reduced_relation_type        0
% 6.92/1.50  --bmc1_ucm_relax_model                  4
% 6.92/1.50  --bmc1_ucm_full_tr_after_sat            true
% 6.92/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 6.92/1.50  --bmc1_ucm_layered_model                none
% 6.92/1.50  --bmc1_ucm_max_lemma_size               10
% 6.92/1.50  
% 6.92/1.50  ------ AIG Options
% 6.92/1.50  
% 6.92/1.50  --aig_mode                              false
% 6.92/1.50  
% 6.92/1.50  ------ Instantiation Options
% 6.92/1.50  
% 6.92/1.50  --instantiation_flag                    true
% 6.92/1.50  --inst_sos_flag                         false
% 6.92/1.50  --inst_sos_phase                        true
% 6.92/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.92/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.92/1.50  --inst_lit_sel_side                     none
% 6.92/1.50  --inst_solver_per_active                1400
% 6.92/1.50  --inst_solver_calls_frac                1.
% 6.92/1.50  --inst_passive_queue_type               priority_queues
% 6.92/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.92/1.50  --inst_passive_queues_freq              [25;2]
% 6.92/1.50  --inst_dismatching                      true
% 6.92/1.50  --inst_eager_unprocessed_to_passive     true
% 6.92/1.50  --inst_prop_sim_given                   true
% 6.92/1.50  --inst_prop_sim_new                     false
% 6.92/1.50  --inst_subs_new                         false
% 6.92/1.50  --inst_eq_res_simp                      false
% 6.92/1.50  --inst_subs_given                       false
% 6.92/1.50  --inst_orphan_elimination               true
% 6.92/1.50  --inst_learning_loop_flag               true
% 6.92/1.50  --inst_learning_start                   3000
% 6.92/1.50  --inst_learning_factor                  2
% 6.92/1.50  --inst_start_prop_sim_after_learn       3
% 6.92/1.50  --inst_sel_renew                        solver
% 6.92/1.50  --inst_lit_activity_flag                true
% 6.92/1.50  --inst_restr_to_given                   false
% 6.92/1.50  --inst_activity_threshold               500
% 6.92/1.50  --inst_out_proof                        true
% 6.92/1.50  
% 6.92/1.50  ------ Resolution Options
% 6.92/1.50  
% 6.92/1.50  --resolution_flag                       false
% 6.92/1.50  --res_lit_sel                           adaptive
% 6.92/1.50  --res_lit_sel_side                      none
% 6.92/1.50  --res_ordering                          kbo
% 6.92/1.50  --res_to_prop_solver                    active
% 6.92/1.50  --res_prop_simpl_new                    false
% 6.92/1.50  --res_prop_simpl_given                  true
% 6.92/1.50  --res_passive_queue_type                priority_queues
% 6.92/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.92/1.50  --res_passive_queues_freq               [15;5]
% 6.92/1.50  --res_forward_subs                      full
% 6.92/1.50  --res_backward_subs                     full
% 6.92/1.50  --res_forward_subs_resolution           true
% 6.92/1.50  --res_backward_subs_resolution          true
% 6.92/1.50  --res_orphan_elimination                true
% 6.92/1.50  --res_time_limit                        2.
% 6.92/1.50  --res_out_proof                         true
% 6.92/1.50  
% 6.92/1.50  ------ Superposition Options
% 6.92/1.50  
% 6.92/1.50  --superposition_flag                    true
% 6.92/1.50  --sup_passive_queue_type                priority_queues
% 6.92/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.92/1.50  --sup_passive_queues_freq               [8;1;4]
% 6.92/1.50  --demod_completeness_check              fast
% 6.92/1.50  --demod_use_ground                      true
% 6.92/1.50  --sup_to_prop_solver                    passive
% 6.92/1.50  --sup_prop_simpl_new                    true
% 6.92/1.50  --sup_prop_simpl_given                  true
% 6.92/1.50  --sup_fun_splitting                     false
% 6.92/1.50  --sup_smt_interval                      50000
% 6.92/1.50  
% 6.92/1.50  ------ Superposition Simplification Setup
% 6.92/1.50  
% 6.92/1.50  --sup_indices_passive                   []
% 6.92/1.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.92/1.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.92/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.92/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 6.92/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.92/1.50  --sup_full_bw                           [BwDemod]
% 6.92/1.50  --sup_immed_triv                        [TrivRules]
% 6.92/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.92/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.92/1.50  --sup_immed_bw_main                     []
% 6.92/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.92/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 6.92/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.92/1.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.92/1.50  
% 6.92/1.50  ------ Combination Options
% 6.92/1.50  
% 6.92/1.50  --comb_res_mult                         3
% 6.92/1.50  --comb_sup_mult                         2
% 6.92/1.50  --comb_inst_mult                        10
% 6.92/1.50  
% 6.92/1.50  ------ Debug Options
% 6.92/1.50  
% 6.92/1.50  --dbg_backtrace                         false
% 6.92/1.50  --dbg_dump_prop_clauses                 false
% 6.92/1.50  --dbg_dump_prop_clauses_file            -
% 6.92/1.50  --dbg_out_stat                          false
% 6.92/1.50  
% 6.92/1.50  
% 6.92/1.50  
% 6.92/1.50  
% 6.92/1.50  ------ Proving...
% 6.92/1.50  
% 6.92/1.50  
% 6.92/1.50  % SZS status Theorem for theBenchmark.p
% 6.92/1.50  
% 6.92/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 6.92/1.50  
% 6.92/1.50  fof(f10,conjecture,(
% 6.92/1.50    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 6.92/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.92/1.50  
% 6.92/1.50  fof(f11,negated_conjecture,(
% 6.92/1.50    ~! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 6.92/1.50    inference(negated_conjecture,[],[f10])).
% 6.92/1.50  
% 6.92/1.50  fof(f20,plain,(
% 6.92/1.50    ? [X0,X1] : ((~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1))) & v1_relat_1(X1))),
% 6.92/1.50    inference(ennf_transformation,[],[f11])).
% 6.92/1.50  
% 6.92/1.50  fof(f21,plain,(
% 6.92/1.50    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1))),
% 6.92/1.50    inference(flattening,[],[f20])).
% 6.92/1.50  
% 6.92/1.50  fof(f22,plain,(
% 6.92/1.50    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1)) => (~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1))),
% 6.92/1.50    introduced(choice_axiom,[])).
% 6.92/1.50  
% 6.92/1.50  fof(f23,plain,(
% 6.92/1.50    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1)),
% 6.92/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f22])).
% 6.92/1.50  
% 6.92/1.50  fof(f33,plain,(
% 6.92/1.50    v1_relat_1(sK1)),
% 6.92/1.50    inference(cnf_transformation,[],[f23])).
% 6.92/1.50  
% 6.92/1.50  fof(f4,axiom,(
% 6.92/1.50    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 6.92/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.92/1.50  
% 6.92/1.50  fof(f13,plain,(
% 6.92/1.50    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 6.92/1.50    inference(ennf_transformation,[],[f4])).
% 6.92/1.50  
% 6.92/1.50  fof(f27,plain,(
% 6.92/1.50    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 6.92/1.50    inference(cnf_transformation,[],[f13])).
% 6.92/1.50  
% 6.92/1.50  fof(f6,axiom,(
% 6.92/1.50    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 6.92/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.92/1.50  
% 6.92/1.50  fof(f15,plain,(
% 6.92/1.50    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 6.92/1.50    inference(ennf_transformation,[],[f6])).
% 6.92/1.50  
% 6.92/1.50  fof(f29,plain,(
% 6.92/1.50    ( ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 6.92/1.50    inference(cnf_transformation,[],[f15])).
% 6.92/1.50  
% 6.92/1.50  fof(f5,axiom,(
% 6.92/1.50    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 6.92/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.92/1.50  
% 6.92/1.50  fof(f14,plain,(
% 6.92/1.50    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 6.92/1.50    inference(ennf_transformation,[],[f5])).
% 6.92/1.50  
% 6.92/1.50  fof(f28,plain,(
% 6.92/1.50    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 6.92/1.50    inference(cnf_transformation,[],[f14])).
% 6.92/1.50  
% 6.92/1.50  fof(f9,axiom,(
% 6.92/1.50    ! [X0,X1,X2] : (v1_relat_1(X2) => k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1))),
% 6.92/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.92/1.50  
% 6.92/1.50  fof(f19,plain,(
% 6.92/1.50    ! [X0,X1,X2] : (k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2))),
% 6.92/1.50    inference(ennf_transformation,[],[f9])).
% 6.92/1.50  
% 6.92/1.50  fof(f32,plain,(
% 6.92/1.50    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 6.92/1.50    inference(cnf_transformation,[],[f19])).
% 6.92/1.50  
% 6.92/1.50  fof(f3,axiom,(
% 6.92/1.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 6.92/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.92/1.50  
% 6.92/1.50  fof(f26,plain,(
% 6.92/1.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 6.92/1.50    inference(cnf_transformation,[],[f3])).
% 6.92/1.50  
% 6.92/1.50  fof(f37,plain,(
% 6.92/1.50    ( ! [X2,X0,X1] : (k1_setfam_1(k2_tarski(X0,k10_relat_1(X2,X1))) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 6.92/1.50    inference(definition_unfolding,[],[f32,f26])).
% 6.92/1.50  
% 6.92/1.50  fof(f2,axiom,(
% 6.92/1.50    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 6.92/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.92/1.50  
% 6.92/1.50  fof(f25,plain,(
% 6.92/1.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 6.92/1.50    inference(cnf_transformation,[],[f2])).
% 6.92/1.50  
% 6.92/1.50  fof(f1,axiom,(
% 6.92/1.50    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) => r1_tarski(X0,X1))),
% 6.92/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.92/1.50  
% 6.92/1.50  fof(f12,plain,(
% 6.92/1.50    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 6.92/1.50    inference(ennf_transformation,[],[f1])).
% 6.92/1.50  
% 6.92/1.50  fof(f24,plain,(
% 6.92/1.50    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2))) )),
% 6.92/1.50    inference(cnf_transformation,[],[f12])).
% 6.92/1.50  
% 6.92/1.50  fof(f36,plain,(
% 6.92/1.50    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k1_setfam_1(k2_tarski(X1,X2)))) )),
% 6.92/1.50    inference(definition_unfolding,[],[f24,f26])).
% 6.92/1.50  
% 6.92/1.50  fof(f35,plain,(
% 6.92/1.50    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 6.92/1.50    inference(cnf_transformation,[],[f23])).
% 6.92/1.50  
% 6.92/1.50  fof(f34,plain,(
% 6.92/1.50    r1_tarski(sK0,k1_relat_1(sK1))),
% 6.92/1.50    inference(cnf_transformation,[],[f23])).
% 6.92/1.50  
% 6.92/1.50  fof(f8,axiom,(
% 6.92/1.50    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 6.92/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.92/1.50  
% 6.92/1.50  fof(f17,plain,(
% 6.92/1.50    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 6.92/1.50    inference(ennf_transformation,[],[f8])).
% 6.92/1.50  
% 6.92/1.50  fof(f18,plain,(
% 6.92/1.50    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 6.92/1.50    inference(flattening,[],[f17])).
% 6.92/1.50  
% 6.92/1.50  fof(f31,plain,(
% 6.92/1.50    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 6.92/1.50    inference(cnf_transformation,[],[f18])).
% 6.92/1.50  
% 6.92/1.50  fof(f7,axiom,(
% 6.92/1.50    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1))))),
% 6.92/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.92/1.50  
% 6.92/1.50  fof(f16,plain,(
% 6.92/1.50    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1))) | ~v1_relat_1(X1))),
% 6.92/1.50    inference(ennf_transformation,[],[f7])).
% 6.92/1.50  
% 6.92/1.50  fof(f30,plain,(
% 6.92/1.50    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1))) | ~v1_relat_1(X1)) )),
% 6.92/1.50    inference(cnf_transformation,[],[f16])).
% 6.92/1.50  
% 6.92/1.50  cnf(c_10,negated_conjecture,
% 6.92/1.50      ( v1_relat_1(sK1) ),
% 6.92/1.50      inference(cnf_transformation,[],[f33]) ).
% 6.92/1.50  
% 6.92/1.50  cnf(c_321,plain,
% 6.92/1.50      ( v1_relat_1(sK1) = iProver_top ),
% 6.92/1.50      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 6.92/1.50  
% 6.92/1.50  cnf(c_2,plain,
% 6.92/1.50      ( ~ v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1)) ),
% 6.92/1.50      inference(cnf_transformation,[],[f27]) ).
% 6.92/1.50  
% 6.92/1.50  cnf(c_329,plain,
% 6.92/1.50      ( v1_relat_1(X0) != iProver_top
% 6.92/1.50      | v1_relat_1(k7_relat_1(X0,X1)) = iProver_top ),
% 6.92/1.50      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 6.92/1.50  
% 6.92/1.50  cnf(c_4,plain,
% 6.92/1.50      ( ~ v1_relat_1(X0)
% 6.92/1.50      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
% 6.92/1.50      inference(cnf_transformation,[],[f29]) ).
% 6.92/1.50  
% 6.92/1.50  cnf(c_327,plain,
% 6.92/1.50      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
% 6.92/1.50      | v1_relat_1(X0) != iProver_top ),
% 6.92/1.50      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 6.92/1.50  
% 6.92/1.50  cnf(c_465,plain,
% 6.92/1.50      ( k10_relat_1(k7_relat_1(X0,X1),k2_relat_1(k7_relat_1(X0,X1))) = k1_relat_1(k7_relat_1(X0,X1))
% 6.92/1.50      | v1_relat_1(X0) != iProver_top ),
% 6.92/1.50      inference(superposition,[status(thm)],[c_329,c_327]) ).
% 6.92/1.50  
% 6.92/1.50  cnf(c_1495,plain,
% 6.92/1.50      ( k10_relat_1(k7_relat_1(sK1,X0),k2_relat_1(k7_relat_1(sK1,X0))) = k1_relat_1(k7_relat_1(sK1,X0)) ),
% 6.92/1.50      inference(superposition,[status(thm)],[c_321,c_465]) ).
% 6.92/1.50  
% 6.92/1.50  cnf(c_3,plain,
% 6.92/1.50      ( ~ v1_relat_1(X0)
% 6.92/1.50      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 6.92/1.50      inference(cnf_transformation,[],[f28]) ).
% 6.92/1.50  
% 6.92/1.50  cnf(c_328,plain,
% 6.92/1.50      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 6.92/1.50      | v1_relat_1(X0) != iProver_top ),
% 6.92/1.50      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 6.92/1.50  
% 6.92/1.50  cnf(c_541,plain,
% 6.92/1.50      ( k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0) ),
% 6.92/1.50      inference(superposition,[status(thm)],[c_321,c_328]) ).
% 6.92/1.50  
% 6.92/1.50  cnf(c_1497,plain,
% 6.92/1.50      ( k10_relat_1(k7_relat_1(sK1,X0),k9_relat_1(sK1,X0)) = k1_relat_1(k7_relat_1(sK1,X0)) ),
% 6.92/1.50      inference(light_normalisation,[status(thm)],[c_1495,c_541]) ).
% 6.92/1.50  
% 6.92/1.50  cnf(c_7,plain,
% 6.92/1.50      ( ~ v1_relat_1(X0)
% 6.92/1.50      | k1_setfam_1(k2_tarski(X1,k10_relat_1(X0,X2))) = k10_relat_1(k7_relat_1(X0,X1),X2) ),
% 6.92/1.50      inference(cnf_transformation,[],[f37]) ).
% 6.92/1.50  
% 6.92/1.50  cnf(c_324,plain,
% 6.92/1.50      ( k1_setfam_1(k2_tarski(X0,k10_relat_1(X1,X2))) = k10_relat_1(k7_relat_1(X1,X0),X2)
% 6.92/1.50      | v1_relat_1(X1) != iProver_top ),
% 6.92/1.50      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 6.92/1.50  
% 6.92/1.50  cnf(c_638,plain,
% 6.92/1.50      ( k1_setfam_1(k2_tarski(X0,k10_relat_1(sK1,X1))) = k10_relat_1(k7_relat_1(sK1,X0),X1) ),
% 6.92/1.50      inference(superposition,[status(thm)],[c_321,c_324]) ).
% 6.92/1.50  
% 6.92/1.50  cnf(c_1,plain,
% 6.92/1.50      ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
% 6.92/1.50      inference(cnf_transformation,[],[f25]) ).
% 6.92/1.50  
% 6.92/1.50  cnf(c_0,plain,
% 6.92/1.50      ( r1_tarski(X0,X1)
% 6.92/1.50      | ~ r1_tarski(X0,k1_setfam_1(k2_tarski(X1,X2))) ),
% 6.92/1.50      inference(cnf_transformation,[],[f36]) ).
% 6.92/1.50  
% 6.92/1.50  cnf(c_330,plain,
% 6.92/1.50      ( r1_tarski(X0,X1) = iProver_top
% 6.92/1.50      | r1_tarski(X0,k1_setfam_1(k2_tarski(X1,X2))) != iProver_top ),
% 6.92/1.50      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 6.92/1.50  
% 6.92/1.50  cnf(c_652,plain,
% 6.92/1.50      ( r1_tarski(X0,X1) = iProver_top
% 6.92/1.50      | r1_tarski(X0,k1_setfam_1(k2_tarski(X2,X1))) != iProver_top ),
% 6.92/1.50      inference(superposition,[status(thm)],[c_1,c_330]) ).
% 6.92/1.50  
% 6.92/1.50  cnf(c_1094,plain,
% 6.92/1.50      ( r1_tarski(X0,k10_relat_1(k7_relat_1(sK1,X1),X2)) != iProver_top
% 6.92/1.50      | r1_tarski(X0,k10_relat_1(sK1,X2)) = iProver_top ),
% 6.92/1.50      inference(superposition,[status(thm)],[c_638,c_652]) ).
% 6.92/1.50  
% 6.92/1.50  cnf(c_2140,plain,
% 6.92/1.50      ( r1_tarski(X0,k10_relat_1(sK1,k9_relat_1(sK1,X1))) = iProver_top
% 6.92/1.50      | r1_tarski(X0,k1_relat_1(k7_relat_1(sK1,X1))) != iProver_top ),
% 6.92/1.50      inference(superposition,[status(thm)],[c_1497,c_1094]) ).
% 6.92/1.50  
% 6.92/1.50  cnf(c_8,negated_conjecture,
% 6.92/1.50      ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
% 6.92/1.50      inference(cnf_transformation,[],[f35]) ).
% 6.92/1.50  
% 6.92/1.50  cnf(c_323,plain,
% 6.92/1.50      ( r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) != iProver_top ),
% 6.92/1.50      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 6.92/1.50  
% 6.92/1.50  cnf(c_24064,plain,
% 6.92/1.50      ( r1_tarski(sK0,k1_relat_1(k7_relat_1(sK1,sK0))) != iProver_top ),
% 6.92/1.50      inference(superposition,[status(thm)],[c_2140,c_323]) ).
% 6.92/1.50  
% 6.92/1.50  cnf(c_9,negated_conjecture,
% 6.92/1.50      ( r1_tarski(sK0,k1_relat_1(sK1)) ),
% 6.92/1.50      inference(cnf_transformation,[],[f34]) ).
% 6.92/1.50  
% 6.92/1.50  cnf(c_322,plain,
% 6.92/1.50      ( r1_tarski(sK0,k1_relat_1(sK1)) = iProver_top ),
% 6.92/1.50      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 6.92/1.50  
% 6.92/1.50  cnf(c_6,plain,
% 6.92/1.50      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 6.92/1.50      | ~ v1_relat_1(X1)
% 6.92/1.50      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
% 6.92/1.50      inference(cnf_transformation,[],[f31]) ).
% 6.92/1.50  
% 6.92/1.50  cnf(c_325,plain,
% 6.92/1.50      ( k1_relat_1(k7_relat_1(X0,X1)) = X1
% 6.92/1.50      | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
% 6.92/1.50      | v1_relat_1(X0) != iProver_top ),
% 6.92/1.50      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 6.92/1.50  
% 6.92/1.50  cnf(c_912,plain,
% 6.92/1.50      ( k1_relat_1(k7_relat_1(sK1,sK0)) = sK0
% 6.92/1.50      | v1_relat_1(sK1) != iProver_top ),
% 6.92/1.50      inference(superposition,[status(thm)],[c_322,c_325]) ).
% 6.92/1.50  
% 6.92/1.50  cnf(c_395,plain,
% 6.92/1.50      ( ~ r1_tarski(sK0,k1_relat_1(sK1))
% 6.92/1.50      | ~ v1_relat_1(sK1)
% 6.92/1.50      | k1_relat_1(k7_relat_1(sK1,sK0)) = sK0 ),
% 6.92/1.50      inference(instantiation,[status(thm)],[c_6]) ).
% 6.92/1.50  
% 6.92/1.50  cnf(c_1116,plain,
% 6.92/1.50      ( k1_relat_1(k7_relat_1(sK1,sK0)) = sK0 ),
% 6.92/1.50      inference(global_propositional_subsumption,
% 6.92/1.50                [status(thm)],
% 6.92/1.50                [c_912,c_10,c_9,c_395]) ).
% 6.92/1.50  
% 6.92/1.50  cnf(c_24071,plain,
% 6.92/1.50      ( r1_tarski(sK0,sK0) != iProver_top ),
% 6.92/1.50      inference(light_normalisation,[status(thm)],[c_24064,c_1116]) ).
% 6.92/1.50  
% 6.92/1.50  cnf(c_5,plain,
% 6.92/1.50      ( r1_tarski(k10_relat_1(X0,X1),k10_relat_1(X0,k2_relat_1(X0)))
% 6.92/1.50      | ~ v1_relat_1(X0) ),
% 6.92/1.50      inference(cnf_transformation,[],[f30]) ).
% 6.92/1.50  
% 6.92/1.50  cnf(c_326,plain,
% 6.92/1.50      ( r1_tarski(k10_relat_1(X0,X1),k10_relat_1(X0,k2_relat_1(X0))) = iProver_top
% 6.92/1.50      | v1_relat_1(X0) != iProver_top ),
% 6.92/1.50      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 6.92/1.50  
% 6.92/1.50  cnf(c_1913,plain,
% 6.92/1.50      ( r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),k10_relat_1(k7_relat_1(sK1,X0),k2_relat_1(k7_relat_1(sK1,X0)))) = iProver_top
% 6.92/1.50      | v1_relat_1(k7_relat_1(sK1,X0)) != iProver_top ),
% 6.92/1.50      inference(superposition,[status(thm)],[c_1497,c_326]) ).
% 6.92/1.50  
% 6.92/1.50  cnf(c_1921,plain,
% 6.92/1.50      ( r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),k1_relat_1(k7_relat_1(sK1,X0))) = iProver_top
% 6.92/1.50      | v1_relat_1(k7_relat_1(sK1,X0)) != iProver_top ),
% 6.92/1.50      inference(light_normalisation,[status(thm)],[c_1913,c_541,c_1497]) ).
% 6.92/1.50  
% 6.92/1.50  cnf(c_2178,plain,
% 6.92/1.50      ( r1_tarski(sK0,sK0) = iProver_top
% 6.92/1.50      | v1_relat_1(k7_relat_1(sK1,sK0)) != iProver_top ),
% 6.92/1.50      inference(superposition,[status(thm)],[c_1116,c_1921]) ).
% 6.92/1.50  
% 6.92/1.50  cnf(c_1572,plain,
% 6.92/1.50      ( v1_relat_1(k7_relat_1(sK1,sK0)) | ~ v1_relat_1(sK1) ),
% 6.92/1.50      inference(instantiation,[status(thm)],[c_2]) ).
% 6.92/1.50  
% 6.92/1.50  cnf(c_1573,plain,
% 6.92/1.50      ( v1_relat_1(k7_relat_1(sK1,sK0)) = iProver_top
% 6.92/1.50      | v1_relat_1(sK1) != iProver_top ),
% 6.92/1.50      inference(predicate_to_equality,[status(thm)],[c_1572]) ).
% 6.92/1.50  
% 6.92/1.50  cnf(c_11,plain,
% 6.92/1.50      ( v1_relat_1(sK1) = iProver_top ),
% 6.92/1.50      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 6.92/1.50  
% 6.92/1.50  cnf(contradiction,plain,
% 6.92/1.50      ( $false ),
% 6.92/1.50      inference(minisat,[status(thm)],[c_24071,c_2178,c_1573,c_11]) ).
% 6.92/1.50  
% 6.92/1.50  
% 6.92/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 6.92/1.50  
% 6.92/1.50  ------                               Statistics
% 6.92/1.50  
% 6.92/1.50  ------ General
% 6.92/1.50  
% 6.92/1.50  abstr_ref_over_cycles:                  0
% 6.92/1.50  abstr_ref_under_cycles:                 0
% 6.92/1.50  gc_basic_clause_elim:                   0
% 6.92/1.50  forced_gc_time:                         0
% 6.92/1.50  parsing_time:                           0.007
% 6.92/1.50  unif_index_cands_time:                  0.
% 6.92/1.50  unif_index_add_time:                    0.
% 6.92/1.50  orderings_time:                         0.
% 6.92/1.50  out_proof_time:                         0.006
% 6.92/1.50  total_time:                             0.614
% 6.92/1.50  num_of_symbols:                         42
% 6.92/1.50  num_of_terms:                           24018
% 6.92/1.50  
% 6.92/1.50  ------ Preprocessing
% 6.92/1.50  
% 6.92/1.50  num_of_splits:                          0
% 6.92/1.50  num_of_split_atoms:                     0
% 6.92/1.50  num_of_reused_defs:                     0
% 6.92/1.50  num_eq_ax_congr_red:                    6
% 6.92/1.50  num_of_sem_filtered_clauses:            1
% 6.92/1.50  num_of_subtypes:                        0
% 6.92/1.50  monotx_restored_types:                  0
% 6.92/1.50  sat_num_of_epr_types:                   0
% 6.92/1.50  sat_num_of_non_cyclic_types:            0
% 6.92/1.50  sat_guarded_non_collapsed_types:        0
% 6.92/1.50  num_pure_diseq_elim:                    0
% 6.92/1.50  simp_replaced_by:                       0
% 6.92/1.50  res_preprocessed:                       54
% 6.92/1.50  prep_upred:                             0
% 6.92/1.50  prep_unflattend:                        0
% 6.92/1.50  smt_new_axioms:                         0
% 6.92/1.50  pred_elim_cands:                        2
% 6.92/1.50  pred_elim:                              0
% 6.92/1.50  pred_elim_cl:                           0
% 6.92/1.50  pred_elim_cycles:                       1
% 6.92/1.50  merged_defs:                            0
% 6.92/1.50  merged_defs_ncl:                        0
% 6.92/1.50  bin_hyper_res:                          0
% 6.92/1.50  prep_cycles:                            3
% 6.92/1.50  pred_elim_time:                         0.
% 6.92/1.50  splitting_time:                         0.
% 6.92/1.50  sem_filter_time:                        0.
% 6.92/1.50  monotx_time:                            0.
% 6.92/1.50  subtype_inf_time:                       0.
% 6.92/1.50  
% 6.92/1.50  ------ Problem properties
% 6.92/1.50  
% 6.92/1.50  clauses:                                11
% 6.92/1.50  conjectures:                            3
% 6.92/1.50  epr:                                    1
% 6.92/1.50  horn:                                   11
% 6.92/1.50  ground:                                 3
% 6.92/1.50  unary:                                  4
% 6.92/1.50  binary:                                 6
% 6.92/1.50  lits:                                   19
% 6.92/1.50  lits_eq:                                5
% 6.92/1.50  fd_pure:                                0
% 6.92/1.50  fd_pseudo:                              0
% 6.92/1.50  fd_cond:                                0
% 6.92/1.50  fd_pseudo_cond:                         0
% 6.92/1.50  ac_symbols:                             0
% 6.92/1.50  
% 6.92/1.50  ------ Propositional Solver
% 6.92/1.50  
% 6.92/1.50  prop_solver_calls:                      26
% 6.92/1.50  prop_fast_solver_calls:                 501
% 6.92/1.50  smt_solver_calls:                       0
% 6.92/1.50  smt_fast_solver_calls:                  0
% 6.92/1.50  prop_num_of_clauses:                    6935
% 6.92/1.50  prop_preprocess_simplified:             13706
% 6.92/1.50  prop_fo_subsumed:                       12
% 6.92/1.50  prop_solver_time:                       0.
% 6.92/1.50  smt_solver_time:                        0.
% 6.92/1.50  smt_fast_solver_time:                   0.
% 6.92/1.50  prop_fast_solver_time:                  0.
% 6.92/1.50  prop_unsat_core_time:                   0.
% 6.92/1.50  
% 6.92/1.50  ------ QBF
% 6.92/1.50  
% 6.92/1.50  qbf_q_res:                              0
% 6.92/1.50  qbf_num_tautologies:                    0
% 6.92/1.50  qbf_prep_cycles:                        0
% 6.92/1.50  
% 6.92/1.50  ------ BMC1
% 6.92/1.50  
% 6.92/1.50  bmc1_current_bound:                     -1
% 6.92/1.50  bmc1_last_solved_bound:                 -1
% 6.92/1.50  bmc1_unsat_core_size:                   -1
% 6.92/1.50  bmc1_unsat_core_parents_size:           -1
% 6.92/1.50  bmc1_merge_next_fun:                    0
% 6.92/1.50  bmc1_unsat_core_clauses_time:           0.
% 6.92/1.50  
% 6.92/1.50  ------ Instantiation
% 6.92/1.50  
% 6.92/1.50  inst_num_of_clauses:                    1735
% 6.92/1.50  inst_num_in_passive:                    804
% 6.92/1.50  inst_num_in_active:                     693
% 6.92/1.50  inst_num_in_unprocessed:                238
% 6.92/1.50  inst_num_of_loops:                      710
% 6.92/1.50  inst_num_of_learning_restarts:          0
% 6.92/1.50  inst_num_moves_active_passive:          14
% 6.92/1.50  inst_lit_activity:                      0
% 6.92/1.50  inst_lit_activity_moves:                0
% 6.92/1.50  inst_num_tautologies:                   0
% 6.92/1.50  inst_num_prop_implied:                  0
% 6.92/1.50  inst_num_existing_simplified:           0
% 6.92/1.50  inst_num_eq_res_simplified:             0
% 6.92/1.50  inst_num_child_elim:                    0
% 6.92/1.50  inst_num_of_dismatching_blockings:      2203
% 6.92/1.50  inst_num_of_non_proper_insts:           2798
% 6.92/1.50  inst_num_of_duplicates:                 0
% 6.92/1.50  inst_inst_num_from_inst_to_res:         0
% 6.92/1.50  inst_dismatching_checking_time:         0.
% 6.92/1.50  
% 6.92/1.50  ------ Resolution
% 6.92/1.50  
% 6.92/1.50  res_num_of_clauses:                     0
% 6.92/1.50  res_num_in_passive:                     0
% 6.92/1.50  res_num_in_active:                      0
% 6.92/1.50  res_num_of_loops:                       57
% 6.92/1.50  res_forward_subset_subsumed:            223
% 6.92/1.50  res_backward_subset_subsumed:           4
% 6.92/1.50  res_forward_subsumed:                   0
% 6.92/1.50  res_backward_subsumed:                  0
% 6.92/1.50  res_forward_subsumption_resolution:     0
% 6.92/1.50  res_backward_subsumption_resolution:    0
% 6.92/1.50  res_clause_to_clause_subsumption:       4572
% 6.92/1.50  res_orphan_elimination:                 0
% 6.92/1.50  res_tautology_del:                      324
% 6.92/1.50  res_num_eq_res_simplified:              0
% 6.92/1.50  res_num_sel_changes:                    0
% 6.92/1.50  res_moves_from_active_to_pass:          0
% 6.92/1.50  
% 6.92/1.50  ------ Superposition
% 6.92/1.50  
% 6.92/1.50  sup_time_total:                         0.
% 6.92/1.50  sup_time_generating:                    0.
% 6.92/1.50  sup_time_sim_full:                      0.
% 6.92/1.50  sup_time_sim_immed:                     0.
% 6.92/1.50  
% 6.92/1.50  sup_num_of_clauses:                     1200
% 6.92/1.50  sup_num_in_active:                      131
% 6.92/1.50  sup_num_in_passive:                     1069
% 6.92/1.50  sup_num_of_loops:                       140
% 6.92/1.50  sup_fw_superposition:                   1822
% 6.92/1.50  sup_bw_superposition:                   1190
% 6.92/1.50  sup_immediate_simplified:               801
% 6.92/1.50  sup_given_eliminated:                   0
% 6.92/1.50  comparisons_done:                       0
% 6.92/1.50  comparisons_avoided:                    0
% 6.92/1.50  
% 6.92/1.50  ------ Simplifications
% 6.92/1.50  
% 6.92/1.50  
% 6.92/1.50  sim_fw_subset_subsumed:                 5
% 6.92/1.50  sim_bw_subset_subsumed:                 4
% 6.92/1.50  sim_fw_subsumed:                        234
% 6.92/1.50  sim_bw_subsumed:                        14
% 6.92/1.50  sim_fw_subsumption_res:                 0
% 6.92/1.50  sim_bw_subsumption_res:                 0
% 6.92/1.50  sim_tautology_del:                      3
% 6.92/1.50  sim_eq_tautology_del:                   89
% 6.92/1.50  sim_eq_res_simp:                        0
% 6.92/1.50  sim_fw_demodulated:                     529
% 6.92/1.50  sim_bw_demodulated:                     21
% 6.92/1.50  sim_light_normalised:                   293
% 6.92/1.50  sim_joinable_taut:                      0
% 6.92/1.50  sim_joinable_simp:                      0
% 6.92/1.50  sim_ac_normalised:                      0
% 6.92/1.50  sim_smt_subsumption:                    0
% 6.92/1.50  
%------------------------------------------------------------------------------
