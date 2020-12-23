%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:09:14 EST 2020

% Result     : Theorem 4.01s
% Output     : CNFRefutation 4.01s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 126 expanded)
%              Number of clauses        :   32 (  33 expanded)
%              Number of leaves         :   15 (  35 expanded)
%              Depth                    :   12
%              Number of atoms          :  145 ( 248 expanded)
%              Number of equality atoms :   79 ( 136 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( r1_tarski(k10_relat_1(X0,X2),X1)
         => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1,X2] :
            ( r1_tarski(k10_relat_1(X0,X2),X1)
           => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f13,plain,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1,X2] :
            ( r1_tarski(k10_relat_1(X0,X2),X1)
           => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f21,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
     => ( k10_relat_1(X0,sK2) != k10_relat_1(k7_relat_1(X0,sK1),sK2)
        & r1_tarski(k10_relat_1(X0,sK2),sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X0] :
        ( ? [X1,X2] :
            ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
            & r1_tarski(k10_relat_1(X0,X2),X1) )
        & v1_relat_1(X0) )
   => ( ? [X2,X1] :
          ( k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2)
          & r1_tarski(k10_relat_1(sK0,X2),X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)
    & r1_tarski(k10_relat_1(sK0,sK2),sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f21,f20])).

fof(f36,plain,(
    r1_tarski(k10_relat_1(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f26,f28])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f18])).

fof(f25,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f45,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f23])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f8])).

fof(f38,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f31,f32])).

fof(f39,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f30,f38])).

fof(f41,plain,(
    ! [X0,X1] : k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f29,f39,f39])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f42,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f33,f28,f39])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,k10_relat_1(X2,X1))) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f34,f28])).

fof(f35,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f37,plain,(
    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_9,negated_conjecture,
    ( r1_tarski(k10_relat_1(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_242,plain,
    ( r1_tarski(k10_relat_1(sK0,sK2),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_244,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_4,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_243,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_246,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_616,plain,
    ( k4_xboole_0(X0,X1) = X0
    | r1_tarski(X0,k4_xboole_0(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_243,c_246])).

cnf(c_2012,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_244,c_616])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_24,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_12266,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2012,c_24])).

cnf(c_12267,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_12266])).

cnf(c_12273,plain,
    ( k4_xboole_0(k10_relat_1(sK0,sK2),k4_xboole_0(k10_relat_1(sK0,sK2),sK1)) = k10_relat_1(sK0,sK2) ),
    inference(superposition,[status(thm)],[c_242,c_12267])).

cnf(c_5,plain,
    ( k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_6,plain,
    ( k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_302,plain,
    ( k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_5,c_6])).

cnf(c_448,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_302,c_6])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | k4_xboole_0(X1,k4_xboole_0(X1,k10_relat_1(X0,X2))) = k10_relat_1(k7_relat_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_10,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_93,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k10_relat_1(X1,X2))) = k10_relat_1(k7_relat_1(X1,X0),X2)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_10])).

cnf(c_94,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k10_relat_1(sK0,X1))) = k10_relat_1(k7_relat_1(sK0,X0),X1) ),
    inference(unflattening,[status(thm)],[c_93])).

cnf(c_608,plain,
    ( k4_xboole_0(k10_relat_1(sK0,X0),k4_xboole_0(k10_relat_1(sK0,X0),X1)) = k10_relat_1(k7_relat_1(sK0,X1),X0) ),
    inference(superposition,[status(thm)],[c_448,c_94])).

cnf(c_14996,plain,
    ( k10_relat_1(k7_relat_1(sK0,sK1),sK2) = k10_relat_1(sK0,sK2) ),
    inference(superposition,[status(thm)],[c_12273,c_608])).

cnf(c_139,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_296,plain,
    ( k10_relat_1(sK0,sK2) = k10_relat_1(sK0,sK2) ),
    inference(instantiation,[status(thm)],[c_139])).

cnf(c_140,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_269,plain,
    ( k10_relat_1(k7_relat_1(sK0,sK1),sK2) != X0
    | k10_relat_1(sK0,sK2) != X0
    | k10_relat_1(sK0,sK2) = k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    inference(instantiation,[status(thm)],[c_140])).

cnf(c_295,plain,
    ( k10_relat_1(k7_relat_1(sK0,sK1),sK2) != k10_relat_1(sK0,sK2)
    | k10_relat_1(sK0,sK2) = k10_relat_1(k7_relat_1(sK0,sK1),sK2)
    | k10_relat_1(sK0,sK2) != k10_relat_1(sK0,sK2) ),
    inference(instantiation,[status(thm)],[c_269])).

cnf(c_8,negated_conjecture,
    ( k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f37])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_14996,c_296,c_295,c_8])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:23:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 4.01/0.97  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.01/0.97  
% 4.01/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 4.01/0.97  
% 4.01/0.97  ------  iProver source info
% 4.01/0.97  
% 4.01/0.97  git: date: 2020-06-30 10:37:57 +0100
% 4.01/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 4.01/0.97  git: non_committed_changes: false
% 4.01/0.97  git: last_make_outside_of_git: false
% 4.01/0.97  
% 4.01/0.97  ------ 
% 4.01/0.97  ------ Parsing...
% 4.01/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 4.01/0.97  
% 4.01/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 4.01/0.97  
% 4.01/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 4.01/0.97  
% 4.01/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.01/0.97  ------ Proving...
% 4.01/0.97  ------ Problem Properties 
% 4.01/0.97  
% 4.01/0.97  
% 4.01/0.97  clauses                                 9
% 4.01/0.97  conjectures                             2
% 4.01/0.97  EPR                                     2
% 4.01/0.97  Horn                                    9
% 4.01/0.97  unary                                   7
% 4.01/0.97  binary                                  0
% 4.01/0.97  lits                                    13
% 4.01/0.97  lits eq                                 5
% 4.01/0.97  fd_pure                                 0
% 4.01/0.97  fd_pseudo                               0
% 4.01/0.97  fd_cond                                 0
% 4.01/0.97  fd_pseudo_cond                          1
% 4.01/0.97  AC symbols                              0
% 4.01/0.97  
% 4.01/0.97  ------ Input Options Time Limit: Unbounded
% 4.01/0.97  
% 4.01/0.97  
% 4.01/0.97  ------ 
% 4.01/0.97  Current options:
% 4.01/0.97  ------ 
% 4.01/0.97  
% 4.01/0.97  
% 4.01/0.97  
% 4.01/0.97  
% 4.01/0.97  ------ Proving...
% 4.01/0.97  
% 4.01/0.97  
% 4.01/0.97  % SZS status Theorem for theBenchmark.p
% 4.01/0.97  
% 4.01/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 4.01/0.97  
% 4.01/0.97  fof(f11,conjecture,(
% 4.01/0.97    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 4.01/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.01/0.97  
% 4.01/0.97  fof(f12,negated_conjecture,(
% 4.01/0.97    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 4.01/0.97    inference(negated_conjecture,[],[f11])).
% 4.01/0.97  
% 4.01/0.97  fof(f13,plain,(
% 4.01/0.97    ~! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 4.01/0.97    inference(pure_predicate_removal,[],[f12])).
% 4.01/0.97  
% 4.01/0.97  fof(f17,plain,(
% 4.01/0.97    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & v1_relat_1(X0))),
% 4.01/0.97    inference(ennf_transformation,[],[f13])).
% 4.01/0.97  
% 4.01/0.97  fof(f21,plain,(
% 4.01/0.97    ( ! [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) => (k10_relat_1(X0,sK2) != k10_relat_1(k7_relat_1(X0,sK1),sK2) & r1_tarski(k10_relat_1(X0,sK2),sK1))) )),
% 4.01/0.97    introduced(choice_axiom,[])).
% 4.01/0.97  
% 4.01/0.97  fof(f20,plain,(
% 4.01/0.97    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & v1_relat_1(X0)) => (? [X2,X1] : (k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2) & r1_tarski(k10_relat_1(sK0,X2),X1)) & v1_relat_1(sK0))),
% 4.01/0.97    introduced(choice_axiom,[])).
% 4.01/0.97  
% 4.01/0.97  fof(f22,plain,(
% 4.01/0.97    (k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) & r1_tarski(k10_relat_1(sK0,sK2),sK1)) & v1_relat_1(sK0)),
% 4.01/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f21,f20])).
% 4.01/0.97  
% 4.01/0.97  fof(f36,plain,(
% 4.01/0.97    r1_tarski(k10_relat_1(sK0,sK2),sK1)),
% 4.01/0.97    inference(cnf_transformation,[],[f22])).
% 4.01/0.97  
% 4.01/0.97  fof(f2,axiom,(
% 4.01/0.97    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 4.01/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.01/0.97  
% 4.01/0.97  fof(f14,plain,(
% 4.01/0.97    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 4.01/0.97    inference(ennf_transformation,[],[f2])).
% 4.01/0.97  
% 4.01/0.97  fof(f15,plain,(
% 4.01/0.97    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 4.01/0.97    inference(flattening,[],[f14])).
% 4.01/0.97  
% 4.01/0.97  fof(f26,plain,(
% 4.01/0.97    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 4.01/0.97    inference(cnf_transformation,[],[f15])).
% 4.01/0.97  
% 4.01/0.97  fof(f4,axiom,(
% 4.01/0.97    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 4.01/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.01/0.97  
% 4.01/0.97  fof(f28,plain,(
% 4.01/0.97    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 4.01/0.97    inference(cnf_transformation,[],[f4])).
% 4.01/0.97  
% 4.01/0.97  fof(f40,plain,(
% 4.01/0.97    ( ! [X2,X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 4.01/0.97    inference(definition_unfolding,[],[f26,f28])).
% 4.01/0.97  
% 4.01/0.97  fof(f3,axiom,(
% 4.01/0.97    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 4.01/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.01/0.97  
% 4.01/0.97  fof(f27,plain,(
% 4.01/0.97    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 4.01/0.97    inference(cnf_transformation,[],[f3])).
% 4.01/0.97  
% 4.01/0.97  fof(f1,axiom,(
% 4.01/0.97    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 4.01/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.01/0.97  
% 4.01/0.97  fof(f18,plain,(
% 4.01/0.97    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.01/0.97    inference(nnf_transformation,[],[f1])).
% 4.01/0.97  
% 4.01/0.97  fof(f19,plain,(
% 4.01/0.97    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.01/0.97    inference(flattening,[],[f18])).
% 4.01/0.97  
% 4.01/0.97  fof(f25,plain,(
% 4.01/0.97    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 4.01/0.97    inference(cnf_transformation,[],[f19])).
% 4.01/0.97  
% 4.01/0.97  fof(f23,plain,(
% 4.01/0.97    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 4.01/0.97    inference(cnf_transformation,[],[f19])).
% 4.01/0.97  
% 4.01/0.97  fof(f45,plain,(
% 4.01/0.97    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 4.01/0.97    inference(equality_resolution,[],[f23])).
% 4.01/0.97  
% 4.01/0.97  fof(f5,axiom,(
% 4.01/0.97    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 4.01/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.01/0.97  
% 4.01/0.97  fof(f29,plain,(
% 4.01/0.97    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 4.01/0.97    inference(cnf_transformation,[],[f5])).
% 4.01/0.97  
% 4.01/0.97  fof(f6,axiom,(
% 4.01/0.97    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 4.01/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.01/0.97  
% 4.01/0.97  fof(f30,plain,(
% 4.01/0.97    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 4.01/0.97    inference(cnf_transformation,[],[f6])).
% 4.01/0.97  
% 4.01/0.97  fof(f7,axiom,(
% 4.01/0.97    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 4.01/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.01/0.97  
% 4.01/0.97  fof(f31,plain,(
% 4.01/0.97    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 4.01/0.97    inference(cnf_transformation,[],[f7])).
% 4.01/0.97  
% 4.01/0.97  fof(f8,axiom,(
% 4.01/0.97    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 4.01/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.01/0.97  
% 4.01/0.97  fof(f32,plain,(
% 4.01/0.97    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 4.01/0.97    inference(cnf_transformation,[],[f8])).
% 4.01/0.97  
% 4.01/0.97  fof(f38,plain,(
% 4.01/0.97    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 4.01/0.97    inference(definition_unfolding,[],[f31,f32])).
% 4.01/0.97  
% 4.01/0.97  fof(f39,plain,(
% 4.01/0.97    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 4.01/0.97    inference(definition_unfolding,[],[f30,f38])).
% 4.01/0.97  
% 4.01/0.97  fof(f41,plain,(
% 4.01/0.97    ( ! [X0,X1] : (k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0)) )),
% 4.01/0.97    inference(definition_unfolding,[],[f29,f39,f39])).
% 4.01/0.97  
% 4.01/0.97  fof(f9,axiom,(
% 4.01/0.97    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 4.01/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.01/0.97  
% 4.01/0.97  fof(f33,plain,(
% 4.01/0.97    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 4.01/0.97    inference(cnf_transformation,[],[f9])).
% 4.01/0.97  
% 4.01/0.97  fof(f42,plain,(
% 4.01/0.97    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 4.01/0.97    inference(definition_unfolding,[],[f33,f28,f39])).
% 4.01/0.97  
% 4.01/0.97  fof(f10,axiom,(
% 4.01/0.97    ! [X0,X1,X2] : (v1_relat_1(X2) => k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1))),
% 4.01/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.01/0.97  
% 4.01/0.97  fof(f16,plain,(
% 4.01/0.97    ! [X0,X1,X2] : (k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2))),
% 4.01/0.97    inference(ennf_transformation,[],[f10])).
% 4.01/0.97  
% 4.01/0.97  fof(f34,plain,(
% 4.01/0.97    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 4.01/0.97    inference(cnf_transformation,[],[f16])).
% 4.01/0.97  
% 4.01/0.97  fof(f43,plain,(
% 4.01/0.97    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k10_relat_1(X2,X1))) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 4.01/0.97    inference(definition_unfolding,[],[f34,f28])).
% 4.01/0.97  
% 4.01/0.97  fof(f35,plain,(
% 4.01/0.97    v1_relat_1(sK0)),
% 4.01/0.97    inference(cnf_transformation,[],[f22])).
% 4.01/0.97  
% 4.01/0.97  fof(f37,plain,(
% 4.01/0.97    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)),
% 4.01/0.97    inference(cnf_transformation,[],[f22])).
% 4.01/0.97  
% 4.01/0.97  cnf(c_9,negated_conjecture,
% 4.01/0.97      ( r1_tarski(k10_relat_1(sK0,sK2),sK1) ),
% 4.01/0.97      inference(cnf_transformation,[],[f36]) ).
% 4.01/0.97  
% 4.01/0.97  cnf(c_242,plain,
% 4.01/0.97      ( r1_tarski(k10_relat_1(sK0,sK2),sK1) = iProver_top ),
% 4.01/0.97      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 4.01/0.97  
% 4.01/0.97  cnf(c_3,plain,
% 4.01/0.97      ( ~ r1_tarski(X0,X1)
% 4.01/0.97      | ~ r1_tarski(X0,X2)
% 4.01/0.97      | r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
% 4.01/0.97      inference(cnf_transformation,[],[f40]) ).
% 4.01/0.97  
% 4.01/0.97  cnf(c_244,plain,
% 4.01/0.97      ( r1_tarski(X0,X1) != iProver_top
% 4.01/0.97      | r1_tarski(X0,X2) != iProver_top
% 4.01/0.97      | r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = iProver_top ),
% 4.01/0.97      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 4.01/0.97  
% 4.01/0.97  cnf(c_4,plain,
% 4.01/0.97      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 4.01/0.97      inference(cnf_transformation,[],[f27]) ).
% 4.01/0.97  
% 4.01/0.97  cnf(c_243,plain,
% 4.01/0.97      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 4.01/0.97      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 4.01/0.97  
% 4.01/0.97  cnf(c_0,plain,
% 4.01/0.97      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 4.01/0.97      inference(cnf_transformation,[],[f25]) ).
% 4.01/0.97  
% 4.01/0.97  cnf(c_246,plain,
% 4.01/0.97      ( X0 = X1
% 4.01/0.97      | r1_tarski(X0,X1) != iProver_top
% 4.01/0.97      | r1_tarski(X1,X0) != iProver_top ),
% 4.01/0.97      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 4.01/0.97  
% 4.01/0.97  cnf(c_616,plain,
% 4.01/0.97      ( k4_xboole_0(X0,X1) = X0
% 4.01/0.97      | r1_tarski(X0,k4_xboole_0(X0,X1)) != iProver_top ),
% 4.01/0.97      inference(superposition,[status(thm)],[c_243,c_246]) ).
% 4.01/0.97  
% 4.01/0.97  cnf(c_2012,plain,
% 4.01/0.97      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
% 4.01/0.97      | r1_tarski(X0,X1) != iProver_top
% 4.01/0.97      | r1_tarski(X0,X0) != iProver_top ),
% 4.01/0.97      inference(superposition,[status(thm)],[c_244,c_616]) ).
% 4.01/0.97  
% 4.01/0.97  cnf(c_2,plain,
% 4.01/0.97      ( r1_tarski(X0,X0) ),
% 4.01/0.97      inference(cnf_transformation,[],[f45]) ).
% 4.01/0.97  
% 4.01/0.97  cnf(c_24,plain,
% 4.01/0.97      ( r1_tarski(X0,X0) = iProver_top ),
% 4.01/0.97      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 4.01/0.97  
% 4.01/0.97  cnf(c_12266,plain,
% 4.01/0.97      ( r1_tarski(X0,X1) != iProver_top
% 4.01/0.97      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 4.01/0.97      inference(global_propositional_subsumption,
% 4.01/0.97                [status(thm)],
% 4.01/0.97                [c_2012,c_24]) ).
% 4.01/0.97  
% 4.01/0.97  cnf(c_12267,plain,
% 4.01/0.97      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
% 4.01/0.97      | r1_tarski(X0,X1) != iProver_top ),
% 4.01/0.97      inference(renaming,[status(thm)],[c_12266]) ).
% 4.01/0.97  
% 4.01/0.97  cnf(c_12273,plain,
% 4.01/0.97      ( k4_xboole_0(k10_relat_1(sK0,sK2),k4_xboole_0(k10_relat_1(sK0,sK2),sK1)) = k10_relat_1(sK0,sK2) ),
% 4.01/0.97      inference(superposition,[status(thm)],[c_242,c_12267]) ).
% 4.01/0.97  
% 4.01/0.97  cnf(c_5,plain,
% 4.01/0.97      ( k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) ),
% 4.01/0.97      inference(cnf_transformation,[],[f41]) ).
% 4.01/0.97  
% 4.01/0.97  cnf(c_6,plain,
% 4.01/0.97      ( k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 4.01/0.97      inference(cnf_transformation,[],[f42]) ).
% 4.01/0.97  
% 4.01/0.97  cnf(c_302,plain,
% 4.01/0.97      ( k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 4.01/0.97      inference(superposition,[status(thm)],[c_5,c_6]) ).
% 4.01/0.97  
% 4.01/0.97  cnf(c_448,plain,
% 4.01/0.97      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 4.01/0.97      inference(superposition,[status(thm)],[c_302,c_6]) ).
% 4.01/0.97  
% 4.01/0.97  cnf(c_7,plain,
% 4.01/0.97      ( ~ v1_relat_1(X0)
% 4.01/0.97      | k4_xboole_0(X1,k4_xboole_0(X1,k10_relat_1(X0,X2))) = k10_relat_1(k7_relat_1(X0,X1),X2) ),
% 4.01/0.97      inference(cnf_transformation,[],[f43]) ).
% 4.01/0.97  
% 4.01/0.97  cnf(c_10,negated_conjecture,
% 4.01/0.97      ( v1_relat_1(sK0) ),
% 4.01/0.97      inference(cnf_transformation,[],[f35]) ).
% 4.01/0.97  
% 4.01/0.97  cnf(c_93,plain,
% 4.01/0.97      ( k4_xboole_0(X0,k4_xboole_0(X0,k10_relat_1(X1,X2))) = k10_relat_1(k7_relat_1(X1,X0),X2)
% 4.01/0.97      | sK0 != X1 ),
% 4.01/0.97      inference(resolution_lifted,[status(thm)],[c_7,c_10]) ).
% 4.01/0.97  
% 4.01/0.97  cnf(c_94,plain,
% 4.01/0.97      ( k4_xboole_0(X0,k4_xboole_0(X0,k10_relat_1(sK0,X1))) = k10_relat_1(k7_relat_1(sK0,X0),X1) ),
% 4.01/0.97      inference(unflattening,[status(thm)],[c_93]) ).
% 4.01/0.97  
% 4.01/0.97  cnf(c_608,plain,
% 4.01/0.97      ( k4_xboole_0(k10_relat_1(sK0,X0),k4_xboole_0(k10_relat_1(sK0,X0),X1)) = k10_relat_1(k7_relat_1(sK0,X1),X0) ),
% 4.01/0.97      inference(superposition,[status(thm)],[c_448,c_94]) ).
% 4.01/0.97  
% 4.01/0.97  cnf(c_14996,plain,
% 4.01/0.97      ( k10_relat_1(k7_relat_1(sK0,sK1),sK2) = k10_relat_1(sK0,sK2) ),
% 4.01/0.97      inference(superposition,[status(thm)],[c_12273,c_608]) ).
% 4.01/0.97  
% 4.01/0.97  cnf(c_139,plain,( X0 = X0 ),theory(equality) ).
% 4.01/0.97  
% 4.01/0.97  cnf(c_296,plain,
% 4.01/0.97      ( k10_relat_1(sK0,sK2) = k10_relat_1(sK0,sK2) ),
% 4.01/0.97      inference(instantiation,[status(thm)],[c_139]) ).
% 4.01/0.97  
% 4.01/0.97  cnf(c_140,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 4.01/0.97  
% 4.01/0.97  cnf(c_269,plain,
% 4.01/0.97      ( k10_relat_1(k7_relat_1(sK0,sK1),sK2) != X0
% 4.01/0.97      | k10_relat_1(sK0,sK2) != X0
% 4.01/0.97      | k10_relat_1(sK0,sK2) = k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
% 4.01/0.97      inference(instantiation,[status(thm)],[c_140]) ).
% 4.01/0.97  
% 4.01/0.97  cnf(c_295,plain,
% 4.01/0.97      ( k10_relat_1(k7_relat_1(sK0,sK1),sK2) != k10_relat_1(sK0,sK2)
% 4.01/0.97      | k10_relat_1(sK0,sK2) = k10_relat_1(k7_relat_1(sK0,sK1),sK2)
% 4.01/0.97      | k10_relat_1(sK0,sK2) != k10_relat_1(sK0,sK2) ),
% 4.01/0.97      inference(instantiation,[status(thm)],[c_269]) ).
% 4.01/0.97  
% 4.01/0.97  cnf(c_8,negated_conjecture,
% 4.01/0.97      ( k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
% 4.01/0.97      inference(cnf_transformation,[],[f37]) ).
% 4.01/0.97  
% 4.01/0.97  cnf(contradiction,plain,
% 4.01/0.97      ( $false ),
% 4.01/0.97      inference(minisat,[status(thm)],[c_14996,c_296,c_295,c_8]) ).
% 4.01/0.97  
% 4.01/0.97  
% 4.01/0.97  % SZS output end CNFRefutation for theBenchmark.p
% 4.01/0.97  
% 4.01/0.97  ------                               Statistics
% 4.01/0.97  
% 4.01/0.97  ------ Selected
% 4.01/0.97  
% 4.01/0.97  total_time:                             0.462
% 4.01/0.97  
%------------------------------------------------------------------------------
