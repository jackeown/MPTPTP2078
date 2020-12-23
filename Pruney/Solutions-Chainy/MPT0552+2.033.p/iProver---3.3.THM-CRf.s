%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:46:40 EST 2020

% Result     : Theorem 3.70s
% Output     : CNFRefutation 3.70s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 218 expanded)
%              Number of clauses        :   39 ( 104 expanded)
%              Number of leaves         :    8 (  38 expanded)
%              Depth                    :   14
%              Number of atoms          :  114 ( 400 expanded)
%              Number of equality atoms :   45 ( 114 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f16,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f16])).

fof(f24,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f20,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f9])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f25,plain,(
    ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_95,plain,
    ( k3_xboole_0(X0_38,X1_38) = k3_xboole_0(X1_38,X0_38) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_7,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_88,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_6235,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_88])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_93,plain,
    ( ~ v1_relat_1(X0_37)
    | v1_relat_1(k7_relat_1(X0_37,X0_38)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_6231,plain,
    ( v1_relat_1(X0_37) != iProver_top
    | v1_relat_1(k7_relat_1(X0_37,X0_38)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_93])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_90,plain,
    ( ~ v1_relat_1(X0_37)
    | k2_relat_1(k7_relat_1(X0_37,X0_38)) = k9_relat_1(X0_37,X0_38) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_6234,plain,
    ( k2_relat_1(k7_relat_1(X0_37,X0_38)) = k9_relat_1(X0_37,X0_38)
    | v1_relat_1(X0_37) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_90])).

cnf(c_6324,plain,
    ( k2_relat_1(k7_relat_1(k7_relat_1(X0_37,X0_38),X1_38)) = k9_relat_1(k7_relat_1(X0_37,X0_38),X1_38)
    | v1_relat_1(X0_37) != iProver_top ),
    inference(superposition,[status(thm)],[c_6231,c_6234])).

cnf(c_6465,plain,
    ( k2_relat_1(k7_relat_1(k7_relat_1(sK2,X0_38),X1_38)) = k9_relat_1(k7_relat_1(sK2,X0_38),X1_38) ),
    inference(superposition,[status(thm)],[c_6235,c_6324])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(k7_relat_1(X0,X1),X2) = k7_relat_1(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_92,plain,
    ( ~ v1_relat_1(X0_37)
    | k7_relat_1(k7_relat_1(X0_37,X0_38),X1_38) = k7_relat_1(X0_37,k3_xboole_0(X0_38,X1_38)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_6232,plain,
    ( k7_relat_1(k7_relat_1(X0_37,X0_38),X1_38) = k7_relat_1(X0_37,k3_xboole_0(X0_38,X1_38))
    | v1_relat_1(X0_37) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_92])).

cnf(c_6389,plain,
    ( k7_relat_1(sK2,k3_xboole_0(X0_38,X1_38)) = k7_relat_1(k7_relat_1(sK2,X0_38),X1_38) ),
    inference(superposition,[status(thm)],[c_6235,c_6232])).

cnf(c_6476,plain,
    ( k2_relat_1(k7_relat_1(sK2,k3_xboole_0(X0_38,X1_38))) = k9_relat_1(k7_relat_1(sK2,X0_38),X1_38) ),
    inference(light_normalisation,[status(thm)],[c_6465,c_6389])).

cnf(c_6323,plain,
    ( k2_relat_1(k7_relat_1(sK2,X0_38)) = k9_relat_1(sK2,X0_38) ),
    inference(superposition,[status(thm)],[c_6235,c_6234])).

cnf(c_6477,plain,
    ( k9_relat_1(sK2,k3_xboole_0(X0_38,X1_38)) = k9_relat_1(k7_relat_1(sK2,X0_38),X1_38) ),
    inference(demodulation,[status(thm)],[c_6476,c_6323])).

cnf(c_4,plain,
    ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_91,plain,
    ( r1_tarski(k9_relat_1(X0_37,X0_38),k2_relat_1(X0_37))
    | ~ v1_relat_1(X0_37) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_6233,plain,
    ( r1_tarski(k9_relat_1(X0_37,X0_38),k2_relat_1(X0_37)) = iProver_top
    | v1_relat_1(X0_37) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_91])).

cnf(c_6342,plain,
    ( r1_tarski(k9_relat_1(k7_relat_1(sK2,X0_38),X1_38),k9_relat_1(sK2,X0_38)) = iProver_top
    | v1_relat_1(k7_relat_1(sK2,X0_38)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6323,c_6233])).

cnf(c_8,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_5165,plain,
    ( v1_relat_1(k7_relat_1(sK2,X0_38))
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_93])).

cnf(c_5166,plain,
    ( v1_relat_1(k7_relat_1(sK2,X0_38)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5165])).

cnf(c_6363,plain,
    ( r1_tarski(k9_relat_1(k7_relat_1(sK2,X0_38),X1_38),k9_relat_1(sK2,X0_38)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6342,c_8,c_5166])).

cnf(c_6504,plain,
    ( r1_tarski(k9_relat_1(sK2,k3_xboole_0(X0_38,X1_38)),k9_relat_1(sK2,X0_38)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6477,c_6363])).

cnf(c_6587,plain,
    ( r1_tarski(k9_relat_1(sK2,k3_xboole_0(X0_38,X1_38)),k9_relat_1(sK2,X1_38)) = iProver_top ),
    inference(superposition,[status(thm)],[c_95,c_6504])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_94,plain,
    ( ~ r1_tarski(X0_38,X1_38)
    | ~ r1_tarski(X0_38,X2_38)
    | r1_tarski(X0_38,k3_xboole_0(X2_38,X1_38)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_6230,plain,
    ( r1_tarski(X0_38,X1_38) != iProver_top
    | r1_tarski(X0_38,X2_38) != iProver_top
    | r1_tarski(X0_38,k3_xboole_0(X2_38,X1_38)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_94])).

cnf(c_6,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_89,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_6236,plain,
    ( r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_89])).

cnf(c_6376,plain,
    ( r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k9_relat_1(sK2,sK1)) != iProver_top
    | r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k9_relat_1(sK2,sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6230,c_6236])).

cnf(c_6819,plain,
    ( r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k9_relat_1(sK2,sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6587,c_6376])).

cnf(c_7035,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6819,c_6504])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:02:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.70/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.70/0.98  
% 3.70/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.70/0.98  
% 3.70/0.98  ------  iProver source info
% 3.70/0.98  
% 3.70/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.70/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.70/0.98  git: non_committed_changes: false
% 3.70/0.98  git: last_make_outside_of_git: false
% 3.70/0.98  
% 3.70/0.98  ------ 
% 3.70/0.98  ------ Parsing...
% 3.70/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.70/0.98  
% 3.70/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.70/0.98  
% 3.70/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.70/0.98  
% 3.70/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.70/0.98  ------ Proving...
% 3.70/0.98  ------ Problem Properties 
% 3.70/0.98  
% 3.70/0.98  
% 3.70/0.98  clauses                                 8
% 3.70/0.98  conjectures                             2
% 3.70/0.98  EPR                                     1
% 3.70/0.98  Horn                                    8
% 3.70/0.98  unary                                   3
% 3.70/0.98  binary                                  4
% 3.70/0.98  lits                                    14
% 3.70/0.98  lits eq                                 3
% 3.70/0.98  fd_pure                                 0
% 3.70/0.98  fd_pseudo                               0
% 3.70/0.98  fd_cond                                 0
% 3.70/0.98  fd_pseudo_cond                          0
% 3.70/0.98  AC symbols                              0
% 3.70/0.98  
% 3.70/0.98  ------ Input Options Time Limit: Unbounded
% 3.70/0.98  
% 3.70/0.98  
% 3.70/0.98  
% 3.70/0.98  
% 3.70/0.98  ------ Preprocessing...
% 3.70/0.98  
% 3.70/0.98  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 3.70/0.98  Current options:
% 3.70/0.98  ------ 
% 3.70/0.98  
% 3.70/0.98  
% 3.70/0.98  
% 3.70/0.98  
% 3.70/0.98  ------ Proving...
% 3.70/0.98  
% 3.70/0.98  
% 3.70/0.98  ------ Preprocessing...
% 3.70/0.98  
% 3.70/0.98  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.70/0.98  
% 3.70/0.98  ------ Proving...
% 3.70/0.98  
% 3.70/0.98  
% 3.70/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.70/0.98  
% 3.70/0.98  ------ Proving...
% 3.70/0.98  
% 3.70/0.98  
% 3.70/0.98  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.70/0.98  
% 3.70/0.98  ------ Proving...
% 3.70/0.98  
% 3.70/0.98  
% 3.70/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.70/0.98  
% 3.70/0.98  ------ Proving...
% 3.70/0.98  
% 3.70/0.98  
% 3.70/0.98  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.70/0.98  
% 3.70/0.98  ------ Proving...
% 3.70/0.98  
% 3.70/0.98  
% 3.70/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.70/0.98  
% 3.70/0.98  ------ Proving...
% 3.70/0.98  
% 3.70/0.98  
% 3.70/0.98  ------ Preprocessing...
% 3.70/0.98  
% 3.70/0.98  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.70/0.98  
% 3.70/0.98  ------ Proving...
% 3.70/0.98  
% 3.70/0.98  
% 3.70/0.98  ------ Preprocessing...
% 3.70/0.98  
% 3.70/0.98  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.70/0.98  
% 3.70/0.98  ------ Proving...
% 3.70/0.98  
% 3.70/0.98  
% 3.70/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.70/0.98  
% 3.70/0.98  ------ Proving...
% 3.70/0.98  
% 3.70/0.98  
% 3.70/0.98  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.70/0.98  
% 3.70/0.98  ------ Proving...
% 3.70/0.98  
% 3.70/0.98  
% 3.70/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.70/0.98  
% 3.70/0.98  ------ Proving...
% 3.70/0.98  
% 3.70/0.98  
% 3.70/0.98  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.70/0.98  
% 3.70/0.98  ------ Proving...
% 3.70/0.98  
% 3.70/0.98  
% 3.70/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.70/0.98  
% 3.70/0.98  ------ Proving...
% 3.70/0.98  
% 3.70/0.98  
% 3.70/0.98  ------ Preprocessing...
% 3.70/0.98  
% 3.70/0.98  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.70/0.98  
% 3.70/0.98  ------ Proving...
% 3.70/0.98  
% 3.70/0.98  
% 3.70/0.98  ------ Preprocessing...
% 3.70/0.98  
% 3.70/0.98  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.70/0.98  
% 3.70/0.98  ------ Proving...
% 3.70/0.98  
% 3.70/0.98  
% 3.70/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.70/0.98  
% 3.70/0.98  ------ Proving...
% 3.70/0.98  
% 3.70/0.98  
% 3.70/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.70/0.98  
% 3.70/0.98  ------ Proving...
% 3.70/0.98  
% 3.70/0.98  
% 3.70/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.70/0.98  
% 3.70/0.98  ------ Proving...
% 3.70/0.98  
% 3.70/0.98  
% 3.70/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.70/0.98  
% 3.70/0.98  ------ Proving...
% 3.70/0.98  
% 3.70/0.98  
% 3.70/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.70/0.98  
% 3.70/0.98  ------ Proving...
% 3.70/0.98  
% 3.70/0.98  
% 3.70/0.98  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.70/0.98  
% 3.70/0.98  ------ Proving...
% 3.70/0.98  
% 3.70/0.98  
% 3.70/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.70/0.98  
% 3.70/0.98  ------ Proving...
% 3.70/0.98  
% 3.70/0.98  
% 3.70/0.98  % SZS status Theorem for theBenchmark.p
% 3.70/0.98  
% 3.70/0.98   Resolution empty clause
% 3.70/0.98  
% 3.70/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.70/0.98  
% 3.70/0.98  fof(f1,axiom,(
% 3.70/0.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.70/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.70/0.98  
% 3.70/0.98  fof(f18,plain,(
% 3.70/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.70/0.98    inference(cnf_transformation,[],[f1])).
% 3.70/0.98  
% 3.70/0.98  fof(f7,conjecture,(
% 3.70/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 3.70/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.70/0.98  
% 3.70/0.98  fof(f8,negated_conjecture,(
% 3.70/0.98    ~! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 3.70/0.98    inference(negated_conjecture,[],[f7])).
% 3.70/0.98  
% 3.70/0.98  fof(f15,plain,(
% 3.70/0.98    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) & v1_relat_1(X2))),
% 3.70/0.98    inference(ennf_transformation,[],[f8])).
% 3.70/0.98  
% 3.70/0.98  fof(f16,plain,(
% 3.70/0.98    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) & v1_relat_1(X2)) => (~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) & v1_relat_1(sK2))),
% 3.70/0.98    introduced(choice_axiom,[])).
% 3.70/0.98  
% 3.70/0.98  fof(f17,plain,(
% 3.70/0.98    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) & v1_relat_1(sK2)),
% 3.70/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f16])).
% 3.70/0.98  
% 3.70/0.98  fof(f24,plain,(
% 3.70/0.98    v1_relat_1(sK2)),
% 3.70/0.98    inference(cnf_transformation,[],[f17])).
% 3.70/0.98  
% 3.70/0.98  fof(f3,axiom,(
% 3.70/0.98    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 3.70/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.70/0.98  
% 3.70/0.98  fof(f11,plain,(
% 3.70/0.98    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 3.70/0.98    inference(ennf_transformation,[],[f3])).
% 3.70/0.98  
% 3.70/0.98  fof(f20,plain,(
% 3.70/0.98    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 3.70/0.98    inference(cnf_transformation,[],[f11])).
% 3.70/0.98  
% 3.70/0.98  fof(f6,axiom,(
% 3.70/0.98    ! [X0,X1] : (v1_relat_1(X1) => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)))),
% 3.70/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.70/0.98  
% 3.70/0.98  fof(f14,plain,(
% 3.70/0.98    ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 3.70/0.98    inference(ennf_transformation,[],[f6])).
% 3.70/0.98  
% 3.70/0.98  fof(f23,plain,(
% 3.70/0.98    ( ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 3.70/0.98    inference(cnf_transformation,[],[f14])).
% 3.70/0.98  
% 3.70/0.98  fof(f4,axiom,(
% 3.70/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1))),
% 3.70/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.70/0.98  
% 3.70/0.98  fof(f12,plain,(
% 3.70/0.98    ! [X0,X1,X2] : (k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2))),
% 3.70/0.98    inference(ennf_transformation,[],[f4])).
% 3.70/0.98  
% 3.70/0.98  fof(f21,plain,(
% 3.70/0.98    ( ! [X2,X0,X1] : (k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 3.70/0.98    inference(cnf_transformation,[],[f12])).
% 3.70/0.98  
% 3.70/0.98  fof(f5,axiom,(
% 3.70/0.98    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)))),
% 3.70/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.70/0.98  
% 3.70/0.98  fof(f13,plain,(
% 3.70/0.98    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 3.70/0.98    inference(ennf_transformation,[],[f5])).
% 3.70/0.98  
% 3.70/0.98  fof(f22,plain,(
% 3.70/0.98    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.70/0.98    inference(cnf_transformation,[],[f13])).
% 3.70/0.98  
% 3.70/0.98  fof(f2,axiom,(
% 3.70/0.98    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 3.70/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.70/0.98  
% 3.70/0.98  fof(f9,plain,(
% 3.70/0.98    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 3.70/0.98    inference(ennf_transformation,[],[f2])).
% 3.70/0.98  
% 3.70/0.98  fof(f10,plain,(
% 3.70/0.98    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 3.70/0.98    inference(flattening,[],[f9])).
% 3.70/0.98  
% 3.70/0.98  fof(f19,plain,(
% 3.70/0.98    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 3.70/0.98    inference(cnf_transformation,[],[f10])).
% 3.70/0.98  
% 3.70/0.98  fof(f25,plain,(
% 3.70/0.98    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))),
% 3.70/0.98    inference(cnf_transformation,[],[f17])).
% 3.70/0.98  
% 3.70/0.98  cnf(c_0,plain,
% 3.70/0.98      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 3.70/0.98      inference(cnf_transformation,[],[f18]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_95,plain,
% 3.70/0.98      ( k3_xboole_0(X0_38,X1_38) = k3_xboole_0(X1_38,X0_38) ),
% 3.70/0.98      inference(subtyping,[status(esa)],[c_0]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_7,negated_conjecture,
% 3.70/0.98      ( v1_relat_1(sK2) ),
% 3.70/0.98      inference(cnf_transformation,[],[f24]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_88,negated_conjecture,
% 3.70/0.98      ( v1_relat_1(sK2) ),
% 3.70/0.98      inference(subtyping,[status(esa)],[c_7]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_6235,plain,
% 3.70/0.98      ( v1_relat_1(sK2) = iProver_top ),
% 3.70/0.98      inference(predicate_to_equality,[status(thm)],[c_88]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_2,plain,
% 3.70/0.98      ( ~ v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1)) ),
% 3.70/0.98      inference(cnf_transformation,[],[f20]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_93,plain,
% 3.70/0.98      ( ~ v1_relat_1(X0_37) | v1_relat_1(k7_relat_1(X0_37,X0_38)) ),
% 3.70/0.98      inference(subtyping,[status(esa)],[c_2]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_6231,plain,
% 3.70/0.98      ( v1_relat_1(X0_37) != iProver_top
% 3.70/0.98      | v1_relat_1(k7_relat_1(X0_37,X0_38)) = iProver_top ),
% 3.70/0.98      inference(predicate_to_equality,[status(thm)],[c_93]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_5,plain,
% 3.70/0.98      ( ~ v1_relat_1(X0) | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 3.70/0.98      inference(cnf_transformation,[],[f23]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_90,plain,
% 3.70/0.98      ( ~ v1_relat_1(X0_37)
% 3.70/0.98      | k2_relat_1(k7_relat_1(X0_37,X0_38)) = k9_relat_1(X0_37,X0_38) ),
% 3.70/0.98      inference(subtyping,[status(esa)],[c_5]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_6234,plain,
% 3.70/0.98      ( k2_relat_1(k7_relat_1(X0_37,X0_38)) = k9_relat_1(X0_37,X0_38)
% 3.70/0.98      | v1_relat_1(X0_37) != iProver_top ),
% 3.70/0.98      inference(predicate_to_equality,[status(thm)],[c_90]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_6324,plain,
% 3.70/0.98      ( k2_relat_1(k7_relat_1(k7_relat_1(X0_37,X0_38),X1_38)) = k9_relat_1(k7_relat_1(X0_37,X0_38),X1_38)
% 3.70/0.98      | v1_relat_1(X0_37) != iProver_top ),
% 3.70/0.98      inference(superposition,[status(thm)],[c_6231,c_6234]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_6465,plain,
% 3.70/0.98      ( k2_relat_1(k7_relat_1(k7_relat_1(sK2,X0_38),X1_38)) = k9_relat_1(k7_relat_1(sK2,X0_38),X1_38) ),
% 3.70/0.98      inference(superposition,[status(thm)],[c_6235,c_6324]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_3,plain,
% 3.70/0.98      ( ~ v1_relat_1(X0)
% 3.70/0.98      | k7_relat_1(k7_relat_1(X0,X1),X2) = k7_relat_1(X0,k3_xboole_0(X1,X2)) ),
% 3.70/0.98      inference(cnf_transformation,[],[f21]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_92,plain,
% 3.70/0.98      ( ~ v1_relat_1(X0_37)
% 3.70/0.98      | k7_relat_1(k7_relat_1(X0_37,X0_38),X1_38) = k7_relat_1(X0_37,k3_xboole_0(X0_38,X1_38)) ),
% 3.70/0.98      inference(subtyping,[status(esa)],[c_3]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_6232,plain,
% 3.70/0.98      ( k7_relat_1(k7_relat_1(X0_37,X0_38),X1_38) = k7_relat_1(X0_37,k3_xboole_0(X0_38,X1_38))
% 3.70/0.98      | v1_relat_1(X0_37) != iProver_top ),
% 3.70/0.98      inference(predicate_to_equality,[status(thm)],[c_92]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_6389,plain,
% 3.70/0.98      ( k7_relat_1(sK2,k3_xboole_0(X0_38,X1_38)) = k7_relat_1(k7_relat_1(sK2,X0_38),X1_38) ),
% 3.70/0.98      inference(superposition,[status(thm)],[c_6235,c_6232]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_6476,plain,
% 3.70/0.98      ( k2_relat_1(k7_relat_1(sK2,k3_xboole_0(X0_38,X1_38))) = k9_relat_1(k7_relat_1(sK2,X0_38),X1_38) ),
% 3.70/0.98      inference(light_normalisation,[status(thm)],[c_6465,c_6389]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_6323,plain,
% 3.70/0.98      ( k2_relat_1(k7_relat_1(sK2,X0_38)) = k9_relat_1(sK2,X0_38) ),
% 3.70/0.98      inference(superposition,[status(thm)],[c_6235,c_6234]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_6477,plain,
% 3.70/0.98      ( k9_relat_1(sK2,k3_xboole_0(X0_38,X1_38)) = k9_relat_1(k7_relat_1(sK2,X0_38),X1_38) ),
% 3.70/0.98      inference(demodulation,[status(thm)],[c_6476,c_6323]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_4,plain,
% 3.70/0.98      ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0)) | ~ v1_relat_1(X0) ),
% 3.70/0.98      inference(cnf_transformation,[],[f22]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_91,plain,
% 3.70/0.98      ( r1_tarski(k9_relat_1(X0_37,X0_38),k2_relat_1(X0_37))
% 3.70/0.98      | ~ v1_relat_1(X0_37) ),
% 3.70/0.98      inference(subtyping,[status(esa)],[c_4]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_6233,plain,
% 3.70/0.98      ( r1_tarski(k9_relat_1(X0_37,X0_38),k2_relat_1(X0_37)) = iProver_top
% 3.70/0.98      | v1_relat_1(X0_37) != iProver_top ),
% 3.70/0.98      inference(predicate_to_equality,[status(thm)],[c_91]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_6342,plain,
% 3.70/0.98      ( r1_tarski(k9_relat_1(k7_relat_1(sK2,X0_38),X1_38),k9_relat_1(sK2,X0_38)) = iProver_top
% 3.70/0.98      | v1_relat_1(k7_relat_1(sK2,X0_38)) != iProver_top ),
% 3.70/0.98      inference(superposition,[status(thm)],[c_6323,c_6233]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_8,plain,
% 3.70/0.98      ( v1_relat_1(sK2) = iProver_top ),
% 3.70/0.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_5165,plain,
% 3.70/0.98      ( v1_relat_1(k7_relat_1(sK2,X0_38)) | ~ v1_relat_1(sK2) ),
% 3.70/0.98      inference(instantiation,[status(thm)],[c_93]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_5166,plain,
% 3.70/0.98      ( v1_relat_1(k7_relat_1(sK2,X0_38)) = iProver_top
% 3.70/0.98      | v1_relat_1(sK2) != iProver_top ),
% 3.70/0.98      inference(predicate_to_equality,[status(thm)],[c_5165]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_6363,plain,
% 3.70/0.98      ( r1_tarski(k9_relat_1(k7_relat_1(sK2,X0_38),X1_38),k9_relat_1(sK2,X0_38)) = iProver_top ),
% 3.70/0.98      inference(global_propositional_subsumption,
% 3.70/0.98                [status(thm)],
% 3.70/0.98                [c_6342,c_8,c_5166]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_6504,plain,
% 3.70/0.98      ( r1_tarski(k9_relat_1(sK2,k3_xboole_0(X0_38,X1_38)),k9_relat_1(sK2,X0_38)) = iProver_top ),
% 3.70/0.98      inference(demodulation,[status(thm)],[c_6477,c_6363]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_6587,plain,
% 3.70/0.98      ( r1_tarski(k9_relat_1(sK2,k3_xboole_0(X0_38,X1_38)),k9_relat_1(sK2,X1_38)) = iProver_top ),
% 3.70/0.98      inference(superposition,[status(thm)],[c_95,c_6504]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_1,plain,
% 3.70/0.98      ( ~ r1_tarski(X0,X1)
% 3.70/0.98      | ~ r1_tarski(X0,X2)
% 3.70/0.98      | r1_tarski(X0,k3_xboole_0(X2,X1)) ),
% 3.70/0.98      inference(cnf_transformation,[],[f19]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_94,plain,
% 3.70/0.98      ( ~ r1_tarski(X0_38,X1_38)
% 3.70/0.98      | ~ r1_tarski(X0_38,X2_38)
% 3.70/0.98      | r1_tarski(X0_38,k3_xboole_0(X2_38,X1_38)) ),
% 3.70/0.98      inference(subtyping,[status(esa)],[c_1]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_6230,plain,
% 3.70/0.98      ( r1_tarski(X0_38,X1_38) != iProver_top
% 3.70/0.98      | r1_tarski(X0_38,X2_38) != iProver_top
% 3.70/0.98      | r1_tarski(X0_38,k3_xboole_0(X2_38,X1_38)) = iProver_top ),
% 3.70/0.98      inference(predicate_to_equality,[status(thm)],[c_94]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_6,negated_conjecture,
% 3.70/0.98      ( ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) ),
% 3.70/0.98      inference(cnf_transformation,[],[f25]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_89,negated_conjecture,
% 3.70/0.98      ( ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) ),
% 3.70/0.98      inference(subtyping,[status(esa)],[c_6]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_6236,plain,
% 3.70/0.98      ( r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) != iProver_top ),
% 3.70/0.98      inference(predicate_to_equality,[status(thm)],[c_89]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_6376,plain,
% 3.70/0.98      ( r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k9_relat_1(sK2,sK1)) != iProver_top
% 3.70/0.98      | r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k9_relat_1(sK2,sK0)) != iProver_top ),
% 3.70/0.98      inference(superposition,[status(thm)],[c_6230,c_6236]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_6819,plain,
% 3.70/0.98      ( r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k9_relat_1(sK2,sK0)) != iProver_top ),
% 3.70/0.98      inference(superposition,[status(thm)],[c_6587,c_6376]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_7035,plain,
% 3.70/0.98      ( $false ),
% 3.70/0.98      inference(forward_subsumption_resolution,[status(thm)],[c_6819,c_6504]) ).
% 3.70/0.98  
% 3.70/0.98  
% 3.70/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.70/0.98  
% 3.70/0.98  ------                               Statistics
% 3.70/0.98  
% 3.70/0.98  ------ Selected
% 3.70/0.98  
% 3.70/0.98  total_time:                             0.23
% 3.70/0.98  
%------------------------------------------------------------------------------
