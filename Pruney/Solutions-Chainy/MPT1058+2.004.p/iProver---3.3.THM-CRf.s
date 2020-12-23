%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:09:12 EST 2020

% Result     : Theorem 3.10s
% Output     : CNFRefutation 3.10s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 156 expanded)
%              Number of clauses        :   31 (  36 expanded)
%              Number of leaves         :   14 (  43 expanded)
%              Depth                    :   14
%              Number of atoms          :  151 ( 327 expanded)
%              Number of equality atoms :   79 ( 169 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( r1_tarski(k10_relat_1(X0,X2),X1)
         => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1,X2] :
            ( r1_tarski(k10_relat_1(X0,X2),X1)
           => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f43,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
     => ( k10_relat_1(X0,sK4) != k10_relat_1(k7_relat_1(X0,sK3),sK4)
        & r1_tarski(k10_relat_1(X0,sK4),sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ? [X0] :
        ( ? [X1,X2] :
            ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
            & r1_tarski(k10_relat_1(X0,X2),X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X2,X1] :
          ( k10_relat_1(sK2,X2) != k10_relat_1(k7_relat_1(sK2,X1),X2)
          & r1_tarski(k10_relat_1(sK2,X2),X1) )
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( k10_relat_1(sK2,sK4) != k10_relat_1(k7_relat_1(sK2,sK3),sK4)
    & r1_tarski(k10_relat_1(sK2,sK4),sK3)
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f30,f43,f42])).

fof(f72,plain,(
    r1_tarski(k10_relat_1(sK2,sK4),sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f70,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f9,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f11])).

fof(f74,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f58,f59])).

fof(f75,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f57,f74])).

fof(f76,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f60,f75])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k1_setfam_1(k3_enumset1(X0,X0,X0,X0,k10_relat_1(X2,X1))) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f68,f76])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2)))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f53,f76])).

fof(f8,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f79,plain,(
    ! [X0,X1] : k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f56,f75,f75])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f77,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f52,f76])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f35])).

fof(f50,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f82,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f48])).

fof(f73,plain,(
    k10_relat_1(sK2,sK4) != k10_relat_1(k7_relat_1(sK2,sK3),sK4) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_22,negated_conjecture,
    ( r1_tarski(k10_relat_1(sK2,sK4),sK3) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_695,plain,
    ( r1_tarski(k10_relat_1(sK2,sK4),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_24,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_693,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_19,plain,
    ( ~ v1_relat_1(X0)
    | k1_setfam_1(k3_enumset1(X1,X1,X1,X1,k10_relat_1(X0,X2))) = k10_relat_1(k7_relat_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_697,plain,
    ( k1_setfam_1(k3_enumset1(X0,X0,X0,X0,k10_relat_1(X1,X2))) = k10_relat_1(k7_relat_1(X1,X0),X2)
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1805,plain,
    ( k1_setfam_1(k3_enumset1(X0,X0,X0,X0,k10_relat_1(sK2,X1))) = k10_relat_1(k7_relat_1(sK2,X0),X1) ),
    inference(superposition,[status(thm)],[c_693,c_697])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2))) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_707,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X0,k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3171,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k10_relat_1(k7_relat_1(sK2,X1),X2)) = iProver_top
    | r1_tarski(X0,k10_relat_1(sK2,X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1805,c_707])).

cnf(c_11,plain,
    ( k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_7,plain,
    ( r1_tarski(k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)),X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_708,plain,
    ( r1_tarski(k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1072,plain,
    ( r1_tarski(k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_11,c_708])).

cnf(c_2329,plain,
    ( r1_tarski(k10_relat_1(k7_relat_1(sK2,X0),X1),k10_relat_1(sK2,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1805,c_1072])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_711,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2644,plain,
    ( k10_relat_1(k7_relat_1(sK2,X0),X1) = k10_relat_1(sK2,X1)
    | r1_tarski(k10_relat_1(sK2,X1),k10_relat_1(k7_relat_1(sK2,X0),X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2329,c_711])).

cnf(c_3811,plain,
    ( k10_relat_1(k7_relat_1(sK2,X0),X1) = k10_relat_1(sK2,X1)
    | r1_tarski(k10_relat_1(sK2,X1),X0) != iProver_top
    | r1_tarski(k10_relat_1(sK2,X1),k10_relat_1(sK2,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3171,c_2644])).

cnf(c_5,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_710,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_7582,plain,
    ( k10_relat_1(k7_relat_1(sK2,X0),X1) = k10_relat_1(sK2,X1)
    | r1_tarski(k10_relat_1(sK2,X1),X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3811,c_710])).

cnf(c_7588,plain,
    ( k10_relat_1(k7_relat_1(sK2,sK3),sK4) = k10_relat_1(sK2,sK4) ),
    inference(superposition,[status(thm)],[c_695,c_7582])).

cnf(c_322,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_4898,plain,
    ( k10_relat_1(sK2,sK4) = k10_relat_1(sK2,sK4) ),
    inference(instantiation,[status(thm)],[c_322])).

cnf(c_323,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_933,plain,
    ( k10_relat_1(k7_relat_1(sK2,sK3),sK4) != X0
    | k10_relat_1(sK2,sK4) != X0
    | k10_relat_1(sK2,sK4) = k10_relat_1(k7_relat_1(sK2,sK3),sK4) ),
    inference(instantiation,[status(thm)],[c_323])).

cnf(c_1065,plain,
    ( k10_relat_1(k7_relat_1(sK2,sK3),sK4) != k10_relat_1(X0,X1)
    | k10_relat_1(sK2,sK4) != k10_relat_1(X0,X1)
    | k10_relat_1(sK2,sK4) = k10_relat_1(k7_relat_1(sK2,sK3),sK4) ),
    inference(instantiation,[status(thm)],[c_933])).

cnf(c_4897,plain,
    ( k10_relat_1(k7_relat_1(sK2,sK3),sK4) != k10_relat_1(sK2,sK4)
    | k10_relat_1(sK2,sK4) = k10_relat_1(k7_relat_1(sK2,sK3),sK4)
    | k10_relat_1(sK2,sK4) != k10_relat_1(sK2,sK4) ),
    inference(instantiation,[status(thm)],[c_1065])).

cnf(c_21,negated_conjecture,
    ( k10_relat_1(sK2,sK4) != k10_relat_1(k7_relat_1(sK2,sK3),sK4) ),
    inference(cnf_transformation,[],[f73])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7588,c_4898,c_4897,c_21])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:28:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.10/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.10/1.01  
% 3.10/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.10/1.01  
% 3.10/1.01  ------  iProver source info
% 3.10/1.01  
% 3.10/1.01  git: date: 2020-06-30 10:37:57 +0100
% 3.10/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.10/1.01  git: non_committed_changes: false
% 3.10/1.01  git: last_make_outside_of_git: false
% 3.10/1.01  
% 3.10/1.01  ------ 
% 3.10/1.01  ------ Parsing...
% 3.10/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.10/1.01  
% 3.10/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 3.10/1.01  
% 3.10/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.10/1.01  
% 3.10/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.10/1.01  ------ Proving...
% 3.10/1.01  ------ Problem Properties 
% 3.10/1.01  
% 3.10/1.01  
% 3.10/1.01  clauses                                 24
% 3.10/1.01  conjectures                             4
% 3.10/1.01  EPR                                     8
% 3.10/1.01  Horn                                    21
% 3.10/1.01  unary                                   8
% 3.10/1.01  binary                                  7
% 3.10/1.01  lits                                    60
% 3.10/1.01  lits eq                                 10
% 3.10/1.01  fd_pure                                 0
% 3.10/1.01  fd_pseudo                               0
% 3.10/1.01  fd_cond                                 1
% 3.10/1.01  fd_pseudo_cond                          4
% 3.10/1.01  AC symbols                              0
% 3.10/1.01  
% 3.10/1.01  ------ Input Options Time Limit: Unbounded
% 3.10/1.01  
% 3.10/1.01  
% 3.10/1.01  ------ 
% 3.10/1.01  Current options:
% 3.10/1.01  ------ 
% 3.10/1.01  
% 3.10/1.01  
% 3.10/1.01  
% 3.10/1.01  
% 3.10/1.01  ------ Proving...
% 3.10/1.01  
% 3.10/1.01  
% 3.10/1.01  % SZS status Theorem for theBenchmark.p
% 3.10/1.01  
% 3.10/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 3.10/1.01  
% 3.10/1.01  fof(f17,conjecture,(
% 3.10/1.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 3.10/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.10/1.01  
% 3.10/1.01  fof(f18,negated_conjecture,(
% 3.10/1.01    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 3.10/1.01    inference(negated_conjecture,[],[f17])).
% 3.10/1.01  
% 3.10/1.01  fof(f29,plain,(
% 3.10/1.01    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 3.10/1.01    inference(ennf_transformation,[],[f18])).
% 3.10/1.01  
% 3.10/1.01  fof(f30,plain,(
% 3.10/1.01    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 3.10/1.01    inference(flattening,[],[f29])).
% 3.10/1.01  
% 3.10/1.01  fof(f43,plain,(
% 3.10/1.01    ( ! [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) => (k10_relat_1(X0,sK4) != k10_relat_1(k7_relat_1(X0,sK3),sK4) & r1_tarski(k10_relat_1(X0,sK4),sK3))) )),
% 3.10/1.01    introduced(choice_axiom,[])).
% 3.10/1.01  
% 3.10/1.01  fof(f42,plain,(
% 3.10/1.01    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X2,X1] : (k10_relat_1(sK2,X2) != k10_relat_1(k7_relat_1(sK2,X1),X2) & r1_tarski(k10_relat_1(sK2,X2),X1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 3.10/1.01    introduced(choice_axiom,[])).
% 3.10/1.01  
% 3.10/1.01  fof(f44,plain,(
% 3.10/1.01    (k10_relat_1(sK2,sK4) != k10_relat_1(k7_relat_1(sK2,sK3),sK4) & r1_tarski(k10_relat_1(sK2,sK4),sK3)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 3.10/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f30,f43,f42])).
% 3.10/1.01  
% 3.10/1.01  fof(f72,plain,(
% 3.10/1.01    r1_tarski(k10_relat_1(sK2,sK4),sK3)),
% 3.10/1.01    inference(cnf_transformation,[],[f44])).
% 3.10/1.01  
% 3.10/1.01  fof(f70,plain,(
% 3.10/1.01    v1_relat_1(sK2)),
% 3.10/1.01    inference(cnf_transformation,[],[f44])).
% 3.10/1.01  
% 3.10/1.01  fof(f15,axiom,(
% 3.10/1.01    ! [X0,X1,X2] : (v1_relat_1(X2) => k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1))),
% 3.10/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.10/1.01  
% 3.10/1.01  fof(f27,plain,(
% 3.10/1.01    ! [X0,X1,X2] : (k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2))),
% 3.10/1.01    inference(ennf_transformation,[],[f15])).
% 3.10/1.01  
% 3.10/1.01  fof(f68,plain,(
% 3.10/1.01    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 3.10/1.01    inference(cnf_transformation,[],[f27])).
% 3.10/1.01  
% 3.10/1.01  fof(f12,axiom,(
% 3.10/1.01    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.10/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.10/1.01  
% 3.10/1.01  fof(f60,plain,(
% 3.10/1.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.10/1.01    inference(cnf_transformation,[],[f12])).
% 3.10/1.01  
% 3.10/1.01  fof(f9,axiom,(
% 3.10/1.01    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.10/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.10/1.01  
% 3.10/1.01  fof(f57,plain,(
% 3.10/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.10/1.01    inference(cnf_transformation,[],[f9])).
% 3.10/1.01  
% 3.10/1.01  fof(f10,axiom,(
% 3.10/1.01    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.10/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.10/1.01  
% 3.10/1.01  fof(f58,plain,(
% 3.10/1.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.10/1.01    inference(cnf_transformation,[],[f10])).
% 3.10/1.01  
% 3.10/1.01  fof(f11,axiom,(
% 3.10/1.01    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.10/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.10/1.01  
% 3.10/1.01  fof(f59,plain,(
% 3.10/1.01    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.10/1.01    inference(cnf_transformation,[],[f11])).
% 3.10/1.01  
% 3.10/1.01  fof(f74,plain,(
% 3.10/1.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 3.10/1.01    inference(definition_unfolding,[],[f58,f59])).
% 3.10/1.01  
% 3.10/1.01  fof(f75,plain,(
% 3.10/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 3.10/1.01    inference(definition_unfolding,[],[f57,f74])).
% 3.10/1.01  
% 3.10/1.01  fof(f76,plain,(
% 3.10/1.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 3.10/1.01    inference(definition_unfolding,[],[f60,f75])).
% 3.10/1.01  
% 3.10/1.01  fof(f80,plain,(
% 3.10/1.01    ( ! [X2,X0,X1] : (k1_setfam_1(k3_enumset1(X0,X0,X0,X0,k10_relat_1(X2,X1))) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 3.10/1.01    inference(definition_unfolding,[],[f68,f76])).
% 3.10/1.01  
% 3.10/1.01  fof(f5,axiom,(
% 3.10/1.01    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 3.10/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.10/1.01  
% 3.10/1.01  fof(f21,plain,(
% 3.10/1.01    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 3.10/1.01    inference(ennf_transformation,[],[f5])).
% 3.10/1.01  
% 3.10/1.01  fof(f22,plain,(
% 3.10/1.01    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 3.10/1.01    inference(flattening,[],[f21])).
% 3.10/1.01  
% 3.10/1.01  fof(f53,plain,(
% 3.10/1.01    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 3.10/1.01    inference(cnf_transformation,[],[f22])).
% 3.10/1.01  
% 3.10/1.01  fof(f78,plain,(
% 3.10/1.01    ( ! [X2,X0,X1] : (r1_tarski(X0,k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 3.10/1.01    inference(definition_unfolding,[],[f53,f76])).
% 3.10/1.01  
% 3.10/1.01  fof(f8,axiom,(
% 3.10/1.01    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 3.10/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.10/1.01  
% 3.10/1.01  fof(f56,plain,(
% 3.10/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 3.10/1.01    inference(cnf_transformation,[],[f8])).
% 3.10/1.01  
% 3.10/1.01  fof(f79,plain,(
% 3.10/1.01    ( ! [X0,X1] : (k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0)) )),
% 3.10/1.01    inference(definition_unfolding,[],[f56,f75,f75])).
% 3.10/1.01  
% 3.10/1.01  fof(f4,axiom,(
% 3.10/1.01    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 3.10/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.10/1.01  
% 3.10/1.01  fof(f52,plain,(
% 3.10/1.01    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 3.10/1.01    inference(cnf_transformation,[],[f4])).
% 3.10/1.01  
% 3.10/1.01  fof(f77,plain,(
% 3.10/1.01    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)),X0)) )),
% 3.10/1.01    inference(definition_unfolding,[],[f52,f76])).
% 3.10/1.01  
% 3.10/1.01  fof(f2,axiom,(
% 3.10/1.01    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.10/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.10/1.01  
% 3.10/1.01  fof(f35,plain,(
% 3.10/1.01    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.10/1.01    inference(nnf_transformation,[],[f2])).
% 3.10/1.01  
% 3.10/1.01  fof(f36,plain,(
% 3.10/1.01    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.10/1.01    inference(flattening,[],[f35])).
% 3.10/1.01  
% 3.10/1.01  fof(f50,plain,(
% 3.10/1.01    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.10/1.01    inference(cnf_transformation,[],[f36])).
% 3.10/1.01  
% 3.10/1.01  fof(f48,plain,(
% 3.10/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.10/1.01    inference(cnf_transformation,[],[f36])).
% 3.10/1.01  
% 3.10/1.01  fof(f82,plain,(
% 3.10/1.01    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.10/1.01    inference(equality_resolution,[],[f48])).
% 3.10/1.01  
% 3.10/1.01  fof(f73,plain,(
% 3.10/1.01    k10_relat_1(sK2,sK4) != k10_relat_1(k7_relat_1(sK2,sK3),sK4)),
% 3.10/1.01    inference(cnf_transformation,[],[f44])).
% 3.10/1.01  
% 3.10/1.01  cnf(c_22,negated_conjecture,
% 3.10/1.01      ( r1_tarski(k10_relat_1(sK2,sK4),sK3) ),
% 3.10/1.01      inference(cnf_transformation,[],[f72]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_695,plain,
% 3.10/1.01      ( r1_tarski(k10_relat_1(sK2,sK4),sK3) = iProver_top ),
% 3.10/1.01      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_24,negated_conjecture,
% 3.10/1.01      ( v1_relat_1(sK2) ),
% 3.10/1.01      inference(cnf_transformation,[],[f70]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_693,plain,
% 3.10/1.01      ( v1_relat_1(sK2) = iProver_top ),
% 3.10/1.01      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_19,plain,
% 3.10/1.01      ( ~ v1_relat_1(X0)
% 3.10/1.01      | k1_setfam_1(k3_enumset1(X1,X1,X1,X1,k10_relat_1(X0,X2))) = k10_relat_1(k7_relat_1(X0,X1),X2) ),
% 3.10/1.01      inference(cnf_transformation,[],[f80]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_697,plain,
% 3.10/1.01      ( k1_setfam_1(k3_enumset1(X0,X0,X0,X0,k10_relat_1(X1,X2))) = k10_relat_1(k7_relat_1(X1,X0),X2)
% 3.10/1.01      | v1_relat_1(X1) != iProver_top ),
% 3.10/1.01      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_1805,plain,
% 3.10/1.01      ( k1_setfam_1(k3_enumset1(X0,X0,X0,X0,k10_relat_1(sK2,X1))) = k10_relat_1(k7_relat_1(sK2,X0),X1) ),
% 3.10/1.01      inference(superposition,[status(thm)],[c_693,c_697]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_8,plain,
% 3.10/1.01      ( ~ r1_tarski(X0,X1)
% 3.10/1.01      | ~ r1_tarski(X0,X2)
% 3.10/1.01      | r1_tarski(X0,k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2))) ),
% 3.10/1.01      inference(cnf_transformation,[],[f78]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_707,plain,
% 3.10/1.01      ( r1_tarski(X0,X1) != iProver_top
% 3.10/1.01      | r1_tarski(X0,X2) != iProver_top
% 3.10/1.01      | r1_tarski(X0,k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2))) = iProver_top ),
% 3.10/1.01      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_3171,plain,
% 3.10/1.01      ( r1_tarski(X0,X1) != iProver_top
% 3.10/1.01      | r1_tarski(X0,k10_relat_1(k7_relat_1(sK2,X1),X2)) = iProver_top
% 3.10/1.01      | r1_tarski(X0,k10_relat_1(sK2,X2)) != iProver_top ),
% 3.10/1.01      inference(superposition,[status(thm)],[c_1805,c_707]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_11,plain,
% 3.10/1.01      ( k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) ),
% 3.10/1.01      inference(cnf_transformation,[],[f79]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_7,plain,
% 3.10/1.01      ( r1_tarski(k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)),X0) ),
% 3.10/1.01      inference(cnf_transformation,[],[f77]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_708,plain,
% 3.10/1.01      ( r1_tarski(k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)),X0) = iProver_top ),
% 3.10/1.01      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_1072,plain,
% 3.10/1.01      ( r1_tarski(k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)),X1) = iProver_top ),
% 3.10/1.01      inference(superposition,[status(thm)],[c_11,c_708]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_2329,plain,
% 3.10/1.01      ( r1_tarski(k10_relat_1(k7_relat_1(sK2,X0),X1),k10_relat_1(sK2,X1)) = iProver_top ),
% 3.10/1.01      inference(superposition,[status(thm)],[c_1805,c_1072]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_3,plain,
% 3.10/1.01      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 3.10/1.01      inference(cnf_transformation,[],[f50]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_711,plain,
% 3.10/1.01      ( X0 = X1
% 3.10/1.01      | r1_tarski(X0,X1) != iProver_top
% 3.10/1.01      | r1_tarski(X1,X0) != iProver_top ),
% 3.10/1.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_2644,plain,
% 3.10/1.01      ( k10_relat_1(k7_relat_1(sK2,X0),X1) = k10_relat_1(sK2,X1)
% 3.10/1.01      | r1_tarski(k10_relat_1(sK2,X1),k10_relat_1(k7_relat_1(sK2,X0),X1)) != iProver_top ),
% 3.10/1.01      inference(superposition,[status(thm)],[c_2329,c_711]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_3811,plain,
% 3.10/1.01      ( k10_relat_1(k7_relat_1(sK2,X0),X1) = k10_relat_1(sK2,X1)
% 3.10/1.01      | r1_tarski(k10_relat_1(sK2,X1),X0) != iProver_top
% 3.10/1.01      | r1_tarski(k10_relat_1(sK2,X1),k10_relat_1(sK2,X1)) != iProver_top ),
% 3.10/1.01      inference(superposition,[status(thm)],[c_3171,c_2644]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_5,plain,
% 3.10/1.01      ( r1_tarski(X0,X0) ),
% 3.10/1.01      inference(cnf_transformation,[],[f82]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_710,plain,
% 3.10/1.01      ( r1_tarski(X0,X0) = iProver_top ),
% 3.10/1.01      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_7582,plain,
% 3.10/1.01      ( k10_relat_1(k7_relat_1(sK2,X0),X1) = k10_relat_1(sK2,X1)
% 3.10/1.01      | r1_tarski(k10_relat_1(sK2,X1),X0) != iProver_top ),
% 3.10/1.01      inference(forward_subsumption_resolution,
% 3.10/1.01                [status(thm)],
% 3.10/1.01                [c_3811,c_710]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_7588,plain,
% 3.10/1.01      ( k10_relat_1(k7_relat_1(sK2,sK3),sK4) = k10_relat_1(sK2,sK4) ),
% 3.10/1.01      inference(superposition,[status(thm)],[c_695,c_7582]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_322,plain,( X0 = X0 ),theory(equality) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_4898,plain,
% 3.10/1.01      ( k10_relat_1(sK2,sK4) = k10_relat_1(sK2,sK4) ),
% 3.10/1.01      inference(instantiation,[status(thm)],[c_322]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_323,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_933,plain,
% 3.10/1.01      ( k10_relat_1(k7_relat_1(sK2,sK3),sK4) != X0
% 3.10/1.01      | k10_relat_1(sK2,sK4) != X0
% 3.10/1.01      | k10_relat_1(sK2,sK4) = k10_relat_1(k7_relat_1(sK2,sK3),sK4) ),
% 3.10/1.01      inference(instantiation,[status(thm)],[c_323]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_1065,plain,
% 3.10/1.01      ( k10_relat_1(k7_relat_1(sK2,sK3),sK4) != k10_relat_1(X0,X1)
% 3.10/1.01      | k10_relat_1(sK2,sK4) != k10_relat_1(X0,X1)
% 3.10/1.01      | k10_relat_1(sK2,sK4) = k10_relat_1(k7_relat_1(sK2,sK3),sK4) ),
% 3.10/1.01      inference(instantiation,[status(thm)],[c_933]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_4897,plain,
% 3.10/1.01      ( k10_relat_1(k7_relat_1(sK2,sK3),sK4) != k10_relat_1(sK2,sK4)
% 3.10/1.01      | k10_relat_1(sK2,sK4) = k10_relat_1(k7_relat_1(sK2,sK3),sK4)
% 3.10/1.01      | k10_relat_1(sK2,sK4) != k10_relat_1(sK2,sK4) ),
% 3.10/1.01      inference(instantiation,[status(thm)],[c_1065]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_21,negated_conjecture,
% 3.10/1.01      ( k10_relat_1(sK2,sK4) != k10_relat_1(k7_relat_1(sK2,sK3),sK4) ),
% 3.10/1.01      inference(cnf_transformation,[],[f73]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(contradiction,plain,
% 3.10/1.01      ( $false ),
% 3.10/1.01      inference(minisat,[status(thm)],[c_7588,c_4898,c_4897,c_21]) ).
% 3.10/1.01  
% 3.10/1.01  
% 3.10/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.10/1.01  
% 3.10/1.01  ------                               Statistics
% 3.10/1.01  
% 3.10/1.01  ------ Selected
% 3.10/1.01  
% 3.10/1.01  total_time:                             0.342
% 3.10/1.01  
%------------------------------------------------------------------------------
