%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:38:22 EST 2020

% Result     : Theorem 15.03s
% Output     : CNFRefutation 15.03s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 129 expanded)
%              Number of clauses        :   24 (  29 expanded)
%              Number of leaves         :   14 (  43 expanded)
%              Depth                    :   12
%              Number of atoms          :  154 ( 307 expanded)
%              Number of equality atoms :   91 ( 202 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(k3_tarski(k2_tarski(X2,X1)),k3_xboole_0(k3_tarski(k2_tarski(X2,X1)),X0)) = k3_tarski(k2_tarski(k5_xboole_0(X2,k3_xboole_0(X2,X0)),X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f27,f33,f24,f24,f33])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( X0 != X1
     => k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X0)) = k4_xboole_0(k2_xboole_0(X2,k1_tarski(X0)),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( X0 != X1
       => k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X0)) = k4_xboole_0(k2_xboole_0(X2,k1_tarski(X0)),k1_tarski(X1)) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X0)) != k4_xboole_0(k2_xboole_0(X2,k1_tarski(X0)),k1_tarski(X1))
      & X0 != X1 ) ),
    inference(ennf_transformation,[],[f11])).

fof(f21,plain,
    ( ? [X0,X1,X2] :
        ( k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X0)) != k4_xboole_0(k2_xboole_0(X2,k1_tarski(X0)),k1_tarski(X1))
        & X0 != X1 )
   => ( k2_xboole_0(k4_xboole_0(sK3,k1_tarski(sK2)),k1_tarski(sK1)) != k4_xboole_0(k2_xboole_0(sK3,k1_tarski(sK1)),k1_tarski(sK2))
      & sK1 != sK2 ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( k2_xboole_0(k4_xboole_0(sK3,k1_tarski(sK2)),k1_tarski(sK1)) != k4_xboole_0(k2_xboole_0(sK3,k1_tarski(sK1)),k1_tarski(sK2))
    & sK1 != sK2 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f16,f21])).

fof(f36,plain,(
    k2_xboole_0(k4_xboole_0(sK3,k1_tarski(sK2)),k1_tarski(sK1)) != k4_xboole_0(k2_xboole_0(sK3,k1_tarski(sK1)),k1_tarski(sK2)) ),
    inference(cnf_transformation,[],[f22])).

fof(f7,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f46,plain,(
    k5_xboole_0(k3_tarski(k2_tarski(sK3,k2_tarski(sK1,sK1))),k3_xboole_0(k3_tarski(k2_tarski(sK3,k2_tarski(sK1,sK1))),k2_tarski(sK2,sK2))) != k3_tarski(k2_tarski(k5_xboole_0(sK3,k3_xboole_0(sK3,k2_tarski(sK2,sK2))),k2_tarski(sK1,sK1))) ),
    inference(definition_unfolding,[],[f36,f33,f24,f32,f32,f24,f33,f32,f32])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f38,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) ),
    inference(definition_unfolding,[],[f25,f24,f24,f33])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => k4_xboole_0(k2_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k2_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k2_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(k3_tarski(k2_tarski(X1,k2_tarski(X0,X0))),k3_xboole_0(k3_tarski(k2_tarski(X1,k2_tarski(X0,X0))),k2_tarski(X0,X0))) = X1
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f34,f24,f33,f32,f32])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f17])).

fof(f19,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK0(X0,X1) != X0
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( sK0(X0,X1) = X0
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK0(X0,X1) != X0
            | ~ r2_hidden(sK0(X0,X1),X1) )
          & ( sK0(X0,X1) = X0
            | r2_hidden(sK0(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f19])).

fof(f28,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f44,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_tarski(X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f28,f32])).

fof(f49,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k2_tarski(X0,X0)) ) ),
    inference(equality_resolution,[],[f44])).

fof(f29,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f43,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k2_tarski(X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f29,f32])).

fof(f47,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k2_tarski(X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f43])).

fof(f48,plain,(
    ! [X3] : r2_hidden(X3,k2_tarski(X3,X3)) ),
    inference(equality_resolution,[],[f47])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
     => r1_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f4])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(ennf_transformation,[],[f12])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X0 ) ),
    inference(definition_unfolding,[],[f26,f24])).

fof(f35,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f22])).

cnf(c_3,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k5_xboole_0(k3_tarski(k2_tarski(X2,X1)),k3_xboole_0(k3_tarski(k2_tarski(X2,X1)),X0)) = k3_tarski(k2_tarski(k5_xboole_0(X2,k3_xboole_0(X2,X0)),X1)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_9,negated_conjecture,
    ( k5_xboole_0(k3_tarski(k2_tarski(sK3,k2_tarski(sK1,sK1))),k3_xboole_0(k3_tarski(k2_tarski(sK3,k2_tarski(sK1,sK1))),k2_tarski(sK2,sK2))) != k3_tarski(k2_tarski(k5_xboole_0(sK3,k3_xboole_0(sK3,k2_tarski(sK2,sK2))),k2_tarski(sK1,sK1))) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_48470,plain,
    ( ~ r1_xboole_0(k2_tarski(sK2,sK2),k2_tarski(sK1,sK1)) ),
    inference(resolution,[status(thm)],[c_3,c_9])).

cnf(c_1,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_175,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_174,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_537,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_175,c_174])).

cnf(c_794,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) ),
    inference(resolution,[status(thm)],[c_1,c_537])).

cnf(c_180,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_786,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_180,c_174])).

cnf(c_11948,plain,
    ( r2_hidden(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2)
    | ~ r2_hidden(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)),X2) ),
    inference(resolution,[status(thm)],[c_794,c_786])).

cnf(c_8,plain,
    ( r2_hidden(X0,X1)
    | k5_xboole_0(k3_tarski(k2_tarski(X1,k2_tarski(X0,X0))),k3_xboole_0(k3_tarski(k2_tarski(X1,k2_tarski(X0,X0))),k2_tarski(X0,X0))) = X1 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_2357,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X0)
    | r2_hidden(k5_xboole_0(k3_tarski(k2_tarski(X0,k2_tarski(X2,X2))),k3_xboole_0(k3_tarski(k2_tarski(X0,k2_tarski(X2,X2))),k2_tarski(X2,X2))),X1) ),
    inference(resolution,[status(thm)],[c_8,c_786])).

cnf(c_46677,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X0)
    | r2_hidden(k5_xboole_0(X0,k3_xboole_0(X0,k2_tarski(X2,X2))),X1) ),
    inference(resolution,[status(thm)],[c_11948,c_2357])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,k2_tarski(X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_46701,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X1,k2_tarski(X2,X2))
    | k5_xboole_0(X1,k3_xboole_0(X1,k2_tarski(X0,X0))) = X2 ),
    inference(resolution,[status(thm)],[c_46677,c_7])).

cnf(c_6,plain,
    ( r2_hidden(X0,k2_tarski(X0,X0)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_46785,plain,
    ( r2_hidden(X0,X1)
    | k5_xboole_0(X1,k3_xboole_0(X1,k2_tarski(X0,X0))) = X1 ),
    inference(resolution,[status(thm)],[c_46701,c_6])).

cnf(c_2,plain,
    ( r1_xboole_0(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_47058,plain,
    ( r2_hidden(X0,X1)
    | r1_xboole_0(X1,k2_tarski(X0,X0)) ),
    inference(resolution,[status(thm)],[c_46785,c_2])).

cnf(c_48702,plain,
    ( r2_hidden(sK1,k2_tarski(sK2,sK2)) ),
    inference(resolution,[status(thm)],[c_48470,c_47058])).

cnf(c_387,plain,
    ( ~ r2_hidden(sK1,k2_tarski(sK2,sK2))
    | sK1 = sK2 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_10,negated_conjecture,
    ( sK1 != sK2 ),
    inference(cnf_transformation,[],[f35])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_48702,c_387,c_10])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:52:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 15.03/2.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.03/2.50  
% 15.03/2.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.03/2.50  
% 15.03/2.50  ------  iProver source info
% 15.03/2.50  
% 15.03/2.50  git: date: 2020-06-30 10:37:57 +0100
% 15.03/2.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.03/2.50  git: non_committed_changes: false
% 15.03/2.50  git: last_make_outside_of_git: false
% 15.03/2.50  
% 15.03/2.50  ------ 
% 15.03/2.50  ------ Parsing...
% 15.03/2.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.03/2.50  
% 15.03/2.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 15.03/2.50  
% 15.03/2.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.03/2.50  
% 15.03/2.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.03/2.50  ------ Proving...
% 15.03/2.50  ------ Problem Properties 
% 15.03/2.50  
% 15.03/2.50  
% 15.03/2.50  clauses                                 11
% 15.03/2.50  conjectures                             2
% 15.03/2.50  EPR                                     1
% 15.03/2.50  Horn                                    9
% 15.03/2.50  unary                                   5
% 15.03/2.50  binary                                  4
% 15.03/2.50  lits                                    19
% 15.03/2.50  lits eq                                 12
% 15.03/2.50  fd_pure                                 0
% 15.03/2.50  fd_pseudo                               0
% 15.03/2.50  fd_cond                                 0
% 15.03/2.50  fd_pseudo_cond                          2
% 15.03/2.50  AC symbols                              0
% 15.03/2.50  
% 15.03/2.50  ------ Input Options Time Limit: Unbounded
% 15.03/2.50  
% 15.03/2.50  
% 15.03/2.50  ------ 
% 15.03/2.50  Current options:
% 15.03/2.50  ------ 
% 15.03/2.50  
% 15.03/2.50  
% 15.03/2.50  
% 15.03/2.50  
% 15.03/2.50  ------ Proving...
% 15.03/2.50  
% 15.03/2.50  
% 15.03/2.50  % SZS status Theorem for theBenchmark.p
% 15.03/2.50  
% 15.03/2.50  % SZS output start CNFRefutation for theBenchmark.p
% 15.03/2.50  
% 15.03/2.50  fof(f5,axiom,(
% 15.03/2.50    ! [X0,X1,X2] : (r1_xboole_0(X0,X1) => k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0))),
% 15.03/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.03/2.50  
% 15.03/2.50  fof(f14,plain,(
% 15.03/2.50    ! [X0,X1,X2] : (k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0) | ~r1_xboole_0(X0,X1))),
% 15.03/2.50    inference(ennf_transformation,[],[f5])).
% 15.03/2.50  
% 15.03/2.50  fof(f27,plain,(
% 15.03/2.50    ( ! [X2,X0,X1] : (k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0) | ~r1_xboole_0(X0,X1)) )),
% 15.03/2.50    inference(cnf_transformation,[],[f14])).
% 15.03/2.50  
% 15.03/2.50  fof(f2,axiom,(
% 15.03/2.50    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 15.03/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.03/2.50  
% 15.03/2.50  fof(f24,plain,(
% 15.03/2.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 15.03/2.50    inference(cnf_transformation,[],[f2])).
% 15.03/2.50  
% 15.03/2.50  fof(f8,axiom,(
% 15.03/2.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 15.03/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.03/2.50  
% 15.03/2.50  fof(f33,plain,(
% 15.03/2.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 15.03/2.50    inference(cnf_transformation,[],[f8])).
% 15.03/2.50  
% 15.03/2.50  fof(f40,plain,(
% 15.03/2.50    ( ! [X2,X0,X1] : (k5_xboole_0(k3_tarski(k2_tarski(X2,X1)),k3_xboole_0(k3_tarski(k2_tarski(X2,X1)),X0)) = k3_tarski(k2_tarski(k5_xboole_0(X2,k3_xboole_0(X2,X0)),X1)) | ~r1_xboole_0(X0,X1)) )),
% 15.03/2.50    inference(definition_unfolding,[],[f27,f33,f24,f24,f33])).
% 15.03/2.50  
% 15.03/2.50  fof(f10,conjecture,(
% 15.03/2.50    ! [X0,X1,X2] : (X0 != X1 => k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X0)) = k4_xboole_0(k2_xboole_0(X2,k1_tarski(X0)),k1_tarski(X1)))),
% 15.03/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.03/2.50  
% 15.03/2.50  fof(f11,negated_conjecture,(
% 15.03/2.50    ~! [X0,X1,X2] : (X0 != X1 => k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X0)) = k4_xboole_0(k2_xboole_0(X2,k1_tarski(X0)),k1_tarski(X1)))),
% 15.03/2.50    inference(negated_conjecture,[],[f10])).
% 15.03/2.50  
% 15.03/2.50  fof(f16,plain,(
% 15.03/2.50    ? [X0,X1,X2] : (k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X0)) != k4_xboole_0(k2_xboole_0(X2,k1_tarski(X0)),k1_tarski(X1)) & X0 != X1)),
% 15.03/2.50    inference(ennf_transformation,[],[f11])).
% 15.03/2.50  
% 15.03/2.50  fof(f21,plain,(
% 15.03/2.50    ? [X0,X1,X2] : (k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X0)) != k4_xboole_0(k2_xboole_0(X2,k1_tarski(X0)),k1_tarski(X1)) & X0 != X1) => (k2_xboole_0(k4_xboole_0(sK3,k1_tarski(sK2)),k1_tarski(sK1)) != k4_xboole_0(k2_xboole_0(sK3,k1_tarski(sK1)),k1_tarski(sK2)) & sK1 != sK2)),
% 15.03/2.50    introduced(choice_axiom,[])).
% 15.03/2.50  
% 15.03/2.50  fof(f22,plain,(
% 15.03/2.50    k2_xboole_0(k4_xboole_0(sK3,k1_tarski(sK2)),k1_tarski(sK1)) != k4_xboole_0(k2_xboole_0(sK3,k1_tarski(sK1)),k1_tarski(sK2)) & sK1 != sK2),
% 15.03/2.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f16,f21])).
% 15.03/2.50  
% 15.03/2.50  fof(f36,plain,(
% 15.03/2.50    k2_xboole_0(k4_xboole_0(sK3,k1_tarski(sK2)),k1_tarski(sK1)) != k4_xboole_0(k2_xboole_0(sK3,k1_tarski(sK1)),k1_tarski(sK2))),
% 15.03/2.50    inference(cnf_transformation,[],[f22])).
% 15.03/2.50  
% 15.03/2.50  fof(f7,axiom,(
% 15.03/2.50    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 15.03/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.03/2.50  
% 15.03/2.50  fof(f32,plain,(
% 15.03/2.50    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 15.03/2.50    inference(cnf_transformation,[],[f7])).
% 15.03/2.50  
% 15.03/2.50  fof(f46,plain,(
% 15.03/2.50    k5_xboole_0(k3_tarski(k2_tarski(sK3,k2_tarski(sK1,sK1))),k3_xboole_0(k3_tarski(k2_tarski(sK3,k2_tarski(sK1,sK1))),k2_tarski(sK2,sK2))) != k3_tarski(k2_tarski(k5_xboole_0(sK3,k3_xboole_0(sK3,k2_tarski(sK2,sK2))),k2_tarski(sK1,sK1)))),
% 15.03/2.50    inference(definition_unfolding,[],[f36,f33,f24,f32,f32,f24,f33,f32,f32])).
% 15.03/2.50  
% 15.03/2.50  fof(f3,axiom,(
% 15.03/2.50    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 15.03/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.03/2.50  
% 15.03/2.50  fof(f25,plain,(
% 15.03/2.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 15.03/2.50    inference(cnf_transformation,[],[f3])).
% 15.03/2.50  
% 15.03/2.50  fof(f38,plain,(
% 15.03/2.50    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1))) )),
% 15.03/2.50    inference(definition_unfolding,[],[f25,f24,f24,f33])).
% 15.03/2.50  
% 15.03/2.50  fof(f9,axiom,(
% 15.03/2.50    ! [X0,X1] : (~r2_hidden(X0,X1) => k4_xboole_0(k2_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1)),
% 15.03/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.03/2.50  
% 15.03/2.50  fof(f15,plain,(
% 15.03/2.50    ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 | r2_hidden(X0,X1))),
% 15.03/2.50    inference(ennf_transformation,[],[f9])).
% 15.03/2.50  
% 15.03/2.50  fof(f34,plain,(
% 15.03/2.50    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 | r2_hidden(X0,X1)) )),
% 15.03/2.50    inference(cnf_transformation,[],[f15])).
% 15.03/2.50  
% 15.03/2.50  fof(f45,plain,(
% 15.03/2.50    ( ! [X0,X1] : (k5_xboole_0(k3_tarski(k2_tarski(X1,k2_tarski(X0,X0))),k3_xboole_0(k3_tarski(k2_tarski(X1,k2_tarski(X0,X0))),k2_tarski(X0,X0))) = X1 | r2_hidden(X0,X1)) )),
% 15.03/2.50    inference(definition_unfolding,[],[f34,f24,f33,f32,f32])).
% 15.03/2.50  
% 15.03/2.50  fof(f6,axiom,(
% 15.03/2.50    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 15.03/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.03/2.50  
% 15.03/2.50  fof(f17,plain,(
% 15.03/2.50    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 15.03/2.50    inference(nnf_transformation,[],[f6])).
% 15.03/2.50  
% 15.03/2.50  fof(f18,plain,(
% 15.03/2.50    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 15.03/2.50    inference(rectify,[],[f17])).
% 15.03/2.50  
% 15.03/2.50  fof(f19,plain,(
% 15.03/2.50    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK0(X0,X1) != X0 | ~r2_hidden(sK0(X0,X1),X1)) & (sK0(X0,X1) = X0 | r2_hidden(sK0(X0,X1),X1))))),
% 15.03/2.50    introduced(choice_axiom,[])).
% 15.03/2.50  
% 15.03/2.50  fof(f20,plain,(
% 15.03/2.50    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK0(X0,X1) != X0 | ~r2_hidden(sK0(X0,X1),X1)) & (sK0(X0,X1) = X0 | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 15.03/2.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f19])).
% 15.03/2.50  
% 15.03/2.50  fof(f28,plain,(
% 15.03/2.50    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 15.03/2.50    inference(cnf_transformation,[],[f20])).
% 15.03/2.50  
% 15.03/2.50  fof(f44,plain,(
% 15.03/2.50    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_tarski(X0,X0) != X1) )),
% 15.03/2.50    inference(definition_unfolding,[],[f28,f32])).
% 15.03/2.50  
% 15.03/2.50  fof(f49,plain,(
% 15.03/2.50    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k2_tarski(X0,X0))) )),
% 15.03/2.50    inference(equality_resolution,[],[f44])).
% 15.03/2.50  
% 15.03/2.50  fof(f29,plain,(
% 15.03/2.50    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 15.03/2.50    inference(cnf_transformation,[],[f20])).
% 15.03/2.50  
% 15.03/2.50  fof(f43,plain,(
% 15.03/2.50    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k2_tarski(X0,X0) != X1) )),
% 15.03/2.50    inference(definition_unfolding,[],[f29,f32])).
% 15.03/2.50  
% 15.03/2.50  fof(f47,plain,(
% 15.03/2.50    ( ! [X3,X1] : (r2_hidden(X3,X1) | k2_tarski(X3,X3) != X1) )),
% 15.03/2.50    inference(equality_resolution,[],[f43])).
% 15.03/2.50  
% 15.03/2.50  fof(f48,plain,(
% 15.03/2.50    ( ! [X3] : (r2_hidden(X3,k2_tarski(X3,X3))) )),
% 15.03/2.50    inference(equality_resolution,[],[f47])).
% 15.03/2.50  
% 15.03/2.50  fof(f4,axiom,(
% 15.03/2.50    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 15.03/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.03/2.50  
% 15.03/2.50  fof(f12,plain,(
% 15.03/2.50    ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 => r1_xboole_0(X0,X1))),
% 15.03/2.50    inference(unused_predicate_definition_removal,[],[f4])).
% 15.03/2.50  
% 15.03/2.50  fof(f13,plain,(
% 15.03/2.50    ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0)),
% 15.03/2.50    inference(ennf_transformation,[],[f12])).
% 15.03/2.50  
% 15.03/2.50  fof(f26,plain,(
% 15.03/2.50    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 15.03/2.50    inference(cnf_transformation,[],[f13])).
% 15.03/2.50  
% 15.03/2.50  fof(f39,plain,(
% 15.03/2.50    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X0) )),
% 15.03/2.50    inference(definition_unfolding,[],[f26,f24])).
% 15.03/2.50  
% 15.03/2.50  fof(f35,plain,(
% 15.03/2.50    sK1 != sK2),
% 15.03/2.50    inference(cnf_transformation,[],[f22])).
% 15.03/2.50  
% 15.03/2.50  cnf(c_3,plain,
% 15.03/2.50      ( ~ r1_xboole_0(X0,X1)
% 15.03/2.50      | k5_xboole_0(k3_tarski(k2_tarski(X2,X1)),k3_xboole_0(k3_tarski(k2_tarski(X2,X1)),X0)) = k3_tarski(k2_tarski(k5_xboole_0(X2,k3_xboole_0(X2,X0)),X1)) ),
% 15.03/2.50      inference(cnf_transformation,[],[f40]) ).
% 15.03/2.50  
% 15.03/2.50  cnf(c_9,negated_conjecture,
% 15.03/2.50      ( k5_xboole_0(k3_tarski(k2_tarski(sK3,k2_tarski(sK1,sK1))),k3_xboole_0(k3_tarski(k2_tarski(sK3,k2_tarski(sK1,sK1))),k2_tarski(sK2,sK2))) != k3_tarski(k2_tarski(k5_xboole_0(sK3,k3_xboole_0(sK3,k2_tarski(sK2,sK2))),k2_tarski(sK1,sK1))) ),
% 15.03/2.50      inference(cnf_transformation,[],[f46]) ).
% 15.03/2.50  
% 15.03/2.50  cnf(c_48470,plain,
% 15.03/2.50      ( ~ r1_xboole_0(k2_tarski(sK2,sK2),k2_tarski(sK1,sK1)) ),
% 15.03/2.50      inference(resolution,[status(thm)],[c_3,c_9]) ).
% 15.03/2.50  
% 15.03/2.50  cnf(c_1,plain,
% 15.03/2.50      ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
% 15.03/2.50      inference(cnf_transformation,[],[f38]) ).
% 15.03/2.50  
% 15.03/2.50  cnf(c_175,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 15.03/2.50  
% 15.03/2.50  cnf(c_174,plain,( X0 = X0 ),theory(equality) ).
% 15.03/2.50  
% 15.03/2.50  cnf(c_537,plain,
% 15.03/2.50      ( X0 != X1 | X1 = X0 ),
% 15.03/2.50      inference(resolution,[status(thm)],[c_175,c_174]) ).
% 15.03/2.50  
% 15.03/2.50  cnf(c_794,plain,
% 15.03/2.50      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) ),
% 15.03/2.50      inference(resolution,[status(thm)],[c_1,c_537]) ).
% 15.03/2.50  
% 15.03/2.50  cnf(c_180,plain,
% 15.03/2.50      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 15.03/2.50      theory(equality) ).
% 15.03/2.50  
% 15.03/2.50  cnf(c_786,plain,
% 15.03/2.50      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X1) | X2 != X0 ),
% 15.03/2.50      inference(resolution,[status(thm)],[c_180,c_174]) ).
% 15.03/2.50  
% 15.03/2.50  cnf(c_11948,plain,
% 15.03/2.50      ( r2_hidden(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2)
% 15.03/2.50      | ~ r2_hidden(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)),X2) ),
% 15.03/2.50      inference(resolution,[status(thm)],[c_794,c_786]) ).
% 15.03/2.50  
% 15.03/2.50  cnf(c_8,plain,
% 15.03/2.50      ( r2_hidden(X0,X1)
% 15.03/2.50      | k5_xboole_0(k3_tarski(k2_tarski(X1,k2_tarski(X0,X0))),k3_xboole_0(k3_tarski(k2_tarski(X1,k2_tarski(X0,X0))),k2_tarski(X0,X0))) = X1 ),
% 15.03/2.50      inference(cnf_transformation,[],[f45]) ).
% 15.03/2.50  
% 15.03/2.50  cnf(c_2357,plain,
% 15.03/2.50      ( ~ r2_hidden(X0,X1)
% 15.03/2.50      | r2_hidden(X2,X0)
% 15.03/2.50      | r2_hidden(k5_xboole_0(k3_tarski(k2_tarski(X0,k2_tarski(X2,X2))),k3_xboole_0(k3_tarski(k2_tarski(X0,k2_tarski(X2,X2))),k2_tarski(X2,X2))),X1) ),
% 15.03/2.50      inference(resolution,[status(thm)],[c_8,c_786]) ).
% 15.03/2.50  
% 15.03/2.50  cnf(c_46677,plain,
% 15.03/2.50      ( ~ r2_hidden(X0,X1)
% 15.03/2.50      | r2_hidden(X2,X0)
% 15.03/2.50      | r2_hidden(k5_xboole_0(X0,k3_xboole_0(X0,k2_tarski(X2,X2))),X1) ),
% 15.03/2.50      inference(resolution,[status(thm)],[c_11948,c_2357]) ).
% 15.03/2.50  
% 15.03/2.50  cnf(c_7,plain,
% 15.03/2.50      ( ~ r2_hidden(X0,k2_tarski(X1,X1)) | X0 = X1 ),
% 15.03/2.50      inference(cnf_transformation,[],[f49]) ).
% 15.03/2.50  
% 15.03/2.50  cnf(c_46701,plain,
% 15.03/2.50      ( r2_hidden(X0,X1)
% 15.03/2.50      | ~ r2_hidden(X1,k2_tarski(X2,X2))
% 15.03/2.50      | k5_xboole_0(X1,k3_xboole_0(X1,k2_tarski(X0,X0))) = X2 ),
% 15.03/2.50      inference(resolution,[status(thm)],[c_46677,c_7]) ).
% 15.03/2.50  
% 15.03/2.50  cnf(c_6,plain,
% 15.03/2.50      ( r2_hidden(X0,k2_tarski(X0,X0)) ),
% 15.03/2.50      inference(cnf_transformation,[],[f48]) ).
% 15.03/2.50  
% 15.03/2.50  cnf(c_46785,plain,
% 15.03/2.50      ( r2_hidden(X0,X1)
% 15.03/2.50      | k5_xboole_0(X1,k3_xboole_0(X1,k2_tarski(X0,X0))) = X1 ),
% 15.03/2.50      inference(resolution,[status(thm)],[c_46701,c_6]) ).
% 15.03/2.50  
% 15.03/2.50  cnf(c_2,plain,
% 15.03/2.50      ( r1_xboole_0(X0,X1) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X0 ),
% 15.03/2.50      inference(cnf_transformation,[],[f39]) ).
% 15.03/2.50  
% 15.03/2.50  cnf(c_47058,plain,
% 15.03/2.50      ( r2_hidden(X0,X1) | r1_xboole_0(X1,k2_tarski(X0,X0)) ),
% 15.03/2.50      inference(resolution,[status(thm)],[c_46785,c_2]) ).
% 15.03/2.50  
% 15.03/2.50  cnf(c_48702,plain,
% 15.03/2.50      ( r2_hidden(sK1,k2_tarski(sK2,sK2)) ),
% 15.03/2.50      inference(resolution,[status(thm)],[c_48470,c_47058]) ).
% 15.03/2.50  
% 15.03/2.50  cnf(c_387,plain,
% 15.03/2.50      ( ~ r2_hidden(sK1,k2_tarski(sK2,sK2)) | sK1 = sK2 ),
% 15.03/2.50      inference(instantiation,[status(thm)],[c_7]) ).
% 15.03/2.50  
% 15.03/2.50  cnf(c_10,negated_conjecture,
% 15.03/2.50      ( sK1 != sK2 ),
% 15.03/2.50      inference(cnf_transformation,[],[f35]) ).
% 15.03/2.50  
% 15.03/2.50  cnf(contradiction,plain,
% 15.03/2.50      ( $false ),
% 15.03/2.50      inference(minisat,[status(thm)],[c_48702,c_387,c_10]) ).
% 15.03/2.50  
% 15.03/2.50  
% 15.03/2.50  % SZS output end CNFRefutation for theBenchmark.p
% 15.03/2.50  
% 15.03/2.50  ------                               Statistics
% 15.03/2.50  
% 15.03/2.50  ------ Selected
% 15.03/2.50  
% 15.03/2.50  total_time:                             1.768
% 15.03/2.50  
%------------------------------------------------------------------------------
