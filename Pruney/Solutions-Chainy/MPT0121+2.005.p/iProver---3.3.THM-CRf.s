%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:26:10 EST 2020

% Result     : Theorem 11.23s
% Output     : CNFRefutation 11.23s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 329 expanded)
%              Number of clauses        :   39 ( 125 expanded)
%              Number of leaves         :   11 (  82 expanded)
%              Depth                    :   19
%              Number of atoms          :  153 ( 713 expanded)
%              Number of equality atoms :   17 ( 106 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X1,X2)))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f27,f23,f23])).

fof(f7,axiom,(
    ! [X0,X1] :
      ~ ( r1_xboole_0(k3_xboole_0(X0,X1),X1)
        & ~ r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k3_xboole_0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k3_xboole_0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f26,f23])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f32,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f20,f23,f23])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f12])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f9,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X3)
        & r1_xboole_0(X1,X3)
        & r1_xboole_0(X0,X3) )
     => r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X2,X3)
          & r1_xboole_0(X1,X3)
          & r1_xboole_0(X0,X3) )
       => r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f16,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3)
      & r1_xboole_0(X2,X3)
      & r1_xboole_0(X1,X3)
      & r1_xboole_0(X0,X3) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f17,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3)
      & r1_xboole_0(X2,X3)
      & r1_xboole_0(X1,X3)
      & r1_xboole_0(X0,X3) ) ),
    inference(flattening,[],[f16])).

fof(f18,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3)
        & r1_xboole_0(X2,X3)
        & r1_xboole_0(X1,X3)
        & r1_xboole_0(X0,X3) )
   => ( ~ r1_xboole_0(k2_xboole_0(k2_xboole_0(sK0,sK1),sK2),sK3)
      & r1_xboole_0(sK2,sK3)
      & r1_xboole_0(sK1,sK3)
      & r1_xboole_0(sK0,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ~ r1_xboole_0(k2_xboole_0(k2_xboole_0(sK0,sK1),sK2),sK3)
    & r1_xboole_0(sK2,sK3)
    & r1_xboole_0(sK1,sK3)
    & r1_xboole_0(sK0,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f17,f18])).

fof(f31,plain,(
    ~ r1_xboole_0(k2_xboole_0(k2_xboole_0(sK0,sK1),sK2),sK3) ),
    inference(cnf_transformation,[],[f19])).

fof(f30,plain,(
    r1_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f19])).

fof(f29,plain,(
    r1_xboole_0(sK1,sK3) ),
    inference(cnf_transformation,[],[f19])).

fof(f28,plain,(
    r1_xboole_0(sK0,sK3) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_6,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X1,X2))) = k4_xboole_0(X0,k4_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_178,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_175,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1284,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_178,c_175])).

cnf(c_2343,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X2)),X3)
    | r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X1,X2))),X3) ),
    inference(resolution,[status(thm)],[c_6,c_1284])).

cnf(c_5,plain,
    ( r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_14915,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X0,k2_xboole_0(X1,X2))
    | ~ r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    inference(resolution,[status(thm)],[c_2343,c_5])).

cnf(c_0,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_1296,plain,
    ( ~ r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)
    | r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
    inference(resolution,[status(thm)],[c_1284,c_0])).

cnf(c_2,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_xboole_0(X1,X2)
    | r1_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_101,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X1)
    | X0 != X3
    | k4_xboole_0(X3,X4) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_4])).

cnf(c_102,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(k4_xboole_0(X0,X2),X1) ),
    inference(unflattening,[status(thm)],[c_101])).

cnf(c_1411,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X0)),X1) ),
    inference(resolution,[status(thm)],[c_1296,c_102])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_570,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,k4_xboole_0(X0,X2)) ),
    inference(resolution,[status(thm)],[c_102,c_1])).

cnf(c_704,plain,
    ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
    | ~ r1_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))) ),
    inference(resolution,[status(thm)],[c_5,c_570])).

cnf(c_857,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(resolution,[status(thm)],[c_704,c_570])).

cnf(c_867,plain,
    ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
    | ~ r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))),X1) ),
    inference(resolution,[status(thm)],[c_857,c_5])).

cnf(c_1437,plain,
    ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
    | ~ r1_xboole_0(k4_xboole_0(X1,X2),X1) ),
    inference(resolution,[status(thm)],[c_1411,c_867])).

cnf(c_865,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(k4_xboole_0(X1,X2),X0) ),
    inference(resolution,[status(thm)],[c_857,c_1])).

cnf(c_1421,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X1)),X0) ),
    inference(resolution,[status(thm)],[c_1296,c_865])).

cnf(c_1936,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(resolution,[status(thm)],[c_1437,c_1421])).

cnf(c_2321,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(resolution,[status(thm)],[c_1936,c_1])).

cnf(c_35923,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(X0,X2)
    | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(resolution,[status(thm)],[c_14915,c_2321])).

cnf(c_37168,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(X0,X2)
    | r1_xboole_0(k2_xboole_0(X1,X2),X0) ),
    inference(resolution,[status(thm)],[c_35923,c_1])).

cnf(c_7,negated_conjecture,
    ( ~ r1_xboole_0(k2_xboole_0(k2_xboole_0(sK0,sK1),sK2),sK3) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_38200,plain,
    ( ~ r1_xboole_0(sK3,k2_xboole_0(sK0,sK1))
    | ~ r1_xboole_0(sK3,sK2) ),
    inference(resolution,[status(thm)],[c_37168,c_7])).

cnf(c_8,negated_conjecture,
    ( r1_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_395,plain,
    ( r1_xboole_0(sK3,sK2)
    | ~ r1_xboole_0(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_38920,plain,
    ( ~ r1_xboole_0(sK3,k2_xboole_0(sK0,sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_38200,c_8,c_395])).

cnf(c_1932,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(resolution,[status(thm)],[c_1437,c_1411])).

cnf(c_2298,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
    inference(resolution,[status(thm)],[c_1932,c_1])).

cnf(c_35941,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(X2,X0)
    | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(resolution,[status(thm)],[c_14915,c_2298])).

cnf(c_38933,plain,
    ( ~ r1_xboole_0(sK3,sK0)
    | ~ r1_xboole_0(sK1,sK3) ),
    inference(resolution,[status(thm)],[c_38920,c_35941])).

cnf(c_401,plain,
    ( r1_xboole_0(sK3,sK0)
    | ~ r1_xboole_0(sK0,sK3) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_9,negated_conjecture,
    ( r1_xboole_0(sK1,sK3) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_10,negated_conjecture,
    ( r1_xboole_0(sK0,sK3) ),
    inference(cnf_transformation,[],[f28])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_38933,c_401,c_9,c_10])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:13:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 11.23/1.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.23/1.99  
% 11.23/1.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.23/1.99  
% 11.23/1.99  ------  iProver source info
% 11.23/1.99  
% 11.23/1.99  git: date: 2020-06-30 10:37:57 +0100
% 11.23/1.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.23/1.99  git: non_committed_changes: false
% 11.23/1.99  git: last_make_outside_of_git: false
% 11.23/1.99  
% 11.23/1.99  ------ 
% 11.23/1.99  ------ Parsing...
% 11.23/1.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.23/1.99  
% 11.23/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 11.23/1.99  
% 11.23/1.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.23/1.99  
% 11.23/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.23/1.99  ------ Proving...
% 11.23/1.99  ------ Problem Properties 
% 11.23/1.99  
% 11.23/1.99  
% 11.23/1.99  clauses                                 10
% 11.23/1.99  conjectures                             4
% 11.23/1.99  EPR                                     4
% 11.23/1.99  Horn                                    10
% 11.23/1.99  unary                                   6
% 11.23/1.99  binary                                  4
% 11.23/1.99  lits                                    14
% 11.23/1.99  lits eq                                 3
% 11.23/1.99  fd_pure                                 0
% 11.23/1.99  fd_pseudo                               0
% 11.23/1.99  fd_cond                                 0
% 11.23/1.99  fd_pseudo_cond                          0
% 11.23/1.99  AC symbols                              0
% 11.23/1.99  
% 11.23/1.99  ------ Input Options Time Limit: Unbounded
% 11.23/1.99  
% 11.23/1.99  
% 11.23/1.99  ------ 
% 11.23/1.99  Current options:
% 11.23/1.99  ------ 
% 11.23/1.99  
% 11.23/1.99  
% 11.23/1.99  
% 11.23/1.99  
% 11.23/1.99  ------ Proving...
% 11.23/1.99  
% 11.23/1.99  
% 11.23/1.99  % SZS status Theorem for theBenchmark.p
% 11.23/1.99  
% 11.23/1.99  % SZS output start CNFRefutation for theBenchmark.p
% 11.23/1.99  
% 11.23/1.99  fof(f8,axiom,(
% 11.23/1.99    ! [X0,X1,X2] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X1,X2)))),
% 11.23/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.23/1.99  
% 11.23/1.99  fof(f15,plain,(
% 11.23/1.99    ! [X0,X1,X2] : (k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X1))),
% 11.23/1.99    inference(ennf_transformation,[],[f8])).
% 11.23/1.99  
% 11.23/1.99  fof(f27,plain,(
% 11.23/1.99    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X1)) )),
% 11.23/1.99    inference(cnf_transformation,[],[f15])).
% 11.23/1.99  
% 11.23/1.99  fof(f4,axiom,(
% 11.23/1.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 11.23/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.23/1.99  
% 11.23/1.99  fof(f23,plain,(
% 11.23/1.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 11.23/1.99    inference(cnf_transformation,[],[f4])).
% 11.23/1.99  
% 11.23/1.99  fof(f34,plain,(
% 11.23/1.99    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X1,X2))) | ~r1_xboole_0(X0,X1)) )),
% 11.23/1.99    inference(definition_unfolding,[],[f27,f23,f23])).
% 11.23/1.99  
% 11.23/1.99  fof(f7,axiom,(
% 11.23/1.99    ! [X0,X1] : ~(r1_xboole_0(k3_xboole_0(X0,X1),X1) & ~r1_xboole_0(X0,X1))),
% 11.23/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.23/1.99  
% 11.23/1.99  fof(f14,plain,(
% 11.23/1.99    ! [X0,X1] : (~r1_xboole_0(k3_xboole_0(X0,X1),X1) | r1_xboole_0(X0,X1))),
% 11.23/1.99    inference(ennf_transformation,[],[f7])).
% 11.23/1.99  
% 11.23/1.99  fof(f26,plain,(
% 11.23/1.99    ( ! [X0,X1] : (~r1_xboole_0(k3_xboole_0(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 11.23/1.99    inference(cnf_transformation,[],[f14])).
% 11.23/1.99  
% 11.23/1.99  fof(f33,plain,(
% 11.23/1.99    ( ! [X0,X1] : (~r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) | r1_xboole_0(X0,X1)) )),
% 11.23/1.99    inference(definition_unfolding,[],[f26,f23])).
% 11.23/1.99  
% 11.23/1.99  fof(f1,axiom,(
% 11.23/1.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 11.23/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.23/1.99  
% 11.23/1.99  fof(f20,plain,(
% 11.23/1.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 11.23/1.99    inference(cnf_transformation,[],[f1])).
% 11.23/1.99  
% 11.23/1.99  fof(f32,plain,(
% 11.23/1.99    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 11.23/1.99    inference(definition_unfolding,[],[f20,f23,f23])).
% 11.23/1.99  
% 11.23/1.99  fof(f3,axiom,(
% 11.23/1.99    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 11.23/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.23/1.99  
% 11.23/1.99  fof(f22,plain,(
% 11.23/1.99    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 11.23/1.99    inference(cnf_transformation,[],[f3])).
% 11.23/1.99  
% 11.23/1.99  fof(f6,axiom,(
% 11.23/1.99    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 11.23/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.23/1.99  
% 11.23/1.99  fof(f12,plain,(
% 11.23/1.99    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 11.23/1.99    inference(ennf_transformation,[],[f6])).
% 11.23/1.99  
% 11.23/1.99  fof(f13,plain,(
% 11.23/1.99    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 11.23/1.99    inference(flattening,[],[f12])).
% 11.23/1.99  
% 11.23/1.99  fof(f25,plain,(
% 11.23/1.99    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)) )),
% 11.23/1.99    inference(cnf_transformation,[],[f13])).
% 11.23/1.99  
% 11.23/1.99  fof(f2,axiom,(
% 11.23/1.99    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 11.23/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.23/1.99  
% 11.23/1.99  fof(f11,plain,(
% 11.23/1.99    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 11.23/1.99    inference(ennf_transformation,[],[f2])).
% 11.23/1.99  
% 11.23/1.99  fof(f21,plain,(
% 11.23/1.99    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 11.23/1.99    inference(cnf_transformation,[],[f11])).
% 11.23/1.99  
% 11.23/1.99  fof(f9,conjecture,(
% 11.23/1.99    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X3) & r1_xboole_0(X1,X3) & r1_xboole_0(X0,X3)) => r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3))),
% 11.23/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.23/1.99  
% 11.23/1.99  fof(f10,negated_conjecture,(
% 11.23/1.99    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X3) & r1_xboole_0(X1,X3) & r1_xboole_0(X0,X3)) => r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3))),
% 11.23/1.99    inference(negated_conjecture,[],[f9])).
% 11.23/1.99  
% 11.23/1.99  fof(f16,plain,(
% 11.23/1.99    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) & (r1_xboole_0(X2,X3) & r1_xboole_0(X1,X3) & r1_xboole_0(X0,X3)))),
% 11.23/1.99    inference(ennf_transformation,[],[f10])).
% 11.23/1.99  
% 11.23/1.99  fof(f17,plain,(
% 11.23/1.99    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) & r1_xboole_0(X2,X3) & r1_xboole_0(X1,X3) & r1_xboole_0(X0,X3))),
% 11.23/1.99    inference(flattening,[],[f16])).
% 11.23/1.99  
% 11.23/1.99  fof(f18,plain,(
% 11.23/1.99    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) & r1_xboole_0(X2,X3) & r1_xboole_0(X1,X3) & r1_xboole_0(X0,X3)) => (~r1_xboole_0(k2_xboole_0(k2_xboole_0(sK0,sK1),sK2),sK3) & r1_xboole_0(sK2,sK3) & r1_xboole_0(sK1,sK3) & r1_xboole_0(sK0,sK3))),
% 11.23/1.99    introduced(choice_axiom,[])).
% 11.23/1.99  
% 11.23/1.99  fof(f19,plain,(
% 11.23/1.99    ~r1_xboole_0(k2_xboole_0(k2_xboole_0(sK0,sK1),sK2),sK3) & r1_xboole_0(sK2,sK3) & r1_xboole_0(sK1,sK3) & r1_xboole_0(sK0,sK3)),
% 11.23/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f17,f18])).
% 11.23/1.99  
% 11.23/1.99  fof(f31,plain,(
% 11.23/1.99    ~r1_xboole_0(k2_xboole_0(k2_xboole_0(sK0,sK1),sK2),sK3)),
% 11.23/1.99    inference(cnf_transformation,[],[f19])).
% 11.23/1.99  
% 11.23/1.99  fof(f30,plain,(
% 11.23/1.99    r1_xboole_0(sK2,sK3)),
% 11.23/1.99    inference(cnf_transformation,[],[f19])).
% 11.23/1.99  
% 11.23/1.99  fof(f29,plain,(
% 11.23/1.99    r1_xboole_0(sK1,sK3)),
% 11.23/1.99    inference(cnf_transformation,[],[f19])).
% 11.23/1.99  
% 11.23/1.99  fof(f28,plain,(
% 11.23/1.99    r1_xboole_0(sK0,sK3)),
% 11.23/1.99    inference(cnf_transformation,[],[f19])).
% 11.23/1.99  
% 11.23/1.99  cnf(c_6,plain,
% 11.23/1.99      ( ~ r1_xboole_0(X0,X1)
% 11.23/1.99      | k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X1,X2))) = k4_xboole_0(X0,k4_xboole_0(X0,X2)) ),
% 11.23/1.99      inference(cnf_transformation,[],[f34]) ).
% 11.23/1.99  
% 11.23/1.99  cnf(c_178,plain,
% 11.23/1.99      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,X3) | X2 != X0 | X3 != X1 ),
% 11.23/1.99      theory(equality) ).
% 11.23/1.99  
% 11.23/1.99  cnf(c_175,plain,( X0 = X0 ),theory(equality) ).
% 11.23/1.99  
% 11.23/1.99  cnf(c_1284,plain,
% 11.23/1.99      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,X1) | X2 != X0 ),
% 11.23/1.99      inference(resolution,[status(thm)],[c_178,c_175]) ).
% 11.23/1.99  
% 11.23/1.99  cnf(c_2343,plain,
% 11.23/1.99      ( ~ r1_xboole_0(X0,X1)
% 11.23/1.99      | ~ r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X2)),X3)
% 11.23/1.99      | r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X1,X2))),X3) ),
% 11.23/1.99      inference(resolution,[status(thm)],[c_6,c_1284]) ).
% 11.23/1.99  
% 11.23/1.99  cnf(c_5,plain,
% 11.23/1.99      ( r1_xboole_0(X0,X1)
% 11.23/1.99      | ~ r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
% 11.23/1.99      inference(cnf_transformation,[],[f33]) ).
% 11.23/1.99  
% 11.23/1.99  cnf(c_14915,plain,
% 11.23/1.99      ( ~ r1_xboole_0(X0,X1)
% 11.23/1.99      | r1_xboole_0(X0,k2_xboole_0(X1,X2))
% 11.23/1.99      | ~ r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
% 11.23/1.99      inference(resolution,[status(thm)],[c_2343,c_5]) ).
% 11.23/1.99  
% 11.23/1.99  cnf(c_0,plain,
% 11.23/1.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 11.23/1.99      inference(cnf_transformation,[],[f32]) ).
% 11.23/1.99  
% 11.23/1.99  cnf(c_1296,plain,
% 11.23/1.99      ( ~ r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)
% 11.23/1.99      | r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
% 11.23/1.99      inference(resolution,[status(thm)],[c_1284,c_0]) ).
% 11.23/1.99  
% 11.23/1.99  cnf(c_2,plain,
% 11.23/1.99      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 11.23/1.99      inference(cnf_transformation,[],[f22]) ).
% 11.23/1.99  
% 11.23/1.99  cnf(c_4,plain,
% 11.23/1.99      ( ~ r1_tarski(X0,X1) | ~ r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2) ),
% 11.23/1.99      inference(cnf_transformation,[],[f25]) ).
% 11.23/1.99  
% 11.23/1.99  cnf(c_101,plain,
% 11.23/1.99      ( ~ r1_xboole_0(X0,X1)
% 11.23/1.99      | r1_xboole_0(X2,X1)
% 11.23/1.99      | X0 != X3
% 11.23/1.99      | k4_xboole_0(X3,X4) != X2 ),
% 11.23/1.99      inference(resolution_lifted,[status(thm)],[c_2,c_4]) ).
% 11.23/1.99  
% 11.23/1.99  cnf(c_102,plain,
% 11.23/1.99      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(k4_xboole_0(X0,X2),X1) ),
% 11.23/1.99      inference(unflattening,[status(thm)],[c_101]) ).
% 11.23/1.99  
% 11.23/1.99  cnf(c_1411,plain,
% 11.23/1.99      ( ~ r1_xboole_0(X0,X1)
% 11.23/1.99      | r1_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X0)),X1) ),
% 11.23/1.99      inference(resolution,[status(thm)],[c_1296,c_102]) ).
% 11.23/1.99  
% 11.23/1.99  cnf(c_1,plain,
% 11.23/1.99      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 11.23/1.99      inference(cnf_transformation,[],[f21]) ).
% 11.23/1.99  
% 11.23/1.99  cnf(c_570,plain,
% 11.23/1.99      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,k4_xboole_0(X0,X2)) ),
% 11.23/1.99      inference(resolution,[status(thm)],[c_102,c_1]) ).
% 11.23/1.99  
% 11.23/1.99  cnf(c_704,plain,
% 11.23/1.99      ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
% 11.23/1.99      | ~ r1_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))) ),
% 11.23/1.99      inference(resolution,[status(thm)],[c_5,c_570]) ).
% 11.23/1.99  
% 11.23/1.99  cnf(c_857,plain,
% 11.23/1.99      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 11.23/1.99      inference(resolution,[status(thm)],[c_704,c_570]) ).
% 11.23/1.99  
% 11.23/1.99  cnf(c_867,plain,
% 11.23/1.99      ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
% 11.23/1.99      | ~ r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))),X1) ),
% 11.23/1.99      inference(resolution,[status(thm)],[c_857,c_5]) ).
% 11.23/1.99  
% 11.23/1.99  cnf(c_1437,plain,
% 11.23/1.99      ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
% 11.23/1.99      | ~ r1_xboole_0(k4_xboole_0(X1,X2),X1) ),
% 11.23/1.99      inference(resolution,[status(thm)],[c_1411,c_867]) ).
% 11.23/1.99  
% 11.23/1.99  cnf(c_865,plain,
% 11.23/1.99      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(k4_xboole_0(X1,X2),X0) ),
% 11.23/1.99      inference(resolution,[status(thm)],[c_857,c_1]) ).
% 11.23/1.99  
% 11.23/1.99  cnf(c_1421,plain,
% 11.23/1.99      ( ~ r1_xboole_0(X0,X1)
% 11.23/1.99      | r1_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X1)),X0) ),
% 11.23/1.99      inference(resolution,[status(thm)],[c_1296,c_865]) ).
% 11.23/1.99  
% 11.23/1.99  cnf(c_1936,plain,
% 11.23/1.99      ( ~ r1_xboole_0(X0,X1)
% 11.23/1.99      | r1_xboole_0(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 11.23/1.99      inference(resolution,[status(thm)],[c_1437,c_1421]) ).
% 11.23/1.99  
% 11.23/1.99  cnf(c_2321,plain,
% 11.23/1.99      ( ~ r1_xboole_0(X0,X1)
% 11.23/1.99      | r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
% 11.23/1.99      inference(resolution,[status(thm)],[c_1936,c_1]) ).
% 11.23/1.99  
% 11.23/1.99  cnf(c_35923,plain,
% 11.23/1.99      ( ~ r1_xboole_0(X0,X1)
% 11.23/1.99      | ~ r1_xboole_0(X0,X2)
% 11.23/1.99      | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 11.23/1.99      inference(resolution,[status(thm)],[c_14915,c_2321]) ).
% 11.23/1.99  
% 11.23/1.99  cnf(c_37168,plain,
% 11.23/1.99      ( ~ r1_xboole_0(X0,X1)
% 11.23/1.99      | ~ r1_xboole_0(X0,X2)
% 11.23/1.99      | r1_xboole_0(k2_xboole_0(X1,X2),X0) ),
% 11.23/1.99      inference(resolution,[status(thm)],[c_35923,c_1]) ).
% 11.23/1.99  
% 11.23/1.99  cnf(c_7,negated_conjecture,
% 11.23/1.99      ( ~ r1_xboole_0(k2_xboole_0(k2_xboole_0(sK0,sK1),sK2),sK3) ),
% 11.23/1.99      inference(cnf_transformation,[],[f31]) ).
% 11.23/1.99  
% 11.23/1.99  cnf(c_38200,plain,
% 11.23/1.99      ( ~ r1_xboole_0(sK3,k2_xboole_0(sK0,sK1))
% 11.23/1.99      | ~ r1_xboole_0(sK3,sK2) ),
% 11.23/1.99      inference(resolution,[status(thm)],[c_37168,c_7]) ).
% 11.23/1.99  
% 11.23/1.99  cnf(c_8,negated_conjecture,
% 11.23/1.99      ( r1_xboole_0(sK2,sK3) ),
% 11.23/1.99      inference(cnf_transformation,[],[f30]) ).
% 11.23/1.99  
% 11.23/1.99  cnf(c_395,plain,
% 11.23/1.99      ( r1_xboole_0(sK3,sK2) | ~ r1_xboole_0(sK2,sK3) ),
% 11.23/1.99      inference(instantiation,[status(thm)],[c_1]) ).
% 11.23/1.99  
% 11.23/1.99  cnf(c_38920,plain,
% 11.23/1.99      ( ~ r1_xboole_0(sK3,k2_xboole_0(sK0,sK1)) ),
% 11.23/1.99      inference(global_propositional_subsumption,
% 11.23/1.99                [status(thm)],
% 11.23/1.99                [c_38200,c_8,c_395]) ).
% 11.23/1.99  
% 11.23/1.99  cnf(c_1932,plain,
% 11.23/1.99      ( ~ r1_xboole_0(X0,X1)
% 11.23/1.99      | r1_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
% 11.23/1.99      inference(resolution,[status(thm)],[c_1437,c_1411]) ).
% 11.23/1.99  
% 11.23/1.99  cnf(c_2298,plain,
% 11.23/1.99      ( ~ r1_xboole_0(X0,X1)
% 11.23/1.99      | r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
% 11.23/1.99      inference(resolution,[status(thm)],[c_1932,c_1]) ).
% 11.23/1.99  
% 11.23/1.99  cnf(c_35941,plain,
% 11.23/1.99      ( ~ r1_xboole_0(X0,X1)
% 11.23/1.99      | ~ r1_xboole_0(X2,X0)
% 11.23/1.99      | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 11.23/1.99      inference(resolution,[status(thm)],[c_14915,c_2298]) ).
% 11.23/1.99  
% 11.23/1.99  cnf(c_38933,plain,
% 11.23/1.99      ( ~ r1_xboole_0(sK3,sK0) | ~ r1_xboole_0(sK1,sK3) ),
% 11.23/1.99      inference(resolution,[status(thm)],[c_38920,c_35941]) ).
% 11.23/1.99  
% 11.23/1.99  cnf(c_401,plain,
% 11.23/1.99      ( r1_xboole_0(sK3,sK0) | ~ r1_xboole_0(sK0,sK3) ),
% 11.23/1.99      inference(instantiation,[status(thm)],[c_1]) ).
% 11.23/1.99  
% 11.23/1.99  cnf(c_9,negated_conjecture,
% 11.23/1.99      ( r1_xboole_0(sK1,sK3) ),
% 11.23/1.99      inference(cnf_transformation,[],[f29]) ).
% 11.23/1.99  
% 11.23/1.99  cnf(c_10,negated_conjecture,
% 11.23/1.99      ( r1_xboole_0(sK0,sK3) ),
% 11.23/1.99      inference(cnf_transformation,[],[f28]) ).
% 11.23/1.99  
% 11.23/1.99  cnf(contradiction,plain,
% 11.23/1.99      ( $false ),
% 11.23/1.99      inference(minisat,[status(thm)],[c_38933,c_401,c_9,c_10]) ).
% 11.23/1.99  
% 11.23/1.99  
% 11.23/1.99  % SZS output end CNFRefutation for theBenchmark.p
% 11.23/1.99  
% 11.23/1.99  ------                               Statistics
% 11.23/1.99  
% 11.23/1.99  ------ Selected
% 11.23/1.99  
% 11.23/1.99  total_time:                             1.067
% 11.23/1.99  
%------------------------------------------------------------------------------
