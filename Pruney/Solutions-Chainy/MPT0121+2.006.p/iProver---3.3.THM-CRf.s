%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:26:11 EST 2020

% Result     : Theorem 3.51s
% Output     : CNFRefutation 3.51s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 139 expanded)
%              Number of clauses        :   34 (  60 expanded)
%              Number of leaves         :    9 (  38 expanded)
%              Depth                    :   13
%              Number of atoms          :  128 ( 351 expanded)
%              Number of equality atoms :   37 ( 109 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X3)
        & r1_xboole_0(X1,X3)
        & r1_xboole_0(X0,X3) )
     => r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X2,X3)
          & r1_xboole_0(X1,X3)
          & r1_xboole_0(X0,X3) )
       => r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f8,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3)
      & r1_xboole_0(X2,X3)
      & r1_xboole_0(X1,X3)
      & r1_xboole_0(X0,X3) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f9,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3)
      & r1_xboole_0(X2,X3)
      & r1_xboole_0(X1,X3)
      & r1_xboole_0(X0,X3) ) ),
    inference(flattening,[],[f8])).

fof(f11,plain,
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

fof(f12,plain,
    ( ~ r1_xboole_0(k2_xboole_0(k2_xboole_0(sK0,sK1),sK2),sK3)
    & r1_xboole_0(sK2,sK3)
    & r1_xboole_0(sK1,sK3)
    & r1_xboole_0(sK0,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f9,f11])).

fof(f21,plain,(
    ~ r1_xboole_0(k2_xboole_0(k2_xboole_0(sK0,sK1),sK2),sK3) ),
    inference(cnf_transformation,[],[f12])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f23,plain,(
    ~ r1_xboole_0(k5_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK2,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)))),sK3) ),
    inference(definition_unfolding,[],[f21,f17,f17])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f22,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) ),
    inference(definition_unfolding,[],[f14,f17])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f20,plain,(
    r1_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f12])).

fof(f19,plain,(
    r1_xboole_0(sK1,sK3) ),
    inference(cnf_transformation,[],[f12])).

fof(f18,plain,(
    r1_xboole_0(sK0,sK3) ),
    inference(cnf_transformation,[],[f12])).

cnf(c_4,negated_conjecture,
    ( ~ r1_xboole_0(k5_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK2,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)))),sK3) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_96,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_95,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_882,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_96,c_95])).

cnf(c_3,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f15])).

cnf(c_1038,plain,
    ( ~ r1_xboole_0(X0,X1)
    | X0 = k4_xboole_0(X0,X1) ),
    inference(resolution,[status(thm)],[c_882,c_3])).

cnf(c_1073,plain,
    ( ~ r1_xboole_0(X0,X1)
    | X0 = X2
    | X2 != k4_xboole_0(X0,X1) ),
    inference(resolution,[status(thm)],[c_1038,c_96])).

cnf(c_2283,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(k4_xboole_0(X0,X1),X2)
    | X0 = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(resolution,[status(thm)],[c_1073,c_3])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_878,plain,
    ( X0 != k4_xboole_0(k4_xboole_0(X1,X2),X3)
    | k4_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X3,X2))) = X0 ),
    inference(resolution,[status(thm)],[c_96,c_1])).

cnf(c_2,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) != X0 ),
    inference(cnf_transformation,[],[f16])).

cnf(c_2127,plain,
    ( r1_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1)))
    | X0 != k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(resolution,[status(thm)],[c_878,c_2])).

cnf(c_8014,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1)))
    | ~ r1_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(resolution,[status(thm)],[c_2283,c_2127])).

cnf(c_0,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f13])).

cnf(c_8308,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),X0)
    | ~ r1_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(resolution,[status(thm)],[c_8014,c_0])).

cnf(c_8636,plain,
    ( ~ r1_xboole_0(k4_xboole_0(sK3,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))),sK2)
    | ~ r1_xboole_0(sK3,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))) ),
    inference(resolution,[status(thm)],[c_4,c_8308])).

cnf(c_97,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_870,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_95,c_97])).

cnf(c_1057,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(X0,X2)
    | r1_xboole_0(k4_xboole_0(X0,X2),X1) ),
    inference(resolution,[status(thm)],[c_870,c_3])).

cnf(c_8650,plain,
    ( ~ r1_xboole_0(sK3,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)))
    | ~ r1_xboole_0(sK3,sK2) ),
    inference(resolution,[status(thm)],[c_8636,c_1057])).

cnf(c_5,negated_conjecture,
    ( r1_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_340,plain,
    ( r1_xboole_0(sK3,sK2)
    | ~ r1_xboole_0(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_8657,plain,
    ( ~ r1_xboole_0(sK3,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8650,c_5,c_340])).

cnf(c_9028,plain,
    ( ~ r1_xboole_0(k4_xboole_0(sK3,sK0),sK1)
    | ~ r1_xboole_0(sK3,sK0) ),
    inference(resolution,[status(thm)],[c_8657,c_8014])).

cnf(c_415,plain,
    ( r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(sK3,sK1)
    | X0 != sK3
    | X1 != sK1 ),
    inference(instantiation,[status(thm)],[c_97])).

cnf(c_536,plain,
    ( r1_xboole_0(X0,sK1)
    | ~ r1_xboole_0(sK3,sK1)
    | X0 != sK3
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_415])).

cnf(c_915,plain,
    ( r1_xboole_0(k4_xboole_0(sK3,sK0),sK1)
    | ~ r1_xboole_0(sK3,sK1)
    | k4_xboole_0(sK3,sK0) != sK3
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_536])).

cnf(c_537,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_95])).

cnf(c_429,plain,
    ( ~ r1_xboole_0(sK3,sK0)
    | k4_xboole_0(sK3,sK0) = sK3 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_346,plain,
    ( r1_xboole_0(sK3,sK0)
    | ~ r1_xboole_0(sK0,sK3) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_343,plain,
    ( r1_xboole_0(sK3,sK1)
    | ~ r1_xboole_0(sK1,sK3) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_6,negated_conjecture,
    ( r1_xboole_0(sK1,sK3) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_7,negated_conjecture,
    ( r1_xboole_0(sK0,sK3) ),
    inference(cnf_transformation,[],[f18])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9028,c_915,c_537,c_429,c_346,c_343,c_6,c_7])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:14:04 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.51/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.51/0.98  
% 3.51/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.51/0.98  
% 3.51/0.98  ------  iProver source info
% 3.51/0.98  
% 3.51/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.51/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.51/0.98  git: non_committed_changes: false
% 3.51/0.98  git: last_make_outside_of_git: false
% 3.51/0.98  
% 3.51/0.98  ------ 
% 3.51/0.98  ------ Parsing...
% 3.51/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.51/0.98  
% 3.51/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.51/0.98  
% 3.51/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.51/0.98  
% 3.51/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.51/0.98  ------ Proving...
% 3.51/0.98  ------ Problem Properties 
% 3.51/0.98  
% 3.51/0.98  
% 3.51/0.98  clauses                                 8
% 3.51/0.98  conjectures                             4
% 3.51/0.98  EPR                                     4
% 3.51/0.98  Horn                                    8
% 3.51/0.98  unary                                   5
% 3.51/0.98  binary                                  3
% 3.51/0.98  lits                                    11
% 3.51/0.98  lits eq                                 3
% 3.51/0.98  fd_pure                                 0
% 3.51/0.98  fd_pseudo                               0
% 3.51/0.98  fd_cond                                 0
% 3.51/0.98  fd_pseudo_cond                          0
% 3.51/0.98  AC symbols                              0
% 3.51/0.98  
% 3.51/0.98  ------ Input Options Time Limit: Unbounded
% 3.51/0.98  
% 3.51/0.98  
% 3.51/0.98  ------ 
% 3.51/0.98  Current options:
% 3.51/0.98  ------ 
% 3.51/0.98  
% 3.51/0.98  
% 3.51/0.98  
% 3.51/0.98  
% 3.51/0.98  ------ Proving...
% 3.51/0.98  
% 3.51/0.98  
% 3.51/0.98  % SZS status Theorem for theBenchmark.p
% 3.51/0.98  
% 3.51/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.51/0.98  
% 3.51/0.98  fof(f5,conjecture,(
% 3.51/0.98    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X3) & r1_xboole_0(X1,X3) & r1_xboole_0(X0,X3)) => r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3))),
% 3.51/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.51/0.98  
% 3.51/0.98  fof(f6,negated_conjecture,(
% 3.51/0.98    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X3) & r1_xboole_0(X1,X3) & r1_xboole_0(X0,X3)) => r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3))),
% 3.51/0.98    inference(negated_conjecture,[],[f5])).
% 3.51/0.98  
% 3.51/0.98  fof(f8,plain,(
% 3.51/0.98    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) & (r1_xboole_0(X2,X3) & r1_xboole_0(X1,X3) & r1_xboole_0(X0,X3)))),
% 3.51/0.98    inference(ennf_transformation,[],[f6])).
% 3.51/0.98  
% 3.51/0.98  fof(f9,plain,(
% 3.51/0.98    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) & r1_xboole_0(X2,X3) & r1_xboole_0(X1,X3) & r1_xboole_0(X0,X3))),
% 3.51/0.98    inference(flattening,[],[f8])).
% 3.51/0.98  
% 3.51/0.98  fof(f11,plain,(
% 3.51/0.98    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) & r1_xboole_0(X2,X3) & r1_xboole_0(X1,X3) & r1_xboole_0(X0,X3)) => (~r1_xboole_0(k2_xboole_0(k2_xboole_0(sK0,sK1),sK2),sK3) & r1_xboole_0(sK2,sK3) & r1_xboole_0(sK1,sK3) & r1_xboole_0(sK0,sK3))),
% 3.51/0.98    introduced(choice_axiom,[])).
% 3.51/0.98  
% 3.51/0.98  fof(f12,plain,(
% 3.51/0.98    ~r1_xboole_0(k2_xboole_0(k2_xboole_0(sK0,sK1),sK2),sK3) & r1_xboole_0(sK2,sK3) & r1_xboole_0(sK1,sK3) & r1_xboole_0(sK0,sK3)),
% 3.51/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f9,f11])).
% 3.51/0.98  
% 3.51/0.98  fof(f21,plain,(
% 3.51/0.98    ~r1_xboole_0(k2_xboole_0(k2_xboole_0(sK0,sK1),sK2),sK3)),
% 3.51/0.98    inference(cnf_transformation,[],[f12])).
% 3.51/0.98  
% 3.51/0.98  fof(f4,axiom,(
% 3.51/0.98    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 3.51/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.51/0.98  
% 3.51/0.98  fof(f17,plain,(
% 3.51/0.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 3.51/0.98    inference(cnf_transformation,[],[f4])).
% 3.51/0.98  
% 3.51/0.98  fof(f23,plain,(
% 3.51/0.98    ~r1_xboole_0(k5_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK2,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)))),sK3)),
% 3.51/0.98    inference(definition_unfolding,[],[f21,f17,f17])).
% 3.51/0.98  
% 3.51/0.98  fof(f3,axiom,(
% 3.51/0.98    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 3.51/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.51/0.98  
% 3.51/0.98  fof(f10,plain,(
% 3.51/0.98    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 3.51/0.98    inference(nnf_transformation,[],[f3])).
% 3.51/0.98  
% 3.51/0.98  fof(f15,plain,(
% 3.51/0.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 3.51/0.98    inference(cnf_transformation,[],[f10])).
% 3.51/0.98  
% 3.51/0.98  fof(f2,axiom,(
% 3.51/0.98    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 3.51/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.51/0.98  
% 3.51/0.98  fof(f14,plain,(
% 3.51/0.98    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 3.51/0.98    inference(cnf_transformation,[],[f2])).
% 3.51/0.98  
% 3.51/0.98  fof(f22,plain,(
% 3.51/0.98    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1)))) )),
% 3.51/0.98    inference(definition_unfolding,[],[f14,f17])).
% 3.51/0.98  
% 3.51/0.98  fof(f16,plain,(
% 3.51/0.98    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 3.51/0.98    inference(cnf_transformation,[],[f10])).
% 3.51/0.98  
% 3.51/0.98  fof(f1,axiom,(
% 3.51/0.98    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 3.51/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.51/0.98  
% 3.51/0.98  fof(f7,plain,(
% 3.51/0.98    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 3.51/0.98    inference(ennf_transformation,[],[f1])).
% 3.51/0.98  
% 3.51/0.98  fof(f13,plain,(
% 3.51/0.98    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 3.51/0.98    inference(cnf_transformation,[],[f7])).
% 3.51/0.98  
% 3.51/0.98  fof(f20,plain,(
% 3.51/0.98    r1_xboole_0(sK2,sK3)),
% 3.51/0.98    inference(cnf_transformation,[],[f12])).
% 3.51/0.98  
% 3.51/0.98  fof(f19,plain,(
% 3.51/0.98    r1_xboole_0(sK1,sK3)),
% 3.51/0.98    inference(cnf_transformation,[],[f12])).
% 3.51/0.98  
% 3.51/0.98  fof(f18,plain,(
% 3.51/0.98    r1_xboole_0(sK0,sK3)),
% 3.51/0.98    inference(cnf_transformation,[],[f12])).
% 3.51/0.98  
% 3.51/0.98  cnf(c_4,negated_conjecture,
% 3.51/0.98      ( ~ r1_xboole_0(k5_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK2,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)))),sK3) ),
% 3.51/0.98      inference(cnf_transformation,[],[f23]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_96,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_95,plain,( X0 = X0 ),theory(equality) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_882,plain,
% 3.51/0.98      ( X0 != X1 | X1 = X0 ),
% 3.51/0.98      inference(resolution,[status(thm)],[c_96,c_95]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_3,plain,
% 3.51/0.98      ( ~ r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0 ),
% 3.51/0.98      inference(cnf_transformation,[],[f15]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_1038,plain,
% 3.51/0.98      ( ~ r1_xboole_0(X0,X1) | X0 = k4_xboole_0(X0,X1) ),
% 3.51/0.98      inference(resolution,[status(thm)],[c_882,c_3]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_1073,plain,
% 3.51/0.98      ( ~ r1_xboole_0(X0,X1) | X0 = X2 | X2 != k4_xboole_0(X0,X1) ),
% 3.51/0.98      inference(resolution,[status(thm)],[c_1038,c_96]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_2283,plain,
% 3.51/0.98      ( ~ r1_xboole_0(X0,X1)
% 3.51/0.98      | ~ r1_xboole_0(k4_xboole_0(X0,X1),X2)
% 3.51/0.98      | X0 = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 3.51/0.98      inference(resolution,[status(thm)],[c_1073,c_3]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_1,plain,
% 3.51/0.98      ( k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 3.51/0.98      inference(cnf_transformation,[],[f22]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_878,plain,
% 3.51/0.98      ( X0 != k4_xboole_0(k4_xboole_0(X1,X2),X3)
% 3.51/0.98      | k4_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X3,X2))) = X0 ),
% 3.51/0.98      inference(resolution,[status(thm)],[c_96,c_1]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_2,plain,
% 3.51/0.98      ( r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0 ),
% 3.51/0.98      inference(cnf_transformation,[],[f16]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_2127,plain,
% 3.51/0.98      ( r1_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1)))
% 3.51/0.98      | X0 != k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 3.51/0.98      inference(resolution,[status(thm)],[c_878,c_2]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_8014,plain,
% 3.51/0.98      ( ~ r1_xboole_0(X0,X1)
% 3.51/0.98      | r1_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1)))
% 3.51/0.98      | ~ r1_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 3.51/0.98      inference(resolution,[status(thm)],[c_2283,c_2127]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_0,plain,
% 3.51/0.98      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 3.51/0.98      inference(cnf_transformation,[],[f13]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_8308,plain,
% 3.51/0.98      ( ~ r1_xboole_0(X0,X1)
% 3.51/0.98      | r1_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),X0)
% 3.51/0.98      | ~ r1_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 3.51/0.98      inference(resolution,[status(thm)],[c_8014,c_0]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_8636,plain,
% 3.51/0.98      ( ~ r1_xboole_0(k4_xboole_0(sK3,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))),sK2)
% 3.51/0.98      | ~ r1_xboole_0(sK3,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))) ),
% 3.51/0.98      inference(resolution,[status(thm)],[c_4,c_8308]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_97,plain,
% 3.51/0.98      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.51/0.98      theory(equality) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_870,plain,
% 3.51/0.98      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,X1) | X2 != X0 ),
% 3.51/0.98      inference(resolution,[status(thm)],[c_95,c_97]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_1057,plain,
% 3.51/0.98      ( ~ r1_xboole_0(X0,X1)
% 3.51/0.98      | ~ r1_xboole_0(X0,X2)
% 3.51/0.98      | r1_xboole_0(k4_xboole_0(X0,X2),X1) ),
% 3.51/0.98      inference(resolution,[status(thm)],[c_870,c_3]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_8650,plain,
% 3.51/0.98      ( ~ r1_xboole_0(sK3,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)))
% 3.51/0.98      | ~ r1_xboole_0(sK3,sK2) ),
% 3.51/0.98      inference(resolution,[status(thm)],[c_8636,c_1057]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_5,negated_conjecture,
% 3.51/0.98      ( r1_xboole_0(sK2,sK3) ),
% 3.51/0.98      inference(cnf_transformation,[],[f20]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_340,plain,
% 3.51/0.98      ( r1_xboole_0(sK3,sK2) | ~ r1_xboole_0(sK2,sK3) ),
% 3.51/0.98      inference(instantiation,[status(thm)],[c_0]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_8657,plain,
% 3.51/0.98      ( ~ r1_xboole_0(sK3,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))) ),
% 3.51/0.98      inference(global_propositional_subsumption,
% 3.51/0.98                [status(thm)],
% 3.51/0.98                [c_8650,c_5,c_340]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_9028,plain,
% 3.51/0.98      ( ~ r1_xboole_0(k4_xboole_0(sK3,sK0),sK1)
% 3.51/0.98      | ~ r1_xboole_0(sK3,sK0) ),
% 3.51/0.98      inference(resolution,[status(thm)],[c_8657,c_8014]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_415,plain,
% 3.51/0.98      ( r1_xboole_0(X0,X1)
% 3.51/0.98      | ~ r1_xboole_0(sK3,sK1)
% 3.51/0.98      | X0 != sK3
% 3.51/0.98      | X1 != sK1 ),
% 3.51/0.98      inference(instantiation,[status(thm)],[c_97]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_536,plain,
% 3.51/0.98      ( r1_xboole_0(X0,sK1)
% 3.51/0.98      | ~ r1_xboole_0(sK3,sK1)
% 3.51/0.98      | X0 != sK3
% 3.51/0.98      | sK1 != sK1 ),
% 3.51/0.98      inference(instantiation,[status(thm)],[c_415]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_915,plain,
% 3.51/0.98      ( r1_xboole_0(k4_xboole_0(sK3,sK0),sK1)
% 3.51/0.98      | ~ r1_xboole_0(sK3,sK1)
% 3.51/0.98      | k4_xboole_0(sK3,sK0) != sK3
% 3.51/0.98      | sK1 != sK1 ),
% 3.51/0.98      inference(instantiation,[status(thm)],[c_536]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_537,plain,
% 3.51/0.98      ( sK1 = sK1 ),
% 3.51/0.98      inference(instantiation,[status(thm)],[c_95]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_429,plain,
% 3.51/0.98      ( ~ r1_xboole_0(sK3,sK0) | k4_xboole_0(sK3,sK0) = sK3 ),
% 3.51/0.98      inference(instantiation,[status(thm)],[c_3]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_346,plain,
% 3.51/0.98      ( r1_xboole_0(sK3,sK0) | ~ r1_xboole_0(sK0,sK3) ),
% 3.51/0.98      inference(instantiation,[status(thm)],[c_0]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_343,plain,
% 3.51/0.98      ( r1_xboole_0(sK3,sK1) | ~ r1_xboole_0(sK1,sK3) ),
% 3.51/0.98      inference(instantiation,[status(thm)],[c_0]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_6,negated_conjecture,
% 3.51/0.98      ( r1_xboole_0(sK1,sK3) ),
% 3.51/0.98      inference(cnf_transformation,[],[f19]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_7,negated_conjecture,
% 3.51/0.98      ( r1_xboole_0(sK0,sK3) ),
% 3.51/0.98      inference(cnf_transformation,[],[f18]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(contradiction,plain,
% 3.51/0.98      ( $false ),
% 3.51/0.98      inference(minisat,
% 3.51/0.98                [status(thm)],
% 3.51/0.98                [c_9028,c_915,c_537,c_429,c_346,c_343,c_6,c_7]) ).
% 3.51/0.98  
% 3.51/0.98  
% 3.51/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.51/0.98  
% 3.51/0.98  ------                               Statistics
% 3.51/0.98  
% 3.51/0.98  ------ Selected
% 3.51/0.98  
% 3.51/0.98  total_time:                             0.279
% 3.51/0.98  
%------------------------------------------------------------------------------
