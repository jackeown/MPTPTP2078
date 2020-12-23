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
% DateTime   : Thu Dec  3 11:26:10 EST 2020

% Result     : Theorem 7.76s
% Output     : CNFRefutation 7.76s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 184 expanded)
%              Number of clauses        :   43 (  96 expanded)
%              Number of leaves         :   10 (  53 expanded)
%              Depth                    :   14
%              Number of atoms          :  152 ( 475 expanded)
%              Number of equality atoms :   40 ( 172 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    3 (   1 average)

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
    inference(nnf_transformation,[],[f4])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f20,plain,(
    r1_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f12])).

fof(f19,plain,(
    r1_xboole_0(sK1,sK3) ),
    inference(cnf_transformation,[],[f12])).

fof(f18,plain,(
    r1_xboole_0(sK0,sK3) ),
    inference(cnf_transformation,[],[f12])).

cnf(c_5,negated_conjecture,
    ( ~ r1_xboole_0(k2_xboole_0(k2_xboole_0(sK0,sK1),sK2),sK3) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_99,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_98,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_816,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_99,c_98])).

cnf(c_4,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f16])).

cnf(c_1003,plain,
    ( ~ r1_xboole_0(X0,X1)
    | X0 = k4_xboole_0(X0,X1) ),
    inference(resolution,[status(thm)],[c_816,c_4])).

cnf(c_1017,plain,
    ( ~ r1_xboole_0(X0,X1)
    | X0 = X2
    | X2 != k4_xboole_0(X0,X1) ),
    inference(resolution,[status(thm)],[c_1003,c_99])).

cnf(c_1641,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(k4_xboole_0(X0,X1),X2)
    | X0 = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(resolution,[status(thm)],[c_1017,c_4])).

cnf(c_2,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_1001,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(resolution,[status(thm)],[c_816,c_2])).

cnf(c_3682,plain,
    ( X0 != k4_xboole_0(k4_xboole_0(X1,X2),X3)
    | k4_xboole_0(X1,k2_xboole_0(X2,X3)) = X0 ),
    inference(resolution,[status(thm)],[c_1001,c_99])).

cnf(c_14627,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(k4_xboole_0(X0,X1),X2)
    | k4_xboole_0(X0,k2_xboole_0(X1,X2)) = X0 ),
    inference(resolution,[status(thm)],[c_1641,c_3682])).

cnf(c_3,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) != X0 ),
    inference(cnf_transformation,[],[f17])).

cnf(c_27101,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X0,k2_xboole_0(X1,X2))
    | ~ r1_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(resolution,[status(thm)],[c_14627,c_3])).

cnf(c_101,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_802,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_98,c_101])).

cnf(c_1152,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(X0,X2)
    | r1_xboole_0(k4_xboole_0(X0,X2),X1) ),
    inference(resolution,[status(thm)],[c_802,c_4])).

cnf(c_27230,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(X0,X2)
    | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(resolution,[status(thm)],[c_27101,c_1152])).

cnf(c_102,plain,
    ( X0 != X1
    | X2 != X3
    | k4_xboole_0(X0,X2) = k4_xboole_0(X1,X3) ),
    theory(equality)).

cnf(c_988,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X2)
    | X2 != X1
    | k4_xboole_0(X0,X1) != X0 ),
    inference(resolution,[status(thm)],[c_102,c_3])).

cnf(c_2166,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(k4_xboole_0(X0,X1),X2)
    | X2 != X1 ),
    inference(resolution,[status(thm)],[c_988,c_4])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f14])).

cnf(c_2517,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,k4_xboole_0(X0,X1))
    | X2 != X1 ),
    inference(resolution,[status(thm)],[c_2166,c_1])).

cnf(c_1161,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X0,X2)
    | ~ r1_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(resolution,[status(thm)],[c_802,c_1003])).

cnf(c_2519,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X0,X2)
    | X2 != X1 ),
    inference(resolution,[status(thm)],[c_2166,c_1161])).

cnf(c_2625,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X0)
    | ~ r1_xboole_0(X2,k4_xboole_0(X0,X1)) ),
    inference(resolution,[status(thm)],[c_2519,c_1003])).

cnf(c_2830,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X0)
    | X2 != X1 ),
    inference(resolution,[status(thm)],[c_2517,c_2625])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f13])).

cnf(c_2840,plain,
    ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
    | r1_xboole_0(k2_xboole_0(X2,X1),X0) ),
    inference(resolution,[status(thm)],[c_2830,c_0])).

cnf(c_27322,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(X0,X2)
    | r1_xboole_0(k2_xboole_0(X2,X1),X0) ),
    inference(resolution,[status(thm)],[c_27230,c_2840])).

cnf(c_30093,plain,
    ( ~ r1_xboole_0(sK3,k2_xboole_0(sK0,sK1))
    | ~ r1_xboole_0(sK3,sK2) ),
    inference(resolution,[status(thm)],[c_5,c_27322])).

cnf(c_6,negated_conjecture,
    ( r1_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_345,plain,
    ( r1_xboole_0(sK3,sK2)
    | ~ r1_xboole_0(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_30096,plain,
    ( ~ r1_xboole_0(sK3,k2_xboole_0(sK0,sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_30093,c_6,c_345])).

cnf(c_668,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(X1,X2)
    | r1_xboole_0(X3,k4_xboole_0(X1,X2))
    | X3 != X0 ),
    inference(resolution,[status(thm)],[c_101,c_4])).

cnf(c_2199,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(X1,X2)
    | r1_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(resolution,[status(thm)],[c_668,c_98])).

cnf(c_2360,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(X1,X2)
    | r1_xboole_0(k4_xboole_0(X1,X2),X0) ),
    inference(resolution,[status(thm)],[c_2199,c_1])).

cnf(c_27276,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(X2,X0)
    | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(resolution,[status(thm)],[c_27101,c_2360])).

cnf(c_30109,plain,
    ( ~ r1_xboole_0(sK3,sK0)
    | ~ r1_xboole_0(sK1,sK3) ),
    inference(resolution,[status(thm)],[c_30096,c_27276])).

cnf(c_351,plain,
    ( r1_xboole_0(sK3,sK0)
    | ~ r1_xboole_0(sK0,sK3) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_7,negated_conjecture,
    ( r1_xboole_0(sK1,sK3) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_8,negated_conjecture,
    ( r1_xboole_0(sK0,sK3) ),
    inference(cnf_transformation,[],[f18])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_30109,c_351,c_7,c_8])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n018.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:06:57 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.76/1.48  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.76/1.48  
% 7.76/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.76/1.48  
% 7.76/1.48  ------  iProver source info
% 7.76/1.48  
% 7.76/1.48  git: date: 2020-06-30 10:37:57 +0100
% 7.76/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.76/1.48  git: non_committed_changes: false
% 7.76/1.48  git: last_make_outside_of_git: false
% 7.76/1.48  
% 7.76/1.48  ------ 
% 7.76/1.48  ------ Parsing...
% 7.76/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.76/1.48  
% 7.76/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.76/1.48  
% 7.76/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.76/1.48  
% 7.76/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.76/1.48  ------ Proving...
% 7.76/1.48  ------ Problem Properties 
% 7.76/1.48  
% 7.76/1.48  
% 7.76/1.48  clauses                                 9
% 7.76/1.48  conjectures                             4
% 7.76/1.48  EPR                                     4
% 7.76/1.48  Horn                                    9
% 7.76/1.48  unary                                   6
% 7.76/1.48  binary                                  3
% 7.76/1.48  lits                                    12
% 7.76/1.48  lits eq                                 4
% 7.76/1.48  fd_pure                                 0
% 7.76/1.48  fd_pseudo                               0
% 7.76/1.48  fd_cond                                 0
% 7.76/1.48  fd_pseudo_cond                          0
% 7.76/1.48  AC symbols                              0
% 7.76/1.48  
% 7.76/1.48  ------ Input Options Time Limit: Unbounded
% 7.76/1.48  
% 7.76/1.48  
% 7.76/1.48  ------ 
% 7.76/1.48  Current options:
% 7.76/1.48  ------ 
% 7.76/1.48  
% 7.76/1.48  
% 7.76/1.48  
% 7.76/1.48  
% 7.76/1.48  ------ Proving...
% 7.76/1.48  
% 7.76/1.48  
% 7.76/1.48  % SZS status Theorem for theBenchmark.p
% 7.76/1.48  
% 7.76/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 7.76/1.48  
% 7.76/1.48  fof(f5,conjecture,(
% 7.76/1.48    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X3) & r1_xboole_0(X1,X3) & r1_xboole_0(X0,X3)) => r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3))),
% 7.76/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.76/1.48  
% 7.76/1.48  fof(f6,negated_conjecture,(
% 7.76/1.48    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X3) & r1_xboole_0(X1,X3) & r1_xboole_0(X0,X3)) => r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3))),
% 7.76/1.48    inference(negated_conjecture,[],[f5])).
% 7.76/1.48  
% 7.76/1.48  fof(f8,plain,(
% 7.76/1.48    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) & (r1_xboole_0(X2,X3) & r1_xboole_0(X1,X3) & r1_xboole_0(X0,X3)))),
% 7.76/1.48    inference(ennf_transformation,[],[f6])).
% 7.76/1.48  
% 7.76/1.48  fof(f9,plain,(
% 7.76/1.48    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) & r1_xboole_0(X2,X3) & r1_xboole_0(X1,X3) & r1_xboole_0(X0,X3))),
% 7.76/1.48    inference(flattening,[],[f8])).
% 7.76/1.48  
% 7.76/1.48  fof(f11,plain,(
% 7.76/1.48    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) & r1_xboole_0(X2,X3) & r1_xboole_0(X1,X3) & r1_xboole_0(X0,X3)) => (~r1_xboole_0(k2_xboole_0(k2_xboole_0(sK0,sK1),sK2),sK3) & r1_xboole_0(sK2,sK3) & r1_xboole_0(sK1,sK3) & r1_xboole_0(sK0,sK3))),
% 7.76/1.48    introduced(choice_axiom,[])).
% 7.76/1.48  
% 7.76/1.48  fof(f12,plain,(
% 7.76/1.48    ~r1_xboole_0(k2_xboole_0(k2_xboole_0(sK0,sK1),sK2),sK3) & r1_xboole_0(sK2,sK3) & r1_xboole_0(sK1,sK3) & r1_xboole_0(sK0,sK3)),
% 7.76/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f9,f11])).
% 7.76/1.48  
% 7.76/1.48  fof(f21,plain,(
% 7.76/1.48    ~r1_xboole_0(k2_xboole_0(k2_xboole_0(sK0,sK1),sK2),sK3)),
% 7.76/1.48    inference(cnf_transformation,[],[f12])).
% 7.76/1.48  
% 7.76/1.48  fof(f4,axiom,(
% 7.76/1.48    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 7.76/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.76/1.48  
% 7.76/1.48  fof(f10,plain,(
% 7.76/1.48    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 7.76/1.48    inference(nnf_transformation,[],[f4])).
% 7.76/1.48  
% 7.76/1.48  fof(f16,plain,(
% 7.76/1.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 7.76/1.48    inference(cnf_transformation,[],[f10])).
% 7.76/1.48  
% 7.76/1.48  fof(f3,axiom,(
% 7.76/1.48    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 7.76/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.76/1.48  
% 7.76/1.48  fof(f15,plain,(
% 7.76/1.48    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 7.76/1.48    inference(cnf_transformation,[],[f3])).
% 7.76/1.48  
% 7.76/1.48  fof(f17,plain,(
% 7.76/1.48    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 7.76/1.48    inference(cnf_transformation,[],[f10])).
% 7.76/1.48  
% 7.76/1.48  fof(f2,axiom,(
% 7.76/1.48    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 7.76/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.76/1.48  
% 7.76/1.48  fof(f7,plain,(
% 7.76/1.48    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 7.76/1.48    inference(ennf_transformation,[],[f2])).
% 7.76/1.48  
% 7.76/1.48  fof(f14,plain,(
% 7.76/1.48    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 7.76/1.48    inference(cnf_transformation,[],[f7])).
% 7.76/1.48  
% 7.76/1.48  fof(f1,axiom,(
% 7.76/1.48    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 7.76/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.76/1.48  
% 7.76/1.48  fof(f13,plain,(
% 7.76/1.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 7.76/1.48    inference(cnf_transformation,[],[f1])).
% 7.76/1.48  
% 7.76/1.48  fof(f20,plain,(
% 7.76/1.48    r1_xboole_0(sK2,sK3)),
% 7.76/1.48    inference(cnf_transformation,[],[f12])).
% 7.76/1.48  
% 7.76/1.48  fof(f19,plain,(
% 7.76/1.48    r1_xboole_0(sK1,sK3)),
% 7.76/1.48    inference(cnf_transformation,[],[f12])).
% 7.76/1.48  
% 7.76/1.48  fof(f18,plain,(
% 7.76/1.48    r1_xboole_0(sK0,sK3)),
% 7.76/1.48    inference(cnf_transformation,[],[f12])).
% 7.76/1.48  
% 7.76/1.48  cnf(c_5,negated_conjecture,
% 7.76/1.48      ( ~ r1_xboole_0(k2_xboole_0(k2_xboole_0(sK0,sK1),sK2),sK3) ),
% 7.76/1.48      inference(cnf_transformation,[],[f21]) ).
% 7.76/1.48  
% 7.76/1.48  cnf(c_99,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.76/1.48  
% 7.76/1.48  cnf(c_98,plain,( X0 = X0 ),theory(equality) ).
% 7.76/1.48  
% 7.76/1.48  cnf(c_816,plain,
% 7.76/1.48      ( X0 != X1 | X1 = X0 ),
% 7.76/1.48      inference(resolution,[status(thm)],[c_99,c_98]) ).
% 7.76/1.48  
% 7.76/1.48  cnf(c_4,plain,
% 7.76/1.48      ( ~ r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0 ),
% 7.76/1.48      inference(cnf_transformation,[],[f16]) ).
% 7.76/1.48  
% 7.76/1.48  cnf(c_1003,plain,
% 7.76/1.48      ( ~ r1_xboole_0(X0,X1) | X0 = k4_xboole_0(X0,X1) ),
% 7.76/1.48      inference(resolution,[status(thm)],[c_816,c_4]) ).
% 7.76/1.48  
% 7.76/1.48  cnf(c_1017,plain,
% 7.76/1.48      ( ~ r1_xboole_0(X0,X1) | X0 = X2 | X2 != k4_xboole_0(X0,X1) ),
% 7.76/1.48      inference(resolution,[status(thm)],[c_1003,c_99]) ).
% 7.76/1.48  
% 7.76/1.48  cnf(c_1641,plain,
% 7.76/1.48      ( ~ r1_xboole_0(X0,X1)
% 7.76/1.48      | ~ r1_xboole_0(k4_xboole_0(X0,X1),X2)
% 7.76/1.48      | X0 = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 7.76/1.48      inference(resolution,[status(thm)],[c_1017,c_4]) ).
% 7.76/1.48  
% 7.76/1.48  cnf(c_2,plain,
% 7.76/1.48      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 7.76/1.48      inference(cnf_transformation,[],[f15]) ).
% 7.76/1.48  
% 7.76/1.48  cnf(c_1001,plain,
% 7.76/1.48      ( k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 7.76/1.48      inference(resolution,[status(thm)],[c_816,c_2]) ).
% 7.76/1.48  
% 7.76/1.48  cnf(c_3682,plain,
% 7.76/1.48      ( X0 != k4_xboole_0(k4_xboole_0(X1,X2),X3)
% 7.76/1.48      | k4_xboole_0(X1,k2_xboole_0(X2,X3)) = X0 ),
% 7.76/1.48      inference(resolution,[status(thm)],[c_1001,c_99]) ).
% 7.76/1.48  
% 7.76/1.48  cnf(c_14627,plain,
% 7.76/1.48      ( ~ r1_xboole_0(X0,X1)
% 7.76/1.48      | ~ r1_xboole_0(k4_xboole_0(X0,X1),X2)
% 7.76/1.48      | k4_xboole_0(X0,k2_xboole_0(X1,X2)) = X0 ),
% 7.76/1.48      inference(resolution,[status(thm)],[c_1641,c_3682]) ).
% 7.76/1.48  
% 7.76/1.48  cnf(c_3,plain,
% 7.76/1.48      ( r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0 ),
% 7.76/1.48      inference(cnf_transformation,[],[f17]) ).
% 7.76/1.48  
% 7.76/1.48  cnf(c_27101,plain,
% 7.76/1.48      ( ~ r1_xboole_0(X0,X1)
% 7.76/1.48      | r1_xboole_0(X0,k2_xboole_0(X1,X2))
% 7.76/1.48      | ~ r1_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 7.76/1.48      inference(resolution,[status(thm)],[c_14627,c_3]) ).
% 7.76/1.48  
% 7.76/1.48  cnf(c_101,plain,
% 7.76/1.48      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.76/1.48      theory(equality) ).
% 7.76/1.48  
% 7.76/1.48  cnf(c_802,plain,
% 7.76/1.48      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,X1) | X2 != X0 ),
% 7.76/1.48      inference(resolution,[status(thm)],[c_98,c_101]) ).
% 7.76/1.48  
% 7.76/1.48  cnf(c_1152,plain,
% 7.76/1.48      ( ~ r1_xboole_0(X0,X1)
% 7.76/1.48      | ~ r1_xboole_0(X0,X2)
% 7.76/1.48      | r1_xboole_0(k4_xboole_0(X0,X2),X1) ),
% 7.76/1.48      inference(resolution,[status(thm)],[c_802,c_4]) ).
% 7.76/1.48  
% 7.76/1.48  cnf(c_27230,plain,
% 7.76/1.48      ( ~ r1_xboole_0(X0,X1)
% 7.76/1.48      | ~ r1_xboole_0(X0,X2)
% 7.76/1.48      | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 7.76/1.48      inference(resolution,[status(thm)],[c_27101,c_1152]) ).
% 7.76/1.48  
% 7.76/1.48  cnf(c_102,plain,
% 7.76/1.48      ( X0 != X1 | X2 != X3 | k4_xboole_0(X0,X2) = k4_xboole_0(X1,X3) ),
% 7.76/1.48      theory(equality) ).
% 7.76/1.48  
% 7.76/1.48  cnf(c_988,plain,
% 7.76/1.48      ( r1_xboole_0(k4_xboole_0(X0,X1),X2)
% 7.76/1.48      | X2 != X1
% 7.76/1.48      | k4_xboole_0(X0,X1) != X0 ),
% 7.76/1.48      inference(resolution,[status(thm)],[c_102,c_3]) ).
% 7.76/1.48  
% 7.76/1.48  cnf(c_2166,plain,
% 7.76/1.48      ( ~ r1_xboole_0(X0,X1)
% 7.76/1.48      | r1_xboole_0(k4_xboole_0(X0,X1),X2)
% 7.76/1.48      | X2 != X1 ),
% 7.76/1.48      inference(resolution,[status(thm)],[c_988,c_4]) ).
% 7.76/1.48  
% 7.76/1.48  cnf(c_1,plain,
% 7.76/1.48      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 7.76/1.48      inference(cnf_transformation,[],[f14]) ).
% 7.76/1.48  
% 7.76/1.48  cnf(c_2517,plain,
% 7.76/1.48      ( ~ r1_xboole_0(X0,X1)
% 7.76/1.48      | r1_xboole_0(X2,k4_xboole_0(X0,X1))
% 7.76/1.48      | X2 != X1 ),
% 7.76/1.48      inference(resolution,[status(thm)],[c_2166,c_1]) ).
% 7.76/1.48  
% 7.76/1.48  cnf(c_1161,plain,
% 7.76/1.48      ( ~ r1_xboole_0(X0,X1)
% 7.76/1.48      | r1_xboole_0(X0,X2)
% 7.76/1.48      | ~ r1_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 7.76/1.48      inference(resolution,[status(thm)],[c_802,c_1003]) ).
% 7.76/1.48  
% 7.76/1.48  cnf(c_2519,plain,
% 7.76/1.48      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X0,X2) | X2 != X1 ),
% 7.76/1.48      inference(resolution,[status(thm)],[c_2166,c_1161]) ).
% 7.76/1.48  
% 7.76/1.48  cnf(c_2625,plain,
% 7.76/1.48      ( ~ r1_xboole_0(X0,X1)
% 7.76/1.48      | r1_xboole_0(X2,X0)
% 7.76/1.48      | ~ r1_xboole_0(X2,k4_xboole_0(X0,X1)) ),
% 7.76/1.48      inference(resolution,[status(thm)],[c_2519,c_1003]) ).
% 7.76/1.48  
% 7.76/1.48  cnf(c_2830,plain,
% 7.76/1.48      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,X0) | X2 != X1 ),
% 7.76/1.48      inference(resolution,[status(thm)],[c_2517,c_2625]) ).
% 7.76/1.48  
% 7.76/1.48  cnf(c_0,plain,
% 7.76/1.48      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 7.76/1.48      inference(cnf_transformation,[],[f13]) ).
% 7.76/1.48  
% 7.76/1.48  cnf(c_2840,plain,
% 7.76/1.48      ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
% 7.76/1.48      | r1_xboole_0(k2_xboole_0(X2,X1),X0) ),
% 7.76/1.48      inference(resolution,[status(thm)],[c_2830,c_0]) ).
% 7.76/1.48  
% 7.76/1.48  cnf(c_27322,plain,
% 7.76/1.48      ( ~ r1_xboole_0(X0,X1)
% 7.76/1.48      | ~ r1_xboole_0(X0,X2)
% 7.76/1.48      | r1_xboole_0(k2_xboole_0(X2,X1),X0) ),
% 7.76/1.48      inference(resolution,[status(thm)],[c_27230,c_2840]) ).
% 7.76/1.48  
% 7.76/1.48  cnf(c_30093,plain,
% 7.76/1.48      ( ~ r1_xboole_0(sK3,k2_xboole_0(sK0,sK1))
% 7.76/1.48      | ~ r1_xboole_0(sK3,sK2) ),
% 7.76/1.48      inference(resolution,[status(thm)],[c_5,c_27322]) ).
% 7.76/1.48  
% 7.76/1.48  cnf(c_6,negated_conjecture,
% 7.76/1.48      ( r1_xboole_0(sK2,sK3) ),
% 7.76/1.48      inference(cnf_transformation,[],[f20]) ).
% 7.76/1.48  
% 7.76/1.48  cnf(c_345,plain,
% 7.76/1.48      ( r1_xboole_0(sK3,sK2) | ~ r1_xboole_0(sK2,sK3) ),
% 7.76/1.48      inference(instantiation,[status(thm)],[c_1]) ).
% 7.76/1.48  
% 7.76/1.48  cnf(c_30096,plain,
% 7.76/1.48      ( ~ r1_xboole_0(sK3,k2_xboole_0(sK0,sK1)) ),
% 7.76/1.48      inference(global_propositional_subsumption,
% 7.76/1.48                [status(thm)],
% 7.76/1.48                [c_30093,c_6,c_345]) ).
% 7.76/1.48  
% 7.76/1.48  cnf(c_668,plain,
% 7.76/1.48      ( ~ r1_xboole_0(X0,X1)
% 7.76/1.48      | ~ r1_xboole_0(X1,X2)
% 7.76/1.48      | r1_xboole_0(X3,k4_xboole_0(X1,X2))
% 7.76/1.48      | X3 != X0 ),
% 7.76/1.48      inference(resolution,[status(thm)],[c_101,c_4]) ).
% 7.76/1.48  
% 7.76/1.48  cnf(c_2199,plain,
% 7.76/1.48      ( ~ r1_xboole_0(X0,X1)
% 7.76/1.48      | ~ r1_xboole_0(X1,X2)
% 7.76/1.48      | r1_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 7.76/1.48      inference(resolution,[status(thm)],[c_668,c_98]) ).
% 7.76/1.48  
% 7.76/1.48  cnf(c_2360,plain,
% 7.76/1.48      ( ~ r1_xboole_0(X0,X1)
% 7.76/1.48      | ~ r1_xboole_0(X1,X2)
% 7.76/1.48      | r1_xboole_0(k4_xboole_0(X1,X2),X0) ),
% 7.76/1.48      inference(resolution,[status(thm)],[c_2199,c_1]) ).
% 7.76/1.48  
% 7.76/1.48  cnf(c_27276,plain,
% 7.76/1.48      ( ~ r1_xboole_0(X0,X1)
% 7.76/1.48      | ~ r1_xboole_0(X2,X0)
% 7.76/1.48      | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 7.76/1.48      inference(resolution,[status(thm)],[c_27101,c_2360]) ).
% 7.76/1.48  
% 7.76/1.48  cnf(c_30109,plain,
% 7.76/1.48      ( ~ r1_xboole_0(sK3,sK0) | ~ r1_xboole_0(sK1,sK3) ),
% 7.76/1.48      inference(resolution,[status(thm)],[c_30096,c_27276]) ).
% 7.76/1.48  
% 7.76/1.48  cnf(c_351,plain,
% 7.76/1.48      ( r1_xboole_0(sK3,sK0) | ~ r1_xboole_0(sK0,sK3) ),
% 7.76/1.48      inference(instantiation,[status(thm)],[c_1]) ).
% 7.76/1.48  
% 7.76/1.48  cnf(c_7,negated_conjecture,
% 7.76/1.48      ( r1_xboole_0(sK1,sK3) ),
% 7.76/1.48      inference(cnf_transformation,[],[f19]) ).
% 7.76/1.48  
% 7.76/1.48  cnf(c_8,negated_conjecture,
% 7.76/1.48      ( r1_xboole_0(sK0,sK3) ),
% 7.76/1.48      inference(cnf_transformation,[],[f18]) ).
% 7.76/1.48  
% 7.76/1.48  cnf(contradiction,plain,
% 7.76/1.48      ( $false ),
% 7.76/1.48      inference(minisat,[status(thm)],[c_30109,c_351,c_7,c_8]) ).
% 7.76/1.48  
% 7.76/1.48  
% 7.76/1.48  % SZS output end CNFRefutation for theBenchmark.p
% 7.76/1.48  
% 7.76/1.48  ------                               Statistics
% 7.76/1.48  
% 7.76/1.48  ------ Selected
% 7.76/1.48  
% 7.76/1.48  total_time:                             0.827
% 7.76/1.48  
%------------------------------------------------------------------------------
