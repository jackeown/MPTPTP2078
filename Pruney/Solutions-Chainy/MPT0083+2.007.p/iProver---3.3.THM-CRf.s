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
% DateTime   : Thu Dec  3 11:24:09 EST 2020

% Result     : Theorem 7.57s
% Output     : CNFRefutation 7.57s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 140 expanded)
%              Number of clauses        :   25 (  55 expanded)
%              Number of leaves         :   10 (  46 expanded)
%              Depth                    :   12
%              Number of atoms          :   98 ( 254 expanded)
%              Number of equality atoms :   33 ( 122 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f17,f22])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f29,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f16,f22,f22])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f18,f22])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f32,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f19,f22])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_xboole_0(X0,X1)
       => r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1))
      & r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f14,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1))
        & r1_xboole_0(X0,X1) )
   => ( ~ r1_xboole_0(k3_xboole_0(sK2,sK0),k3_xboole_0(sK2,sK1))
      & r1_xboole_0(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ~ r1_xboole_0(k3_xboole_0(sK2,sK0),k3_xboole_0(sK2,sK1))
    & r1_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f14])).

fof(f28,plain,(
    ~ r1_xboole_0(k3_xboole_0(sK2,sK0),k3_xboole_0(sK2,sK1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f35,plain,(
    ~ r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK1))) ),
    inference(definition_unfolding,[],[f28,f22,f22])).

fof(f27,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_112,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_111,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_976,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_112,c_111])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_2608,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(resolution,[status(thm)],[c_976,c_2])).

cnf(c_0,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_968,plain,
    ( X0 != k4_xboole_0(X1,k4_xboole_0(X1,X2))
    | k4_xboole_0(X2,k4_xboole_0(X2,X1)) = X0 ),
    inference(resolution,[status(thm)],[c_112,c_0])).

cnf(c_6983,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X1,k4_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2608,c_968])).

cnf(c_1,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_20677,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(resolution,[status(thm)],[c_6983,c_1])).

cnf(c_114,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_3,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_1197,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,k2_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X3))))
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_114,c_3])).

cnf(c_5824,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
    inference(resolution,[status(thm)],[c_1197,c_111])).

cnf(c_7,plain,
    ( r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_12463,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(resolution,[status(thm)],[c_5824,c_7])).

cnf(c_20706,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X0) ),
    inference(resolution,[status(thm)],[c_20677,c_12463])).

cnf(c_1211,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_114,c_111])).

cnf(c_1387,plain,
    ( ~ r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)
    | r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
    inference(resolution,[status(thm)],[c_1211,c_0])).

cnf(c_25780,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X1)),X0) ),
    inference(resolution,[status(thm)],[c_20706,c_1387])).

cnf(c_10,negated_conjecture,
    ( ~ r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK1))) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_32378,plain,
    ( ~ r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)),sK0) ),
    inference(resolution,[status(thm)],[c_25780,c_10])).

cnf(c_34162,plain,
    ( ~ r1_xboole_0(sK0,sK1) ),
    inference(resolution,[status(thm)],[c_32378,c_25780])).

cnf(c_11,negated_conjecture,
    ( r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f27])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_34162,c_11])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:26:36 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 7.57/1.50  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.57/1.50  
% 7.57/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.57/1.50  
% 7.57/1.50  ------  iProver source info
% 7.57/1.50  
% 7.57/1.50  git: date: 2020-06-30 10:37:57 +0100
% 7.57/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.57/1.50  git: non_committed_changes: false
% 7.57/1.50  git: last_make_outside_of_git: false
% 7.57/1.50  
% 7.57/1.50  ------ 
% 7.57/1.50  ------ Parsing...
% 7.57/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.57/1.50  
% 7.57/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.57/1.50  
% 7.57/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.57/1.50  
% 7.57/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.57/1.50  ------ Proving...
% 7.57/1.50  ------ Problem Properties 
% 7.57/1.50  
% 7.57/1.50  
% 7.57/1.50  clauses                                 12
% 7.57/1.50  conjectures                             2
% 7.57/1.50  EPR                                     1
% 7.57/1.50  Horn                                    12
% 7.57/1.50  unary                                   7
% 7.57/1.50  binary                                  4
% 7.57/1.50  lits                                    18
% 7.57/1.50  lits eq                                 7
% 7.57/1.50  fd_pure                                 0
% 7.57/1.50  fd_pseudo                               0
% 7.57/1.50  fd_cond                                 0
% 7.57/1.50  fd_pseudo_cond                          0
% 7.57/1.50  AC symbols                              0
% 7.57/1.50  
% 7.57/1.50  ------ Input Options Time Limit: Unbounded
% 7.57/1.50  
% 7.57/1.50  
% 7.57/1.50  ------ 
% 7.57/1.50  Current options:
% 7.57/1.50  ------ 
% 7.57/1.50  
% 7.57/1.50  
% 7.57/1.50  
% 7.57/1.50  
% 7.57/1.50  ------ Proving...
% 7.57/1.50  
% 7.57/1.50  
% 7.57/1.50  % SZS status Theorem for theBenchmark.p
% 7.57/1.50  
% 7.57/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.57/1.50  
% 7.57/1.50  fof(f2,axiom,(
% 7.57/1.50    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 7.57/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.57/1.50  
% 7.57/1.50  fof(f13,plain,(
% 7.57/1.50    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 7.57/1.50    inference(nnf_transformation,[],[f2])).
% 7.57/1.50  
% 7.57/1.50  fof(f17,plain,(
% 7.57/1.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 7.57/1.50    inference(cnf_transformation,[],[f13])).
% 7.57/1.50  
% 7.57/1.50  fof(f6,axiom,(
% 7.57/1.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 7.57/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.57/1.50  
% 7.57/1.50  fof(f22,plain,(
% 7.57/1.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 7.57/1.50    inference(cnf_transformation,[],[f6])).
% 7.57/1.50  
% 7.57/1.50  fof(f31,plain,(
% 7.57/1.50    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 7.57/1.50    inference(definition_unfolding,[],[f17,f22])).
% 7.57/1.50  
% 7.57/1.50  fof(f1,axiom,(
% 7.57/1.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 7.57/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.57/1.50  
% 7.57/1.50  fof(f16,plain,(
% 7.57/1.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 7.57/1.50    inference(cnf_transformation,[],[f1])).
% 7.57/1.50  
% 7.57/1.50  fof(f29,plain,(
% 7.57/1.50    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 7.57/1.50    inference(definition_unfolding,[],[f16,f22,f22])).
% 7.57/1.50  
% 7.57/1.50  fof(f18,plain,(
% 7.57/1.50    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 7.57/1.50    inference(cnf_transformation,[],[f13])).
% 7.57/1.50  
% 7.57/1.50  fof(f30,plain,(
% 7.57/1.50    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 7.57/1.50    inference(definition_unfolding,[],[f18,f22])).
% 7.57/1.50  
% 7.57/1.50  fof(f3,axiom,(
% 7.57/1.50    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 7.57/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.57/1.50  
% 7.57/1.50  fof(f19,plain,(
% 7.57/1.50    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 7.57/1.50    inference(cnf_transformation,[],[f3])).
% 7.57/1.50  
% 7.57/1.50  fof(f32,plain,(
% 7.57/1.50    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0) )),
% 7.57/1.50    inference(definition_unfolding,[],[f19,f22])).
% 7.57/1.50  
% 7.57/1.50  fof(f8,axiom,(
% 7.57/1.50    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 7.57/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.57/1.50  
% 7.57/1.50  fof(f11,plain,(
% 7.57/1.50    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 7.57/1.50    inference(ennf_transformation,[],[f8])).
% 7.57/1.50  
% 7.57/1.50  fof(f26,plain,(
% 7.57/1.50    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | r1_xboole_0(X0,X2)) )),
% 7.57/1.50    inference(cnf_transformation,[],[f11])).
% 7.57/1.50  
% 7.57/1.50  fof(f9,conjecture,(
% 7.57/1.50    ! [X0,X1,X2] : (r1_xboole_0(X0,X1) => r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)))),
% 7.57/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.57/1.50  
% 7.57/1.50  fof(f10,negated_conjecture,(
% 7.57/1.50    ~! [X0,X1,X2] : (r1_xboole_0(X0,X1) => r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)))),
% 7.57/1.50    inference(negated_conjecture,[],[f9])).
% 7.57/1.50  
% 7.57/1.50  fof(f12,plain,(
% 7.57/1.50    ? [X0,X1,X2] : (~r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)) & r1_xboole_0(X0,X1))),
% 7.57/1.50    inference(ennf_transformation,[],[f10])).
% 7.57/1.50  
% 7.57/1.50  fof(f14,plain,(
% 7.57/1.50    ? [X0,X1,X2] : (~r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)) & r1_xboole_0(X0,X1)) => (~r1_xboole_0(k3_xboole_0(sK2,sK0),k3_xboole_0(sK2,sK1)) & r1_xboole_0(sK0,sK1))),
% 7.57/1.50    introduced(choice_axiom,[])).
% 7.57/1.50  
% 7.57/1.50  fof(f15,plain,(
% 7.57/1.50    ~r1_xboole_0(k3_xboole_0(sK2,sK0),k3_xboole_0(sK2,sK1)) & r1_xboole_0(sK0,sK1)),
% 7.57/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f14])).
% 7.57/1.50  
% 7.57/1.50  fof(f28,plain,(
% 7.57/1.50    ~r1_xboole_0(k3_xboole_0(sK2,sK0),k3_xboole_0(sK2,sK1))),
% 7.57/1.50    inference(cnf_transformation,[],[f15])).
% 7.57/1.50  
% 7.57/1.50  fof(f35,plain,(
% 7.57/1.50    ~r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)))),
% 7.57/1.50    inference(definition_unfolding,[],[f28,f22,f22])).
% 7.57/1.50  
% 7.57/1.50  fof(f27,plain,(
% 7.57/1.50    r1_xboole_0(sK0,sK1)),
% 7.57/1.50    inference(cnf_transformation,[],[f15])).
% 7.57/1.50  
% 7.57/1.50  cnf(c_112,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.57/1.50  
% 7.57/1.50  cnf(c_111,plain,( X0 = X0 ),theory(equality) ).
% 7.57/1.50  
% 7.57/1.50  cnf(c_976,plain,
% 7.57/1.50      ( X0 != X1 | X1 = X0 ),
% 7.57/1.50      inference(resolution,[status(thm)],[c_112,c_111]) ).
% 7.57/1.50  
% 7.57/1.50  cnf(c_2,plain,
% 7.57/1.50      ( ~ r1_xboole_0(X0,X1)
% 7.57/1.50      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 7.57/1.50      inference(cnf_transformation,[],[f31]) ).
% 7.57/1.50  
% 7.57/1.50  cnf(c_2608,plain,
% 7.57/1.50      ( ~ r1_xboole_0(X0,X1)
% 7.57/1.50      | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 7.57/1.50      inference(resolution,[status(thm)],[c_976,c_2]) ).
% 7.57/1.50  
% 7.57/1.50  cnf(c_0,plain,
% 7.57/1.50      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 7.57/1.50      inference(cnf_transformation,[],[f29]) ).
% 7.57/1.50  
% 7.57/1.50  cnf(c_968,plain,
% 7.57/1.50      ( X0 != k4_xboole_0(X1,k4_xboole_0(X1,X2))
% 7.57/1.50      | k4_xboole_0(X2,k4_xboole_0(X2,X1)) = X0 ),
% 7.57/1.50      inference(resolution,[status(thm)],[c_112,c_0]) ).
% 7.57/1.50  
% 7.57/1.50  cnf(c_6983,plain,
% 7.57/1.50      ( ~ r1_xboole_0(X0,X1)
% 7.57/1.50      | k4_xboole_0(X1,k4_xboole_0(X1,X0)) = k1_xboole_0 ),
% 7.57/1.50      inference(resolution,[status(thm)],[c_2608,c_968]) ).
% 7.57/1.50  
% 7.57/1.50  cnf(c_1,plain,
% 7.57/1.50      ( r1_xboole_0(X0,X1)
% 7.57/1.50      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
% 7.57/1.50      inference(cnf_transformation,[],[f30]) ).
% 7.57/1.50  
% 7.57/1.50  cnf(c_20677,plain,
% 7.57/1.50      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 7.57/1.50      inference(resolution,[status(thm)],[c_6983,c_1]) ).
% 7.57/1.50  
% 7.57/1.50  cnf(c_114,plain,
% 7.57/1.50      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.57/1.50      theory(equality) ).
% 7.57/1.50  
% 7.57/1.50  cnf(c_3,plain,
% 7.57/1.50      ( k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
% 7.57/1.50      inference(cnf_transformation,[],[f32]) ).
% 7.57/1.50  
% 7.57/1.50  cnf(c_1197,plain,
% 7.57/1.50      ( ~ r1_xboole_0(X0,X1)
% 7.57/1.50      | r1_xboole_0(X2,k2_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X3))))
% 7.57/1.50      | X2 != X0 ),
% 7.57/1.50      inference(resolution,[status(thm)],[c_114,c_3]) ).
% 7.57/1.50  
% 7.57/1.50  cnf(c_5824,plain,
% 7.57/1.50      ( ~ r1_xboole_0(X0,X1)
% 7.57/1.50      | r1_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
% 7.57/1.50      inference(resolution,[status(thm)],[c_1197,c_111]) ).
% 7.57/1.50  
% 7.57/1.50  cnf(c_7,plain,
% 7.57/1.50      ( r1_xboole_0(X0,X1) | ~ r1_xboole_0(X0,k2_xboole_0(X2,X1)) ),
% 7.57/1.50      inference(cnf_transformation,[],[f26]) ).
% 7.57/1.50  
% 7.57/1.50  cnf(c_12463,plain,
% 7.57/1.50      ( ~ r1_xboole_0(X0,X1)
% 7.57/1.50      | r1_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
% 7.57/1.50      inference(resolution,[status(thm)],[c_5824,c_7]) ).
% 7.57/1.50  
% 7.57/1.50  cnf(c_20706,plain,
% 7.57/1.50      ( ~ r1_xboole_0(X0,X1)
% 7.57/1.50      | r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X0) ),
% 7.57/1.50      inference(resolution,[status(thm)],[c_20677,c_12463]) ).
% 7.57/1.50  
% 7.57/1.50  cnf(c_1211,plain,
% 7.57/1.50      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,X1) | X2 != X0 ),
% 7.57/1.50      inference(resolution,[status(thm)],[c_114,c_111]) ).
% 7.57/1.50  
% 7.57/1.50  cnf(c_1387,plain,
% 7.57/1.50      ( ~ r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)
% 7.57/1.50      | r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
% 7.57/1.50      inference(resolution,[status(thm)],[c_1211,c_0]) ).
% 7.57/1.50  
% 7.57/1.50  cnf(c_25780,plain,
% 7.57/1.50      ( ~ r1_xboole_0(X0,X1)
% 7.57/1.50      | r1_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X1)),X0) ),
% 7.57/1.50      inference(resolution,[status(thm)],[c_20706,c_1387]) ).
% 7.57/1.50  
% 7.57/1.50  cnf(c_10,negated_conjecture,
% 7.57/1.50      ( ~ r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK1))) ),
% 7.57/1.50      inference(cnf_transformation,[],[f35]) ).
% 7.57/1.50  
% 7.57/1.50  cnf(c_32378,plain,
% 7.57/1.50      ( ~ r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)),sK0) ),
% 7.57/1.50      inference(resolution,[status(thm)],[c_25780,c_10]) ).
% 7.57/1.50  
% 7.57/1.50  cnf(c_34162,plain,
% 7.57/1.50      ( ~ r1_xboole_0(sK0,sK1) ),
% 7.57/1.50      inference(resolution,[status(thm)],[c_32378,c_25780]) ).
% 7.57/1.50  
% 7.57/1.50  cnf(c_11,negated_conjecture,
% 7.57/1.50      ( r1_xboole_0(sK0,sK1) ),
% 7.57/1.50      inference(cnf_transformation,[],[f27]) ).
% 7.57/1.50  
% 7.57/1.50  cnf(contradiction,plain,
% 7.57/1.50      ( $false ),
% 7.57/1.50      inference(minisat,[status(thm)],[c_34162,c_11]) ).
% 7.57/1.50  
% 7.57/1.50  
% 7.57/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.57/1.50  
% 7.57/1.50  ------                               Statistics
% 7.57/1.50  
% 7.57/1.50  ------ Selected
% 7.57/1.50  
% 7.57/1.50  total_time:                             0.942
% 7.57/1.50  
%------------------------------------------------------------------------------
