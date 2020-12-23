%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:24:09 EST 2020

% Result     : Theorem 3.61s
% Output     : CNFRefutation 3.61s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 264 expanded)
%              Number of clauses        :   27 ( 103 expanded)
%              Number of leaves         :   10 (  86 expanded)
%              Depth                    :   14
%              Number of atoms          :  100 ( 473 expanded)
%              Number of equality atoms :   32 ( 270 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f38,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f22,f30,f30])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f23,f30])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f24,f30])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f43,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f27,f30])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_xboole_0(X0,X1)
       => r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1))
      & r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f20,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1))
        & r1_xboole_0(X0,X1) )
   => ( ~ r1_xboole_0(k3_xboole_0(sK3,sK1),k3_xboole_0(sK3,sK2))
      & r1_xboole_0(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ~ r1_xboole_0(k3_xboole_0(sK3,sK1),k3_xboole_0(sK3,sK2))
    & r1_xboole_0(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f16,f20])).

fof(f37,plain,(
    ~ r1_xboole_0(k3_xboole_0(sK3,sK1),k3_xboole_0(sK3,sK2)) ),
    inference(cnf_transformation,[],[f21])).

fof(f48,plain,(
    ~ r1_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)),k4_xboole_0(sK3,k4_xboole_0(sK3,sK2))) ),
    inference(definition_unfolding,[],[f37,f30,f30])).

fof(f36,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_159,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_0,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1327,plain,
    ( X0 != k4_xboole_0(X1,k4_xboole_0(X1,X2))
    | k4_xboole_0(X2,k4_xboole_0(X2,X1)) = X0 ),
    inference(resolution,[status(thm)],[c_159,c_0])).

cnf(c_158,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1335,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_159,c_158])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_2823,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(resolution,[status(thm)],[c_1335,c_2])).

cnf(c_5062,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X1,k4_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1327,c_2823])).

cnf(c_1,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_5991,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(resolution,[status(thm)],[c_5062,c_1])).

cnf(c_161,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1516,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_161,c_158])).

cnf(c_5,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1693,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X2))),X1) ),
    inference(resolution,[status(thm)],[c_1516,c_5])).

cnf(c_6024,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X2)))) ),
    inference(resolution,[status(thm)],[c_5991,c_1693])).

cnf(c_10,plain,
    ( r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_15818,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2))) ),
    inference(resolution,[status(thm)],[c_6024,c_10])).

cnf(c_15830,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X2)),X1) ),
    inference(resolution,[status(thm)],[c_15818,c_5991])).

cnf(c_1687,plain,
    ( ~ r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)
    | r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
    inference(resolution,[status(thm)],[c_1516,c_0])).

cnf(c_16616,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X0)),X1) ),
    inference(resolution,[status(thm)],[c_15830,c_1687])).

cnf(c_17240,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X0))) ),
    inference(resolution,[status(thm)],[c_16616,c_5991])).

cnf(c_13,negated_conjecture,
    ( ~ r1_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)),k4_xboole_0(sK3,k4_xboole_0(sK3,sK2))) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_17250,plain,
    ( ~ r1_xboole_0(sK1,k4_xboole_0(sK3,k4_xboole_0(sK3,sK2))) ),
    inference(resolution,[status(thm)],[c_16616,c_13])).

cnf(c_18156,plain,
    ( ~ r1_xboole_0(sK2,sK1) ),
    inference(resolution,[status(thm)],[c_17240,c_17250])).

cnf(c_14,negated_conjecture,
    ( r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_6014,plain,
    ( r1_xboole_0(sK2,sK1) ),
    inference(resolution,[status(thm)],[c_5991,c_14])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_18156,c_6014])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 16:47:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.61/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.61/0.99  
% 3.61/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.61/0.99  
% 3.61/0.99  ------  iProver source info
% 3.61/0.99  
% 3.61/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.61/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.61/0.99  git: non_committed_changes: false
% 3.61/0.99  git: last_make_outside_of_git: false
% 3.61/0.99  
% 3.61/0.99  ------ 
% 3.61/0.99  ------ Parsing...
% 3.61/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.61/0.99  
% 3.61/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.61/0.99  
% 3.61/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.61/0.99  
% 3.61/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.61/0.99  ------ Proving...
% 3.61/0.99  ------ Problem Properties 
% 3.61/0.99  
% 3.61/0.99  
% 3.61/0.99  clauses                                 15
% 3.61/0.99  conjectures                             2
% 3.61/0.99  EPR                                     1
% 3.61/0.99  Horn                                    14
% 3.61/0.99  unary                                   8
% 3.61/0.99  binary                                  6
% 3.61/0.99  lits                                    23
% 3.61/0.99  lits eq                                 8
% 3.61/0.99  fd_pure                                 0
% 3.61/0.99  fd_pseudo                               0
% 3.61/0.99  fd_cond                                 0
% 3.61/0.99  fd_pseudo_cond                          0
% 3.61/0.99  AC symbols                              0
% 3.61/0.99  
% 3.61/0.99  ------ Input Options Time Limit: Unbounded
% 3.61/0.99  
% 3.61/0.99  
% 3.61/0.99  ------ 
% 3.61/0.99  Current options:
% 3.61/0.99  ------ 
% 3.61/0.99  
% 3.61/0.99  
% 3.61/0.99  
% 3.61/0.99  
% 3.61/0.99  ------ Proving...
% 3.61/0.99  
% 3.61/0.99  
% 3.61/0.99  % SZS status Theorem for theBenchmark.p
% 3.61/0.99  
% 3.61/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.61/0.99  
% 3.61/0.99  fof(f1,axiom,(
% 3.61/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.61/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.61/0.99  
% 3.61/0.99  fof(f22,plain,(
% 3.61/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.61/0.99    inference(cnf_transformation,[],[f1])).
% 3.61/0.99  
% 3.61/0.99  fof(f7,axiom,(
% 3.61/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.61/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.61/0.99  
% 3.61/0.99  fof(f30,plain,(
% 3.61/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.61/0.99    inference(cnf_transformation,[],[f7])).
% 3.61/0.99  
% 3.61/0.99  fof(f38,plain,(
% 3.61/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 3.61/0.99    inference(definition_unfolding,[],[f22,f30,f30])).
% 3.61/0.99  
% 3.61/0.99  fof(f2,axiom,(
% 3.61/0.99    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 3.61/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.61/0.99  
% 3.61/0.99  fof(f17,plain,(
% 3.61/0.99    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 3.61/0.99    inference(nnf_transformation,[],[f2])).
% 3.61/0.99  
% 3.61/0.99  fof(f23,plain,(
% 3.61/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 3.61/0.99    inference(cnf_transformation,[],[f17])).
% 3.61/0.99  
% 3.61/0.99  fof(f40,plain,(
% 3.61/0.99    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 3.61/0.99    inference(definition_unfolding,[],[f23,f30])).
% 3.61/0.99  
% 3.61/0.99  fof(f24,plain,(
% 3.61/0.99    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 3.61/0.99    inference(cnf_transformation,[],[f17])).
% 3.61/0.99  
% 3.61/0.99  fof(f39,plain,(
% 3.61/0.99    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.61/0.99    inference(definition_unfolding,[],[f24,f30])).
% 3.61/0.99  
% 3.61/0.99  fof(f4,axiom,(
% 3.61/0.99    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 3.61/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.61/0.99  
% 3.61/0.99  fof(f27,plain,(
% 3.61/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 3.61/0.99    inference(cnf_transformation,[],[f4])).
% 3.61/0.99  
% 3.61/0.99  fof(f43,plain,(
% 3.61/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0) )),
% 3.61/0.99    inference(definition_unfolding,[],[f27,f30])).
% 3.61/0.99  
% 3.61/0.99  fof(f10,axiom,(
% 3.61/0.99    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 3.61/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.61/0.99  
% 3.61/0.99  fof(f15,plain,(
% 3.61/0.99    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 3.61/0.99    inference(ennf_transformation,[],[f10])).
% 3.61/0.99  
% 3.61/0.99  fof(f35,plain,(
% 3.61/0.99    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | r1_xboole_0(X0,X2)) )),
% 3.61/0.99    inference(cnf_transformation,[],[f15])).
% 3.61/0.99  
% 3.61/0.99  fof(f11,conjecture,(
% 3.61/0.99    ! [X0,X1,X2] : (r1_xboole_0(X0,X1) => r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)))),
% 3.61/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.61/0.99  
% 3.61/0.99  fof(f12,negated_conjecture,(
% 3.61/0.99    ~! [X0,X1,X2] : (r1_xboole_0(X0,X1) => r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)))),
% 3.61/0.99    inference(negated_conjecture,[],[f11])).
% 3.61/0.99  
% 3.61/0.99  fof(f16,plain,(
% 3.61/0.99    ? [X0,X1,X2] : (~r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)) & r1_xboole_0(X0,X1))),
% 3.61/0.99    inference(ennf_transformation,[],[f12])).
% 3.61/0.99  
% 3.61/0.99  fof(f20,plain,(
% 3.61/0.99    ? [X0,X1,X2] : (~r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)) & r1_xboole_0(X0,X1)) => (~r1_xboole_0(k3_xboole_0(sK3,sK1),k3_xboole_0(sK3,sK2)) & r1_xboole_0(sK1,sK2))),
% 3.61/0.99    introduced(choice_axiom,[])).
% 3.61/0.99  
% 3.61/0.99  fof(f21,plain,(
% 3.61/0.99    ~r1_xboole_0(k3_xboole_0(sK3,sK1),k3_xboole_0(sK3,sK2)) & r1_xboole_0(sK1,sK2)),
% 3.61/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f16,f20])).
% 3.61/0.99  
% 3.61/0.99  fof(f37,plain,(
% 3.61/0.99    ~r1_xboole_0(k3_xboole_0(sK3,sK1),k3_xboole_0(sK3,sK2))),
% 3.61/0.99    inference(cnf_transformation,[],[f21])).
% 3.61/0.99  
% 3.61/0.99  fof(f48,plain,(
% 3.61/0.99    ~r1_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)),k4_xboole_0(sK3,k4_xboole_0(sK3,sK2)))),
% 3.61/0.99    inference(definition_unfolding,[],[f37,f30,f30])).
% 3.61/0.99  
% 3.61/0.99  fof(f36,plain,(
% 3.61/0.99    r1_xboole_0(sK1,sK2)),
% 3.61/0.99    inference(cnf_transformation,[],[f21])).
% 3.61/0.99  
% 3.61/0.99  cnf(c_159,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_0,plain,
% 3.61/0.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 3.61/0.99      inference(cnf_transformation,[],[f38]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_1327,plain,
% 3.61/0.99      ( X0 != k4_xboole_0(X1,k4_xboole_0(X1,X2))
% 3.61/0.99      | k4_xboole_0(X2,k4_xboole_0(X2,X1)) = X0 ),
% 3.61/0.99      inference(resolution,[status(thm)],[c_159,c_0]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_158,plain,( X0 = X0 ),theory(equality) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_1335,plain,
% 3.61/0.99      ( X0 != X1 | X1 = X0 ),
% 3.61/0.99      inference(resolution,[status(thm)],[c_159,c_158]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_2,plain,
% 3.61/0.99      ( ~ r1_xboole_0(X0,X1)
% 3.61/0.99      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 3.61/0.99      inference(cnf_transformation,[],[f40]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_2823,plain,
% 3.61/0.99      ( ~ r1_xboole_0(X0,X1)
% 3.61/0.99      | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 3.61/0.99      inference(resolution,[status(thm)],[c_1335,c_2]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_5062,plain,
% 3.61/0.99      ( ~ r1_xboole_0(X0,X1)
% 3.61/0.99      | k4_xboole_0(X1,k4_xboole_0(X1,X0)) = k1_xboole_0 ),
% 3.61/0.99      inference(resolution,[status(thm)],[c_1327,c_2823]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_1,plain,
% 3.61/0.99      ( r1_xboole_0(X0,X1)
% 3.61/0.99      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
% 3.61/0.99      inference(cnf_transformation,[],[f39]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_5991,plain,
% 3.61/0.99      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 3.61/0.99      inference(resolution,[status(thm)],[c_5062,c_1]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_161,plain,
% 3.61/0.99      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.61/0.99      theory(equality) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_1516,plain,
% 3.61/0.99      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,X1) | X2 != X0 ),
% 3.61/0.99      inference(resolution,[status(thm)],[c_161,c_158]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_5,plain,
% 3.61/0.99      ( k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
% 3.61/0.99      inference(cnf_transformation,[],[f43]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_1693,plain,
% 3.61/0.99      ( ~ r1_xboole_0(X0,X1)
% 3.61/0.99      | r1_xboole_0(k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X2))),X1) ),
% 3.61/0.99      inference(resolution,[status(thm)],[c_1516,c_5]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_6024,plain,
% 3.61/0.99      ( ~ r1_xboole_0(X0,X1)
% 3.61/0.99      | r1_xboole_0(X1,k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X2)))) ),
% 3.61/0.99      inference(resolution,[status(thm)],[c_5991,c_1693]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_10,plain,
% 3.61/0.99      ( r1_xboole_0(X0,X1) | ~ r1_xboole_0(X0,k2_xboole_0(X2,X1)) ),
% 3.61/0.99      inference(cnf_transformation,[],[f35]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_15818,plain,
% 3.61/0.99      ( ~ r1_xboole_0(X0,X1)
% 3.61/0.99      | r1_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2))) ),
% 3.61/0.99      inference(resolution,[status(thm)],[c_6024,c_10]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_15830,plain,
% 3.61/0.99      ( ~ r1_xboole_0(X0,X1)
% 3.61/0.99      | r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X2)),X1) ),
% 3.61/0.99      inference(resolution,[status(thm)],[c_15818,c_5991]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_1687,plain,
% 3.61/0.99      ( ~ r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)
% 3.61/0.99      | r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
% 3.61/0.99      inference(resolution,[status(thm)],[c_1516,c_0]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_16616,plain,
% 3.61/0.99      ( ~ r1_xboole_0(X0,X1)
% 3.61/0.99      | r1_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X0)),X1) ),
% 3.61/0.99      inference(resolution,[status(thm)],[c_15830,c_1687]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_17240,plain,
% 3.61/0.99      ( ~ r1_xboole_0(X0,X1)
% 3.61/0.99      | r1_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X0))) ),
% 3.61/0.99      inference(resolution,[status(thm)],[c_16616,c_5991]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_13,negated_conjecture,
% 3.61/0.99      ( ~ r1_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)),k4_xboole_0(sK3,k4_xboole_0(sK3,sK2))) ),
% 3.61/0.99      inference(cnf_transformation,[],[f48]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_17250,plain,
% 3.61/0.99      ( ~ r1_xboole_0(sK1,k4_xboole_0(sK3,k4_xboole_0(sK3,sK2))) ),
% 3.61/0.99      inference(resolution,[status(thm)],[c_16616,c_13]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_18156,plain,
% 3.61/0.99      ( ~ r1_xboole_0(sK2,sK1) ),
% 3.61/0.99      inference(resolution,[status(thm)],[c_17240,c_17250]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_14,negated_conjecture,
% 3.61/0.99      ( r1_xboole_0(sK1,sK2) ),
% 3.61/0.99      inference(cnf_transformation,[],[f36]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_6014,plain,
% 3.61/0.99      ( r1_xboole_0(sK2,sK1) ),
% 3.61/0.99      inference(resolution,[status(thm)],[c_5991,c_14]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(contradiction,plain,
% 3.61/0.99      ( $false ),
% 3.61/0.99      inference(minisat,[status(thm)],[c_18156,c_6014]) ).
% 3.61/0.99  
% 3.61/0.99  
% 3.61/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.61/0.99  
% 3.61/0.99  ------                               Statistics
% 3.61/0.99  
% 3.61/0.99  ------ Selected
% 3.61/0.99  
% 3.61/0.99  total_time:                             0.411
% 3.61/0.99  
%------------------------------------------------------------------------------
