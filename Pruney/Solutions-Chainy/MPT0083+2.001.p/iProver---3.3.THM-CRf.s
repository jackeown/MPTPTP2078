%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:24:08 EST 2020

% Result     : Theorem 3.60s
% Output     : CNFRefutation 3.60s
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
fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f36,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f22,f25])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f33,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f19,f25,f25])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f20,f25])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f21,f25])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_xboole_0(X0,X1)
       => r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1))
      & r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f16,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1))
        & r1_xboole_0(X0,X1) )
   => ( ~ r1_xboole_0(k3_xboole_0(sK2,sK0),k3_xboole_0(sK2,sK1))
      & r1_xboole_0(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ~ r1_xboole_0(k3_xboole_0(sK2,sK0),k3_xboole_0(sK2,sK1))
    & r1_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f16])).

fof(f32,plain,(
    ~ r1_xboole_0(k3_xboole_0(sK2,sK0),k3_xboole_0(sK2,sK1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f41,plain,(
    ~ r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK1))) ),
    inference(definition_unfolding,[],[f32,f25,f25])).

fof(f31,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_121,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_4,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1222,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,k2_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X3))))
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_121,c_4])).

cnf(c_117,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_7421,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
    inference(resolution,[status(thm)],[c_1222,c_117])).

cnf(c_9,plain,
    ( r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_16314,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(resolution,[status(thm)],[c_7421,c_9])).

cnf(c_118,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_976,plain,
    ( X0 != k4_xboole_0(X1,k4_xboole_0(X1,X2))
    | k4_xboole_0(X2,k4_xboole_0(X2,X1)) = X0 ),
    inference(resolution,[status(thm)],[c_118,c_1])).

cnf(c_984,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_118,c_117])).

cnf(c_3,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_2540,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(resolution,[status(thm)],[c_984,c_3])).

cnf(c_4794,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X1,k4_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_976,c_2540])).

cnf(c_2,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_6158,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(resolution,[status(thm)],[c_4794,c_2])).

cnf(c_17445,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X0) ),
    inference(resolution,[status(thm)],[c_16314,c_6158])).

cnf(c_1240,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_121,c_117])).

cnf(c_1252,plain,
    ( ~ r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)
    | r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
    inference(resolution,[status(thm)],[c_1240,c_1])).

cnf(c_18123,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X1)),X0) ),
    inference(resolution,[status(thm)],[c_17445,c_1252])).

cnf(c_12,negated_conjecture,
    ( ~ r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK1))) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_19246,plain,
    ( ~ r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)),sK0) ),
    inference(resolution,[status(thm)],[c_18123,c_12])).

cnf(c_19266,plain,
    ( ~ r1_xboole_0(sK0,sK1) ),
    inference(resolution,[status(thm)],[c_19246,c_18123])).

cnf(c_13,negated_conjecture,
    ( r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f31])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_19266,c_13])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:29:30 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.60/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.60/0.99  
% 3.60/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.60/0.99  
% 3.60/0.99  ------  iProver source info
% 3.60/0.99  
% 3.60/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.60/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.60/0.99  git: non_committed_changes: false
% 3.60/0.99  git: last_make_outside_of_git: false
% 3.60/0.99  
% 3.60/0.99  ------ 
% 3.60/0.99  ------ Parsing...
% 3.60/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.60/0.99  
% 3.60/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.60/0.99  
% 3.60/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.60/0.99  
% 3.60/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.60/0.99  ------ Proving...
% 3.60/0.99  ------ Problem Properties 
% 3.60/0.99  
% 3.60/0.99  
% 3.60/0.99  clauses                                 14
% 3.60/0.99  conjectures                             2
% 3.60/0.99  EPR                                     1
% 3.60/0.99  Horn                                    14
% 3.60/0.99  unary                                   9
% 3.60/0.99  binary                                  4
% 3.60/0.99  lits                                    20
% 3.60/0.99  lits eq                                 9
% 3.60/0.99  fd_pure                                 0
% 3.60/0.99  fd_pseudo                               0
% 3.60/0.99  fd_cond                                 0
% 3.60/0.99  fd_pseudo_cond                          0
% 3.60/0.99  AC symbols                              0
% 3.60/0.99  
% 3.60/0.99  ------ Input Options Time Limit: Unbounded
% 3.60/0.99  
% 3.60/0.99  
% 3.60/0.99  ------ 
% 3.60/0.99  Current options:
% 3.60/0.99  ------ 
% 3.60/0.99  
% 3.60/0.99  
% 3.60/0.99  
% 3.60/0.99  
% 3.60/0.99  ------ Proving...
% 3.60/0.99  
% 3.60/0.99  
% 3.60/0.99  % SZS status Theorem for theBenchmark.p
% 3.60/0.99  
% 3.60/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.60/0.99  
% 3.60/0.99  fof(f4,axiom,(
% 3.60/0.99    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 3.60/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.60/0.99  
% 3.60/0.99  fof(f22,plain,(
% 3.60/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 3.60/0.99    inference(cnf_transformation,[],[f4])).
% 3.60/0.99  
% 3.60/0.99  fof(f7,axiom,(
% 3.60/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.60/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.60/0.99  
% 3.60/0.99  fof(f25,plain,(
% 3.60/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.60/0.99    inference(cnf_transformation,[],[f7])).
% 3.60/0.99  
% 3.60/0.99  fof(f36,plain,(
% 3.60/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0) )),
% 3.60/0.99    inference(definition_unfolding,[],[f22,f25])).
% 3.60/0.99  
% 3.60/0.99  fof(f10,axiom,(
% 3.60/0.99    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 3.60/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.60/0.99  
% 3.60/0.99  fof(f13,plain,(
% 3.60/0.99    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 3.60/0.99    inference(ennf_transformation,[],[f10])).
% 3.60/0.99  
% 3.60/0.99  fof(f30,plain,(
% 3.60/0.99    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | r1_xboole_0(X0,X2)) )),
% 3.60/0.99    inference(cnf_transformation,[],[f13])).
% 3.60/0.99  
% 3.60/0.99  fof(f2,axiom,(
% 3.60/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.60/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.60/0.99  
% 3.60/0.99  fof(f19,plain,(
% 3.60/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.60/0.99    inference(cnf_transformation,[],[f2])).
% 3.60/0.99  
% 3.60/0.99  fof(f33,plain,(
% 3.60/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 3.60/0.99    inference(definition_unfolding,[],[f19,f25,f25])).
% 3.60/0.99  
% 3.60/0.99  fof(f3,axiom,(
% 3.60/0.99    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 3.60/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.60/0.99  
% 3.60/0.99  fof(f15,plain,(
% 3.60/0.99    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 3.60/0.99    inference(nnf_transformation,[],[f3])).
% 3.60/0.99  
% 3.60/0.99  fof(f20,plain,(
% 3.60/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 3.60/0.99    inference(cnf_transformation,[],[f15])).
% 3.60/0.99  
% 3.60/0.99  fof(f35,plain,(
% 3.60/0.99    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 3.60/0.99    inference(definition_unfolding,[],[f20,f25])).
% 3.60/0.99  
% 3.60/0.99  fof(f21,plain,(
% 3.60/0.99    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 3.60/0.99    inference(cnf_transformation,[],[f15])).
% 3.60/0.99  
% 3.60/0.99  fof(f34,plain,(
% 3.60/0.99    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.60/0.99    inference(definition_unfolding,[],[f21,f25])).
% 3.60/0.99  
% 3.60/0.99  fof(f11,conjecture,(
% 3.60/0.99    ! [X0,X1,X2] : (r1_xboole_0(X0,X1) => r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)))),
% 3.60/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.60/0.99  
% 3.60/0.99  fof(f12,negated_conjecture,(
% 3.60/0.99    ~! [X0,X1,X2] : (r1_xboole_0(X0,X1) => r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)))),
% 3.60/0.99    inference(negated_conjecture,[],[f11])).
% 3.60/0.99  
% 3.60/0.99  fof(f14,plain,(
% 3.60/0.99    ? [X0,X1,X2] : (~r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)) & r1_xboole_0(X0,X1))),
% 3.60/0.99    inference(ennf_transformation,[],[f12])).
% 3.60/0.99  
% 3.60/0.99  fof(f16,plain,(
% 3.60/0.99    ? [X0,X1,X2] : (~r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)) & r1_xboole_0(X0,X1)) => (~r1_xboole_0(k3_xboole_0(sK2,sK0),k3_xboole_0(sK2,sK1)) & r1_xboole_0(sK0,sK1))),
% 3.60/0.99    introduced(choice_axiom,[])).
% 3.60/0.99  
% 3.60/0.99  fof(f17,plain,(
% 3.60/0.99    ~r1_xboole_0(k3_xboole_0(sK2,sK0),k3_xboole_0(sK2,sK1)) & r1_xboole_0(sK0,sK1)),
% 3.60/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f16])).
% 3.60/0.99  
% 3.60/0.99  fof(f32,plain,(
% 3.60/0.99    ~r1_xboole_0(k3_xboole_0(sK2,sK0),k3_xboole_0(sK2,sK1))),
% 3.60/0.99    inference(cnf_transformation,[],[f17])).
% 3.60/0.99  
% 3.60/0.99  fof(f41,plain,(
% 3.60/0.99    ~r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)))),
% 3.60/0.99    inference(definition_unfolding,[],[f32,f25,f25])).
% 3.60/0.99  
% 3.60/0.99  fof(f31,plain,(
% 3.60/0.99    r1_xboole_0(sK0,sK1)),
% 3.60/0.99    inference(cnf_transformation,[],[f17])).
% 3.60/0.99  
% 3.60/0.99  cnf(c_121,plain,
% 3.60/0.99      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.60/0.99      theory(equality) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_4,plain,
% 3.60/0.99      ( k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
% 3.60/0.99      inference(cnf_transformation,[],[f36]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_1222,plain,
% 3.60/0.99      ( ~ r1_xboole_0(X0,X1)
% 3.60/0.99      | r1_xboole_0(X2,k2_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X3))))
% 3.60/0.99      | X2 != X0 ),
% 3.60/0.99      inference(resolution,[status(thm)],[c_121,c_4]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_117,plain,( X0 = X0 ),theory(equality) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_7421,plain,
% 3.60/0.99      ( ~ r1_xboole_0(X0,X1)
% 3.60/0.99      | r1_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
% 3.60/0.99      inference(resolution,[status(thm)],[c_1222,c_117]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_9,plain,
% 3.60/0.99      ( r1_xboole_0(X0,X1) | ~ r1_xboole_0(X0,k2_xboole_0(X2,X1)) ),
% 3.60/0.99      inference(cnf_transformation,[],[f30]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_16314,plain,
% 3.60/0.99      ( ~ r1_xboole_0(X0,X1)
% 3.60/0.99      | r1_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
% 3.60/0.99      inference(resolution,[status(thm)],[c_7421,c_9]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_118,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_1,plain,
% 3.60/0.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 3.60/0.99      inference(cnf_transformation,[],[f33]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_976,plain,
% 3.60/0.99      ( X0 != k4_xboole_0(X1,k4_xboole_0(X1,X2))
% 3.60/0.99      | k4_xboole_0(X2,k4_xboole_0(X2,X1)) = X0 ),
% 3.60/0.99      inference(resolution,[status(thm)],[c_118,c_1]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_984,plain,
% 3.60/0.99      ( X0 != X1 | X1 = X0 ),
% 3.60/0.99      inference(resolution,[status(thm)],[c_118,c_117]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_3,plain,
% 3.60/0.99      ( ~ r1_xboole_0(X0,X1)
% 3.60/0.99      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 3.60/0.99      inference(cnf_transformation,[],[f35]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_2540,plain,
% 3.60/0.99      ( ~ r1_xboole_0(X0,X1)
% 3.60/0.99      | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 3.60/0.99      inference(resolution,[status(thm)],[c_984,c_3]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_4794,plain,
% 3.60/0.99      ( ~ r1_xboole_0(X0,X1)
% 3.60/0.99      | k4_xboole_0(X1,k4_xboole_0(X1,X0)) = k1_xboole_0 ),
% 3.60/0.99      inference(resolution,[status(thm)],[c_976,c_2540]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_2,plain,
% 3.60/0.99      ( r1_xboole_0(X0,X1)
% 3.60/0.99      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
% 3.60/0.99      inference(cnf_transformation,[],[f34]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_6158,plain,
% 3.60/0.99      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 3.60/0.99      inference(resolution,[status(thm)],[c_4794,c_2]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_17445,plain,
% 3.60/0.99      ( ~ r1_xboole_0(X0,X1)
% 3.60/0.99      | r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X0) ),
% 3.60/0.99      inference(resolution,[status(thm)],[c_16314,c_6158]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_1240,plain,
% 3.60/0.99      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,X1) | X2 != X0 ),
% 3.60/0.99      inference(resolution,[status(thm)],[c_121,c_117]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_1252,plain,
% 3.60/0.99      ( ~ r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)
% 3.60/0.99      | r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
% 3.60/0.99      inference(resolution,[status(thm)],[c_1240,c_1]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_18123,plain,
% 3.60/0.99      ( ~ r1_xboole_0(X0,X1)
% 3.60/0.99      | r1_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X1)),X0) ),
% 3.60/0.99      inference(resolution,[status(thm)],[c_17445,c_1252]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_12,negated_conjecture,
% 3.60/0.99      ( ~ r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK1))) ),
% 3.60/0.99      inference(cnf_transformation,[],[f41]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_19246,plain,
% 3.60/0.99      ( ~ r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)),sK0) ),
% 3.60/0.99      inference(resolution,[status(thm)],[c_18123,c_12]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_19266,plain,
% 3.60/0.99      ( ~ r1_xboole_0(sK0,sK1) ),
% 3.60/0.99      inference(resolution,[status(thm)],[c_19246,c_18123]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_13,negated_conjecture,
% 3.60/0.99      ( r1_xboole_0(sK0,sK1) ),
% 3.60/0.99      inference(cnf_transformation,[],[f31]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(contradiction,plain,
% 3.60/0.99      ( $false ),
% 3.60/0.99      inference(minisat,[status(thm)],[c_19266,c_13]) ).
% 3.60/0.99  
% 3.60/0.99  
% 3.60/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.60/0.99  
% 3.60/0.99  ------                               Statistics
% 3.60/0.99  
% 3.60/0.99  ------ Selected
% 3.60/0.99  
% 3.60/0.99  total_time:                             0.482
% 3.60/0.99  
%------------------------------------------------------------------------------
