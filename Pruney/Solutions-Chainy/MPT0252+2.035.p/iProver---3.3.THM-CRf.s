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
% DateTime   : Thu Dec  3 11:33:26 EST 2020

% Result     : Theorem 3.83s
% Output     : CNFRefutation 3.83s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 256 expanded)
%              Number of clauses        :   33 (  91 expanded)
%              Number of leaves         :    8 (  53 expanded)
%              Depth                    :   16
%              Number of atoms          :  127 ( 610 expanded)
%              Number of equality atoms :   59 ( 207 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f30])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f84,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f39])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f32])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f14,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f23,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f16,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f72,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_tarski(k2_tarski(k2_tarski(X0,X0),k2_tarski(X1,X1))) ),
    inference(definition_unfolding,[],[f51,f60,f53,f53])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f77,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f43,f60])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f41,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f25,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)
     => r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)
       => r2_hidden(X0,X2) ) ),
    inference(negated_conjecture,[],[f25])).

fof(f29,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f34,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_hidden(X0,X2)
        & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) )
   => ( ~ r2_hidden(sK0,sK2)
      & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ~ r2_hidden(sK0,sK2)
    & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f29,f34])).

fof(f64,plain,(
    r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f82,plain,(
    r1_tarski(k3_tarski(k2_tarski(k2_tarski(sK0,sK1),sK2)),sK2) ),
    inference(definition_unfolding,[],[f64,f60])).

fof(f65,plain,(
    ~ r2_hidden(sK0,sK2) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_7,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1589,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_17,plain,
    ( r2_hidden(X0,X1)
    | ~ r1_tarski(k2_tarski(X2,X0),X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1586,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r1_tarski(k2_tarski(X2,X0),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1674,plain,
    ( r2_hidden(X0,k2_tarski(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1589,c_1586])).

cnf(c_0,plain,
    ( k3_tarski(k2_tarski(k2_tarski(X0,X0),k2_tarski(X1,X1))) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_9,plain,
    ( r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1588,plain,
    ( r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1655,plain,
    ( r1_tarski(k2_tarski(X0,X0),k2_tarski(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_1588])).

cnf(c_18,plain,
    ( r2_hidden(X0,X1)
    | ~ r1_tarski(k2_tarski(X0,X2),X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1585,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r1_tarski(k2_tarski(X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1664,plain,
    ( r2_hidden(X0,k2_tarski(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1655,c_1585])).

cnf(c_16,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X1)
    | r1_tarski(k2_tarski(X2,X0),X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1587,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X1) != iProver_top
    | r1_tarski(k2_tarski(X2,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1590,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1716,plain,
    ( k2_tarski(X0,X1) = X2
    | r2_hidden(X1,X2) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r1_tarski(X2,k2_tarski(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1587,c_1590])).

cnf(c_1814,plain,
    ( k2_tarski(X0,X1) = k2_tarski(X2,X3)
    | r2_hidden(X1,k2_tarski(X2,X3)) != iProver_top
    | r2_hidden(X0,k2_tarski(X2,X3)) != iProver_top
    | r2_hidden(X3,k2_tarski(X0,X1)) != iProver_top
    | r2_hidden(X2,k2_tarski(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1587,c_1716])).

cnf(c_1837,plain,
    ( k2_tarski(X0,X1) = k2_tarski(X2,X0)
    | r2_hidden(X0,k2_tarski(X2,X0)) != iProver_top
    | r2_hidden(X2,k2_tarski(X0,X1)) != iProver_top
    | r2_hidden(X1,k2_tarski(X2,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1664,c_1814])).

cnf(c_1862,plain,
    ( k2_tarski(X0,X1) = k2_tarski(X1,X2)
    | r2_hidden(X0,k2_tarski(X1,X2)) != iProver_top
    | r2_hidden(X2,k2_tarski(X0,X1)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1837,c_1674])).

cnf(c_1865,plain,
    ( k2_tarski(X0,X1) = k2_tarski(X1,X0)
    | r2_hidden(X1,k2_tarski(X1,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1674,c_1862])).

cnf(c_1874,plain,
    ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1865,c_1664])).

cnf(c_20,negated_conjecture,
    ( r1_tarski(k3_tarski(k2_tarski(k2_tarski(sK0,sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1583,plain,
    ( r1_tarski(k3_tarski(k2_tarski(k2_tarski(sK0,sK1),sK2)),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1876,plain,
    ( r1_tarski(k3_tarski(k2_tarski(sK2,k2_tarski(sK0,sK1))),sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1874,c_1583])).

cnf(c_1688,plain,
    ( k3_tarski(k2_tarski(X0,X1)) = X0
    | r1_tarski(k3_tarski(k2_tarski(X0,X1)),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1588,c_1590])).

cnf(c_2030,plain,
    ( k3_tarski(k2_tarski(sK2,k2_tarski(sK0,sK1))) = sK2 ),
    inference(superposition,[status(thm)],[c_1876,c_1688])).

cnf(c_1908,plain,
    ( r1_tarski(X0,k3_tarski(k2_tarski(X1,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1874,c_1588])).

cnf(c_2040,plain,
    ( r1_tarski(k2_tarski(sK0,sK1),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2030,c_1908])).

cnf(c_2048,plain,
    ( r2_hidden(sK0,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2040,c_1585])).

cnf(c_19,negated_conjecture,
    ( ~ r2_hidden(sK0,sK2) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_22,plain,
    ( r2_hidden(sK0,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2048,c_22])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n018.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 14:45:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.83/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.83/0.99  
% 3.83/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.83/0.99  
% 3.83/0.99  ------  iProver source info
% 3.83/0.99  
% 3.83/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.83/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.83/0.99  git: non_committed_changes: false
% 3.83/0.99  git: last_make_outside_of_git: false
% 3.83/0.99  
% 3.83/0.99  ------ 
% 3.83/0.99  ------ Parsing...
% 3.83/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.83/0.99  
% 3.83/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.83/0.99  
% 3.83/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.83/0.99  
% 3.83/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.83/0.99  ------ Proving...
% 3.83/0.99  ------ Problem Properties 
% 3.83/0.99  
% 3.83/0.99  
% 3.83/0.99  clauses                                 20
% 3.83/0.99  conjectures                             2
% 3.83/0.99  EPR                                     3
% 3.83/0.99  Horn                                    20
% 3.83/0.99  unary                                   16
% 3.83/0.99  binary                                  2
% 3.83/0.99  lits                                    26
% 3.83/0.99  lits eq                                 12
% 3.83/0.99  fd_pure                                 0
% 3.83/0.99  fd_pseudo                               0
% 3.83/0.99  fd_cond                                 0
% 3.83/0.99  fd_pseudo_cond                          1
% 3.83/0.99  AC symbols                              1
% 3.83/0.99  
% 3.83/0.99  ------ Input Options Time Limit: Unbounded
% 3.83/0.99  
% 3.83/0.99  
% 3.83/0.99  
% 3.83/0.99  
% 3.83/0.99  ------ Preprocessing...
% 3.83/0.99  
% 3.83/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 3.83/0.99  Current options:
% 3.83/0.99  ------ 
% 3.83/0.99  
% 3.83/0.99  
% 3.83/0.99  
% 3.83/0.99  
% 3.83/0.99  ------ Proving...
% 3.83/0.99  
% 3.83/0.99  
% 3.83/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.83/0.99  
% 3.83/0.99  ------ Proving...
% 3.83/0.99  
% 3.83/0.99  
% 3.83/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.83/0.99  
% 3.83/0.99  ------ Proving...
% 3.83/0.99  
% 3.83/0.99  
% 3.83/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.83/0.99  
% 3.83/0.99  ------ Proving...
% 3.83/0.99  
% 3.83/0.99  
% 3.83/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.83/0.99  
% 3.83/0.99  ------ Proving...
% 3.83/0.99  
% 3.83/0.99  
% 3.83/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.83/0.99  
% 3.83/0.99  ------ Proving...
% 3.83/0.99  
% 3.83/0.99  
% 3.83/0.99  % SZS status Theorem for theBenchmark.p
% 3.83/0.99  
% 3.83/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.83/0.99  
% 3.83/0.99  fof(f4,axiom,(
% 3.83/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.83/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.83/0.99  
% 3.83/0.99  fof(f30,plain,(
% 3.83/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.83/0.99    inference(nnf_transformation,[],[f4])).
% 3.83/0.99  
% 3.83/0.99  fof(f31,plain,(
% 3.83/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.83/0.99    inference(flattening,[],[f30])).
% 3.83/0.99  
% 3.83/0.99  fof(f39,plain,(
% 3.83/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.83/0.99    inference(cnf_transformation,[],[f31])).
% 3.83/0.99  
% 3.83/0.99  fof(f84,plain,(
% 3.83/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.83/0.99    inference(equality_resolution,[],[f39])).
% 3.83/0.99  
% 3.83/0.99  fof(f24,axiom,(
% 3.83/0.99    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 3.83/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.83/0.99  
% 3.83/0.99  fof(f32,plain,(
% 3.83/0.99    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 3.83/0.99    inference(nnf_transformation,[],[f24])).
% 3.83/0.99  
% 3.83/0.99  fof(f33,plain,(
% 3.83/0.99    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 3.83/0.99    inference(flattening,[],[f32])).
% 3.83/0.99  
% 3.83/0.99  fof(f62,plain,(
% 3.83/0.99    ( ! [X2,X0,X1] : (r2_hidden(X1,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 3.83/0.99    inference(cnf_transformation,[],[f33])).
% 3.83/0.99  
% 3.83/0.99  fof(f14,axiom,(
% 3.83/0.99    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1)),
% 3.83/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.83/0.99  
% 3.83/0.99  fof(f51,plain,(
% 3.83/0.99    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1)) )),
% 3.83/0.99    inference(cnf_transformation,[],[f14])).
% 3.83/0.99  
% 3.83/0.99  fof(f23,axiom,(
% 3.83/0.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.83/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.83/0.99  
% 3.83/0.99  fof(f60,plain,(
% 3.83/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.83/0.99    inference(cnf_transformation,[],[f23])).
% 3.83/0.99  
% 3.83/0.99  fof(f16,axiom,(
% 3.83/0.99    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.83/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.83/0.99  
% 3.83/0.99  fof(f53,plain,(
% 3.83/0.99    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.83/0.99    inference(cnf_transformation,[],[f16])).
% 3.83/0.99  
% 3.83/0.99  fof(f72,plain,(
% 3.83/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_tarski(k2_tarski(k2_tarski(X0,X0),k2_tarski(X1,X1)))) )),
% 3.83/0.99    inference(definition_unfolding,[],[f51,f60,f53,f53])).
% 3.83/0.99  
% 3.83/0.99  fof(f6,axiom,(
% 3.83/0.99    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 3.83/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.83/0.99  
% 3.83/0.99  fof(f43,plain,(
% 3.83/0.99    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 3.83/0.99    inference(cnf_transformation,[],[f6])).
% 3.83/0.99  
% 3.83/0.99  fof(f77,plain,(
% 3.83/0.99    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) )),
% 3.83/0.99    inference(definition_unfolding,[],[f43,f60])).
% 3.83/0.99  
% 3.83/0.99  fof(f61,plain,(
% 3.83/0.99    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 3.83/0.99    inference(cnf_transformation,[],[f33])).
% 3.83/0.99  
% 3.83/0.99  fof(f63,plain,(
% 3.83/0.99    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 3.83/0.99    inference(cnf_transformation,[],[f33])).
% 3.83/0.99  
% 3.83/0.99  fof(f41,plain,(
% 3.83/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.83/0.99    inference(cnf_transformation,[],[f31])).
% 3.83/0.99  
% 3.83/0.99  fof(f25,conjecture,(
% 3.83/0.99    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) => r2_hidden(X0,X2))),
% 3.83/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.83/0.99  
% 3.83/0.99  fof(f26,negated_conjecture,(
% 3.83/0.99    ~! [X0,X1,X2] : (r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) => r2_hidden(X0,X2))),
% 3.83/0.99    inference(negated_conjecture,[],[f25])).
% 3.83/0.99  
% 3.83/0.99  fof(f29,plain,(
% 3.83/0.99    ? [X0,X1,X2] : (~r2_hidden(X0,X2) & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2))),
% 3.83/0.99    inference(ennf_transformation,[],[f26])).
% 3.83/0.99  
% 3.83/0.99  fof(f34,plain,(
% 3.83/0.99    ? [X0,X1,X2] : (~r2_hidden(X0,X2) & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)) => (~r2_hidden(sK0,sK2) & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2))),
% 3.83/0.99    introduced(choice_axiom,[])).
% 3.83/0.99  
% 3.83/0.99  fof(f35,plain,(
% 3.83/0.99    ~r2_hidden(sK0,sK2) & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2)),
% 3.83/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f29,f34])).
% 3.83/0.99  
% 3.83/0.99  fof(f64,plain,(
% 3.83/0.99    r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2)),
% 3.83/0.99    inference(cnf_transformation,[],[f35])).
% 3.83/0.99  
% 3.83/0.99  fof(f82,plain,(
% 3.83/0.99    r1_tarski(k3_tarski(k2_tarski(k2_tarski(sK0,sK1),sK2)),sK2)),
% 3.83/0.99    inference(definition_unfolding,[],[f64,f60])).
% 3.83/0.99  
% 3.83/0.99  fof(f65,plain,(
% 3.83/0.99    ~r2_hidden(sK0,sK2)),
% 3.83/0.99    inference(cnf_transformation,[],[f35])).
% 3.83/0.99  
% 3.83/0.99  cnf(c_7,plain,
% 3.83/0.99      ( r1_tarski(X0,X0) ),
% 3.83/0.99      inference(cnf_transformation,[],[f84]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_1589,plain,
% 3.83/0.99      ( r1_tarski(X0,X0) = iProver_top ),
% 3.83/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_17,plain,
% 3.83/0.99      ( r2_hidden(X0,X1) | ~ r1_tarski(k2_tarski(X2,X0),X1) ),
% 3.83/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_1586,plain,
% 3.83/0.99      ( r2_hidden(X0,X1) = iProver_top
% 3.83/0.99      | r1_tarski(k2_tarski(X2,X0),X1) != iProver_top ),
% 3.83/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_1674,plain,
% 3.83/0.99      ( r2_hidden(X0,k2_tarski(X1,X0)) = iProver_top ),
% 3.83/0.99      inference(superposition,[status(thm)],[c_1589,c_1586]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_0,plain,
% 3.83/0.99      ( k3_tarski(k2_tarski(k2_tarski(X0,X0),k2_tarski(X1,X1))) = k2_tarski(X0,X1) ),
% 3.83/0.99      inference(cnf_transformation,[],[f72]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_9,plain,
% 3.83/0.99      ( r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) ),
% 3.83/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_1588,plain,
% 3.83/0.99      ( r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) = iProver_top ),
% 3.83/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_1655,plain,
% 3.83/0.99      ( r1_tarski(k2_tarski(X0,X0),k2_tarski(X0,X1)) = iProver_top ),
% 3.83/0.99      inference(superposition,[status(thm)],[c_0,c_1588]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_18,plain,
% 3.83/0.99      ( r2_hidden(X0,X1) | ~ r1_tarski(k2_tarski(X0,X2),X1) ),
% 3.83/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_1585,plain,
% 3.83/0.99      ( r2_hidden(X0,X1) = iProver_top
% 3.83/0.99      | r1_tarski(k2_tarski(X0,X2),X1) != iProver_top ),
% 3.83/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_1664,plain,
% 3.83/0.99      ( r2_hidden(X0,k2_tarski(X0,X1)) = iProver_top ),
% 3.83/0.99      inference(superposition,[status(thm)],[c_1655,c_1585]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_16,plain,
% 3.83/0.99      ( ~ r2_hidden(X0,X1)
% 3.83/0.99      | ~ r2_hidden(X2,X1)
% 3.83/0.99      | r1_tarski(k2_tarski(X2,X0),X1) ),
% 3.83/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_1587,plain,
% 3.83/0.99      ( r2_hidden(X0,X1) != iProver_top
% 3.83/0.99      | r2_hidden(X2,X1) != iProver_top
% 3.83/0.99      | r1_tarski(k2_tarski(X2,X0),X1) = iProver_top ),
% 3.83/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_5,plain,
% 3.83/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.83/0.99      inference(cnf_transformation,[],[f41]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_1590,plain,
% 3.83/0.99      ( X0 = X1
% 3.83/0.99      | r1_tarski(X0,X1) != iProver_top
% 3.83/0.99      | r1_tarski(X1,X0) != iProver_top ),
% 3.83/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_1716,plain,
% 3.83/0.99      ( k2_tarski(X0,X1) = X2
% 3.83/0.99      | r2_hidden(X1,X2) != iProver_top
% 3.83/0.99      | r2_hidden(X0,X2) != iProver_top
% 3.83/0.99      | r1_tarski(X2,k2_tarski(X0,X1)) != iProver_top ),
% 3.83/0.99      inference(superposition,[status(thm)],[c_1587,c_1590]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_1814,plain,
% 3.83/0.99      ( k2_tarski(X0,X1) = k2_tarski(X2,X3)
% 3.83/0.99      | r2_hidden(X1,k2_tarski(X2,X3)) != iProver_top
% 3.83/0.99      | r2_hidden(X0,k2_tarski(X2,X3)) != iProver_top
% 3.83/0.99      | r2_hidden(X3,k2_tarski(X0,X1)) != iProver_top
% 3.83/0.99      | r2_hidden(X2,k2_tarski(X0,X1)) != iProver_top ),
% 3.83/0.99      inference(superposition,[status(thm)],[c_1587,c_1716]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_1837,plain,
% 3.83/0.99      ( k2_tarski(X0,X1) = k2_tarski(X2,X0)
% 3.83/0.99      | r2_hidden(X0,k2_tarski(X2,X0)) != iProver_top
% 3.83/0.99      | r2_hidden(X2,k2_tarski(X0,X1)) != iProver_top
% 3.83/0.99      | r2_hidden(X1,k2_tarski(X2,X0)) != iProver_top ),
% 3.83/0.99      inference(superposition,[status(thm)],[c_1664,c_1814]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_1862,plain,
% 3.83/0.99      ( k2_tarski(X0,X1) = k2_tarski(X1,X2)
% 3.83/0.99      | r2_hidden(X0,k2_tarski(X1,X2)) != iProver_top
% 3.83/0.99      | r2_hidden(X2,k2_tarski(X0,X1)) != iProver_top ),
% 3.83/0.99      inference(forward_subsumption_resolution,
% 3.83/0.99                [status(thm)],
% 3.83/0.99                [c_1837,c_1674]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_1865,plain,
% 3.83/0.99      ( k2_tarski(X0,X1) = k2_tarski(X1,X0)
% 3.83/0.99      | r2_hidden(X1,k2_tarski(X1,X0)) != iProver_top ),
% 3.83/0.99      inference(superposition,[status(thm)],[c_1674,c_1862]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_1874,plain,
% 3.83/0.99      ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
% 3.83/0.99      inference(forward_subsumption_resolution,
% 3.83/0.99                [status(thm)],
% 3.83/0.99                [c_1865,c_1664]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_20,negated_conjecture,
% 3.83/0.99      ( r1_tarski(k3_tarski(k2_tarski(k2_tarski(sK0,sK1),sK2)),sK2) ),
% 3.83/0.99      inference(cnf_transformation,[],[f82]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_1583,plain,
% 3.83/0.99      ( r1_tarski(k3_tarski(k2_tarski(k2_tarski(sK0,sK1),sK2)),sK2) = iProver_top ),
% 3.83/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_1876,plain,
% 3.83/0.99      ( r1_tarski(k3_tarski(k2_tarski(sK2,k2_tarski(sK0,sK1))),sK2) = iProver_top ),
% 3.83/0.99      inference(demodulation,[status(thm)],[c_1874,c_1583]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_1688,plain,
% 3.83/0.99      ( k3_tarski(k2_tarski(X0,X1)) = X0
% 3.83/0.99      | r1_tarski(k3_tarski(k2_tarski(X0,X1)),X0) != iProver_top ),
% 3.83/0.99      inference(superposition,[status(thm)],[c_1588,c_1590]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_2030,plain,
% 3.83/0.99      ( k3_tarski(k2_tarski(sK2,k2_tarski(sK0,sK1))) = sK2 ),
% 3.83/0.99      inference(superposition,[status(thm)],[c_1876,c_1688]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_1908,plain,
% 3.83/0.99      ( r1_tarski(X0,k3_tarski(k2_tarski(X1,X0))) = iProver_top ),
% 3.83/0.99      inference(superposition,[status(thm)],[c_1874,c_1588]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_2040,plain,
% 3.83/0.99      ( r1_tarski(k2_tarski(sK0,sK1),sK2) = iProver_top ),
% 3.83/0.99      inference(superposition,[status(thm)],[c_2030,c_1908]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_2048,plain,
% 3.83/0.99      ( r2_hidden(sK0,sK2) = iProver_top ),
% 3.83/0.99      inference(superposition,[status(thm)],[c_2040,c_1585]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_19,negated_conjecture,
% 3.83/0.99      ( ~ r2_hidden(sK0,sK2) ),
% 3.83/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_22,plain,
% 3.83/0.99      ( r2_hidden(sK0,sK2) != iProver_top ),
% 3.83/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(contradiction,plain,
% 3.83/0.99      ( $false ),
% 3.83/0.99      inference(minisat,[status(thm)],[c_2048,c_22]) ).
% 3.83/0.99  
% 3.83/0.99  
% 3.83/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.83/0.99  
% 3.83/0.99  ------                               Statistics
% 3.83/0.99  
% 3.83/0.99  ------ Selected
% 3.83/0.99  
% 3.83/0.99  total_time:                             0.085
% 3.83/0.99  
%------------------------------------------------------------------------------
