%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:24:38 EST 2020

% Result     : Theorem 3.56s
% Output     : CNFRefutation 3.56s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 261 expanded)
%              Number of clauses        :   30 (  92 expanded)
%              Number of leaves         :    8 (  61 expanded)
%              Depth                    :   19
%              Number of atoms          :  132 ( 651 expanded)
%              Number of equality atoms :   69 ( 263 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,conjecture,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_xboole_0(X0,X1)
      <=> k4_xboole_0(X0,X1) = X0 ) ),
    inference(negated_conjecture,[],[f8])).

fof(f13,plain,(
    ? [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <~> k4_xboole_0(X0,X1) = X0 ) ),
    inference(ennf_transformation,[],[f9])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ( k4_xboole_0(X0,X1) != X0
        | ~ r1_xboole_0(X0,X1) )
      & ( k4_xboole_0(X0,X1) = X0
        | r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f18,plain,
    ( ? [X0,X1] :
        ( ( k4_xboole_0(X0,X1) != X0
          | ~ r1_xboole_0(X0,X1) )
        & ( k4_xboole_0(X0,X1) = X0
          | r1_xboole_0(X0,X1) ) )
   => ( ( k4_xboole_0(sK1,sK2) != sK1
        | ~ r1_xboole_0(sK1,sK2) )
      & ( k4_xboole_0(sK1,sK2) = sK1
        | r1_xboole_0(sK1,sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ( k4_xboole_0(sK1,sK2) != sK1
      | ~ r1_xboole_0(sK1,sK2) )
    & ( k4_xboole_0(sK1,sK2) = sK1
      | r1_xboole_0(sK1,sK2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f17,f18])).

fof(f30,plain,
    ( k4_xboole_0(sK1,sK2) = sK1
    | r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f21,f28])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f22,f28])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f15,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f15])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f35,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f29,f28,f28])).

fof(f31,plain,
    ( k4_xboole_0(sK1,sK2) != sK1
    | ~ r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_10,negated_conjecture,
    ( r1_xboole_0(sK1,sK2)
    | k4_xboole_0(sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_575,plain,
    ( k4_xboole_0(sK1,sK2) = sK1
    | r1_xboole_0(sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_581,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1206,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = k1_xboole_0
    | k4_xboole_0(sK1,sK2) = sK1 ),
    inference(superposition,[status(thm)],[c_575,c_581])).

cnf(c_7,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f27])).

cnf(c_1,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_582,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1301,plain,
    ( k4_xboole_0(X0,X0) != k1_xboole_0
    | r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_582])).

cnf(c_1440,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_1301])).

cnf(c_5,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_578,plain,
    ( r2_hidden(sK0(X0,X1),X1) = iProver_top
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_4,negated_conjecture,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_579,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r1_xboole_0(X2,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_779,plain,
    ( r2_hidden(sK0(X0,X1),X2) != iProver_top
    | r1_xboole_0(X2,X1) != iProver_top
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_578,c_579])).

cnf(c_955,plain,
    ( r1_xboole_0(X0,X0) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_578,c_779])).

cnf(c_1472,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1440,c_955])).

cnf(c_1620,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1472,c_581])).

cnf(c_1625,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1620,c_7])).

cnf(c_8,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_2209,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X0,k1_xboole_0),X1) ),
    inference(superposition,[status(thm)],[c_1625,c_8])).

cnf(c_2239,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_2209,c_7])).

cnf(c_3024,plain,
    ( k4_xboole_0(sK1,sK2) = sK1
    | k4_xboole_0(sK1,k1_xboole_0) = k4_xboole_0(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_1206,c_2239])).

cnf(c_3171,plain,
    ( k4_xboole_0(sK1,sK2) = sK1 ),
    inference(demodulation,[status(thm)],[c_3024,c_7])).

cnf(c_3223,plain,
    ( k4_xboole_0(sK1,sK1) != k1_xboole_0
    | r1_xboole_0(sK1,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_3171,c_582])).

cnf(c_3241,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(sK1,sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3223,c_1625])).

cnf(c_3242,plain,
    ( r1_xboole_0(sK1,sK2) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3241])).

cnf(c_9,negated_conjecture,
    ( ~ r1_xboole_0(sK1,sK2)
    | k4_xboole_0(sK1,sK2) != sK1 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_12,plain,
    ( k4_xboole_0(sK1,sK2) != sK1
    | r1_xboole_0(sK1,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3242,c_3171,c_12])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n015.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:28:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.34  % Running in FOF mode
% 3.56/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.56/0.99  
% 3.56/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.56/0.99  
% 3.56/0.99  ------  iProver source info
% 3.56/0.99  
% 3.56/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.56/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.56/0.99  git: non_committed_changes: false
% 3.56/0.99  git: last_make_outside_of_git: false
% 3.56/0.99  
% 3.56/0.99  ------ 
% 3.56/0.99  ------ Parsing...
% 3.56/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.56/0.99  
% 3.56/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.56/0.99  
% 3.56/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.56/0.99  
% 3.56/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.56/0.99  ------ Proving...
% 3.56/0.99  ------ Problem Properties 
% 3.56/0.99  
% 3.56/0.99  
% 3.56/0.99  clauses                                 11
% 3.56/0.99  conjectures                             3
% 3.56/0.99  EPR                                     2
% 3.56/0.99  Horn                                    8
% 3.56/0.99  unary                                   3
% 3.56/0.99  binary                                  7
% 3.56/0.99  lits                                    20
% 3.56/0.99  lits eq                                 7
% 3.56/0.99  fd_pure                                 0
% 3.56/0.99  fd_pseudo                               0
% 3.56/0.99  fd_cond                                 0
% 3.56/0.99  fd_pseudo_cond                          0
% 3.56/0.99  AC symbols                              0
% 3.56/0.99  
% 3.56/0.99  ------ Input Options Time Limit: Unbounded
% 3.56/0.99  
% 3.56/0.99  
% 3.56/0.99  
% 3.56/0.99  
% 3.56/0.99  ------ Preprocessing... sf_s  rm: 7 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 3.56/0.99  Current options:
% 3.56/0.99  ------ 
% 3.56/0.99  
% 3.56/0.99  
% 3.56/0.99  
% 3.56/0.99  
% 3.56/0.99  ------ Proving...
% 3.56/0.99  
% 3.56/0.99  
% 3.56/0.99  ------ Preprocessing... sf_s  rm: 7 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.56/0.99  
% 3.56/0.99  ------ Proving...
% 3.56/0.99  
% 3.56/0.99  
% 3.56/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.56/0.99  
% 3.56/0.99  ------ Proving...
% 3.56/0.99  
% 3.56/0.99  
% 3.56/0.99  % SZS status Theorem for theBenchmark.p
% 3.56/0.99  
% 3.56/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.56/0.99  
% 3.56/0.99  fof(f8,conjecture,(
% 3.56/0.99    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 3.56/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.56/0.99  
% 3.56/0.99  fof(f9,negated_conjecture,(
% 3.56/0.99    ~! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 3.56/0.99    inference(negated_conjecture,[],[f8])).
% 3.56/0.99  
% 3.56/0.99  fof(f13,plain,(
% 3.56/0.99    ? [X0,X1] : (r1_xboole_0(X0,X1) <~> k4_xboole_0(X0,X1) = X0)),
% 3.56/0.99    inference(ennf_transformation,[],[f9])).
% 3.56/0.99  
% 3.56/0.99  fof(f17,plain,(
% 3.56/0.99    ? [X0,X1] : ((k4_xboole_0(X0,X1) != X0 | ~r1_xboole_0(X0,X1)) & (k4_xboole_0(X0,X1) = X0 | r1_xboole_0(X0,X1)))),
% 3.56/0.99    inference(nnf_transformation,[],[f13])).
% 3.56/0.99  
% 3.56/0.99  fof(f18,plain,(
% 3.56/0.99    ? [X0,X1] : ((k4_xboole_0(X0,X1) != X0 | ~r1_xboole_0(X0,X1)) & (k4_xboole_0(X0,X1) = X0 | r1_xboole_0(X0,X1))) => ((k4_xboole_0(sK1,sK2) != sK1 | ~r1_xboole_0(sK1,sK2)) & (k4_xboole_0(sK1,sK2) = sK1 | r1_xboole_0(sK1,sK2)))),
% 3.56/0.99    introduced(choice_axiom,[])).
% 3.56/0.99  
% 3.56/0.99  fof(f19,plain,(
% 3.56/0.99    (k4_xboole_0(sK1,sK2) != sK1 | ~r1_xboole_0(sK1,sK2)) & (k4_xboole_0(sK1,sK2) = sK1 | r1_xboole_0(sK1,sK2))),
% 3.56/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f17,f18])).
% 3.56/0.99  
% 3.56/0.99  fof(f30,plain,(
% 3.56/0.99    k4_xboole_0(sK1,sK2) = sK1 | r1_xboole_0(sK1,sK2)),
% 3.56/0.99    inference(cnf_transformation,[],[f19])).
% 3.56/0.99  
% 3.56/0.99  fof(f2,axiom,(
% 3.56/0.99    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 3.56/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.56/0.99  
% 3.56/0.99  fof(f14,plain,(
% 3.56/0.99    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 3.56/0.99    inference(nnf_transformation,[],[f2])).
% 3.56/0.99  
% 3.56/0.99  fof(f21,plain,(
% 3.56/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 3.56/0.99    inference(cnf_transformation,[],[f14])).
% 3.56/0.99  
% 3.56/0.99  fof(f6,axiom,(
% 3.56/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.56/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.56/0.99  
% 3.56/0.99  fof(f28,plain,(
% 3.56/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.56/0.99    inference(cnf_transformation,[],[f6])).
% 3.56/0.99  
% 3.56/0.99  fof(f34,plain,(
% 3.56/0.99    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 3.56/0.99    inference(definition_unfolding,[],[f21,f28])).
% 3.56/0.99  
% 3.56/0.99  fof(f5,axiom,(
% 3.56/0.99    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 3.56/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.56/0.99  
% 3.56/0.99  fof(f27,plain,(
% 3.56/0.99    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.56/0.99    inference(cnf_transformation,[],[f5])).
% 3.56/0.99  
% 3.56/0.99  fof(f22,plain,(
% 3.56/0.99    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 3.56/0.99    inference(cnf_transformation,[],[f14])).
% 3.56/0.99  
% 3.56/0.99  fof(f33,plain,(
% 3.56/0.99    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.56/0.99    inference(definition_unfolding,[],[f22,f28])).
% 3.56/0.99  
% 3.56/0.99  fof(f4,axiom,(
% 3.56/0.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.56/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.56/0.99  
% 3.56/0.99  fof(f10,plain,(
% 3.56/0.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.56/0.99    inference(rectify,[],[f4])).
% 3.56/0.99  
% 3.56/0.99  fof(f12,plain,(
% 3.56/0.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 3.56/0.99    inference(ennf_transformation,[],[f10])).
% 3.56/0.99  
% 3.56/0.99  fof(f15,plain,(
% 3.56/0.99    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.56/0.99    introduced(choice_axiom,[])).
% 3.56/0.99  
% 3.56/0.99  fof(f16,plain,(
% 3.56/0.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 3.56/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f15])).
% 3.56/0.99  
% 3.56/0.99  fof(f25,plain,(
% 3.56/0.99    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 3.56/0.99    inference(cnf_transformation,[],[f16])).
% 3.56/0.99  
% 3.56/0.99  fof(f26,plain,(
% 3.56/0.99    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 3.56/0.99    inference(cnf_transformation,[],[f16])).
% 3.56/0.99  
% 3.56/0.99  fof(f7,axiom,(
% 3.56/0.99    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 3.56/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.56/0.99  
% 3.56/0.99  fof(f29,plain,(
% 3.56/0.99    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 3.56/0.99    inference(cnf_transformation,[],[f7])).
% 3.56/0.99  
% 3.56/0.99  fof(f35,plain,(
% 3.56/0.99    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 3.56/0.99    inference(definition_unfolding,[],[f29,f28,f28])).
% 3.56/0.99  
% 3.56/0.99  fof(f31,plain,(
% 3.56/0.99    k4_xboole_0(sK1,sK2) != sK1 | ~r1_xboole_0(sK1,sK2)),
% 3.56/0.99    inference(cnf_transformation,[],[f19])).
% 3.56/0.99  
% 3.56/0.99  cnf(c_10,negated_conjecture,
% 3.56/0.99      ( r1_xboole_0(sK1,sK2) | k4_xboole_0(sK1,sK2) = sK1 ),
% 3.56/0.99      inference(cnf_transformation,[],[f30]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_575,plain,
% 3.56/0.99      ( k4_xboole_0(sK1,sK2) = sK1 | r1_xboole_0(sK1,sK2) = iProver_top ),
% 3.56/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_2,plain,
% 3.56/0.99      ( ~ r1_xboole_0(X0,X1)
% 3.56/0.99      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 3.56/0.99      inference(cnf_transformation,[],[f34]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_581,plain,
% 3.56/0.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
% 3.56/0.99      | r1_xboole_0(X0,X1) != iProver_top ),
% 3.56/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_1206,plain,
% 3.56/0.99      ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = k1_xboole_0
% 3.56/0.99      | k4_xboole_0(sK1,sK2) = sK1 ),
% 3.56/0.99      inference(superposition,[status(thm)],[c_575,c_581]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_7,plain,
% 3.56/0.99      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.56/0.99      inference(cnf_transformation,[],[f27]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_1,plain,
% 3.56/0.99      ( r1_xboole_0(X0,X1)
% 3.56/0.99      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
% 3.56/0.99      inference(cnf_transformation,[],[f33]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_582,plain,
% 3.56/0.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0
% 3.56/0.99      | r1_xboole_0(X0,X1) = iProver_top ),
% 3.56/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_1301,plain,
% 3.56/0.99      ( k4_xboole_0(X0,X0) != k1_xboole_0
% 3.56/0.99      | r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 3.56/0.99      inference(superposition,[status(thm)],[c_7,c_582]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_1440,plain,
% 3.56/0.99      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 3.56/0.99      inference(superposition,[status(thm)],[c_7,c_1301]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_5,plain,
% 3.56/0.99      ( r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1) ),
% 3.56/0.99      inference(cnf_transformation,[],[f25]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_578,plain,
% 3.56/0.99      ( r2_hidden(sK0(X0,X1),X1) = iProver_top
% 3.56/0.99      | r1_xboole_0(X0,X1) = iProver_top ),
% 3.56/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_4,negated_conjecture,
% 3.56/0.99      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,X2) | ~ r1_xboole_0(X2,X1) ),
% 3.56/0.99      inference(cnf_transformation,[],[f26]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_579,plain,
% 3.56/0.99      ( r2_hidden(X0,X1) != iProver_top
% 3.56/0.99      | r2_hidden(X0,X2) != iProver_top
% 3.56/0.99      | r1_xboole_0(X2,X1) != iProver_top ),
% 3.56/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_779,plain,
% 3.56/0.99      ( r2_hidden(sK0(X0,X1),X2) != iProver_top
% 3.56/0.99      | r1_xboole_0(X2,X1) != iProver_top
% 3.56/0.99      | r1_xboole_0(X0,X1) = iProver_top ),
% 3.56/0.99      inference(superposition,[status(thm)],[c_578,c_579]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_955,plain,
% 3.56/0.99      ( r1_xboole_0(X0,X0) != iProver_top
% 3.56/0.99      | r1_xboole_0(X1,X0) = iProver_top ),
% 3.56/0.99      inference(superposition,[status(thm)],[c_578,c_779]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_1472,plain,
% 3.56/0.99      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 3.56/0.99      inference(superposition,[status(thm)],[c_1440,c_955]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_1620,plain,
% 3.56/0.99      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 3.56/0.99      inference(superposition,[status(thm)],[c_1472,c_581]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_1625,plain,
% 3.56/0.99      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.56/0.99      inference(light_normalisation,[status(thm)],[c_1620,c_7]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_8,plain,
% 3.56/0.99      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
% 3.56/0.99      inference(cnf_transformation,[],[f35]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_2209,plain,
% 3.56/0.99      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X0,k1_xboole_0),X1) ),
% 3.56/0.99      inference(superposition,[status(thm)],[c_1625,c_8]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_2239,plain,
% 3.56/0.99      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 3.56/0.99      inference(light_normalisation,[status(thm)],[c_2209,c_7]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_3024,plain,
% 3.56/0.99      ( k4_xboole_0(sK1,sK2) = sK1
% 3.56/0.99      | k4_xboole_0(sK1,k1_xboole_0) = k4_xboole_0(sK1,sK2) ),
% 3.56/0.99      inference(superposition,[status(thm)],[c_1206,c_2239]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_3171,plain,
% 3.56/0.99      ( k4_xboole_0(sK1,sK2) = sK1 ),
% 3.56/0.99      inference(demodulation,[status(thm)],[c_3024,c_7]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_3223,plain,
% 3.56/0.99      ( k4_xboole_0(sK1,sK1) != k1_xboole_0
% 3.56/0.99      | r1_xboole_0(sK1,sK2) = iProver_top ),
% 3.56/0.99      inference(superposition,[status(thm)],[c_3171,c_582]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_3241,plain,
% 3.56/0.99      ( k1_xboole_0 != k1_xboole_0 | r1_xboole_0(sK1,sK2) = iProver_top ),
% 3.56/0.99      inference(demodulation,[status(thm)],[c_3223,c_1625]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_3242,plain,
% 3.56/0.99      ( r1_xboole_0(sK1,sK2) = iProver_top ),
% 3.56/0.99      inference(equality_resolution_simp,[status(thm)],[c_3241]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_9,negated_conjecture,
% 3.56/0.99      ( ~ r1_xboole_0(sK1,sK2) | k4_xboole_0(sK1,sK2) != sK1 ),
% 3.56/0.99      inference(cnf_transformation,[],[f31]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_12,plain,
% 3.56/0.99      ( k4_xboole_0(sK1,sK2) != sK1
% 3.56/0.99      | r1_xboole_0(sK1,sK2) != iProver_top ),
% 3.56/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(contradiction,plain,
% 3.56/0.99      ( $false ),
% 3.56/0.99      inference(minisat,[status(thm)],[c_3242,c_3171,c_12]) ).
% 3.56/0.99  
% 3.56/0.99  
% 3.56/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.56/0.99  
% 3.56/0.99  ------                               Statistics
% 3.56/0.99  
% 3.56/0.99  ------ Selected
% 3.56/0.99  
% 3.56/0.99  total_time:                             0.165
% 3.56/0.99  
%------------------------------------------------------------------------------
