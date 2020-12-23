%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:23:30 EST 2020

% Result     : CounterSatisfiable 3.47s
% Output     : Saturation 3.47s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 152 expanded)
%              Number of clauses        :   38 (  62 expanded)
%              Number of leaves         :   10 (  29 expanded)
%              Depth                    :   11
%              Number of atoms          :  190 ( 478 expanded)
%              Number of equality atoms :   64 ( 115 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f19])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f21])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ~ ( r1_xboole_0(X0,X1)
          & r1_tarski(X2,X1)
          & r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ~ v1_xboole_0(X2)
       => ~ ( r1_xboole_0(X0,X1)
            & r1_tarski(X2,X1)
            & r1_tarski(X2,X0) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
      & r1_tarski(X2,X1)
      & r1_tarski(X2,X0)
      & ~ v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
      & r1_tarski(X2,X1)
      & r1_tarski(X2,X0)
      & ~ v1_xboole_0(X2) ) ),
    inference(flattening,[],[f17])).

fof(f25,plain,
    ( ? [X0,X1,X2] :
        ( r1_xboole_0(X0,X1)
        & r1_tarski(X2,X1)
        & r1_tarski(X2,X0)
        & ~ v1_xboole_0(X2) )
   => ( r1_xboole_0(sK2,sK3)
      & r1_tarski(sK4,sK3)
      & r1_tarski(sK4,sK2)
      & ~ v1_xboole_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( r1_xboole_0(sK2,sK3)
    & r1_tarski(sK4,sK3)
    & r1_tarski(sK4,sK2)
    & ~ v1_xboole_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f18,f25])).

fof(f40,plain,(
    r1_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f26])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f13,f23])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f6,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f39,plain,(
    r1_tarski(sK4,sK3) ),
    inference(cnf_transformation,[],[f26])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f37,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_116,plain,
    ( X0_2 = X0_2 ),
    theory(equality)).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_1425,plain,
    ( arAF0_r1_tarski_0_1(X0)
    | arAF0_r2_hidden_0_1(arAF0_sK0_0)
    | ~ iProver_ARSWP_33 ),
    inference(arg_filter_abstr,[status(unp)],[c_1])).

cnf(c_1624,plain,
    ( arAF0_r1_tarski_0_1(X0) = iProver_top
    | arAF0_r2_hidden_0_1(arAF0_sK0_0) = iProver_top
    | iProver_ARSWP_33 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1425])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_1430,plain,
    ( ~ arAF0_r1_tarski_0_1(X0)
    | ~ iProver_ARSWP_38
    | arAF0_k3_xboole_0_0_1(X0) = X0 ),
    inference(arg_filter_abstr,[status(unp)],[c_7])).

cnf(c_1621,plain,
    ( arAF0_k3_xboole_0_0_1(X0) = X0
    | arAF0_r1_tarski_0_1(X0) != iProver_top
    | iProver_ARSWP_38 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1430])).

cnf(c_2005,plain,
    ( arAF0_k3_xboole_0_0_1(X0) = X0
    | arAF0_r2_hidden_0_1(arAF0_sK0_0) = iProver_top
    | iProver_ARSWP_38 != iProver_top
    | iProver_ARSWP_33 != iProver_top ),
    inference(superposition,[status(thm)],[c_1624,c_1621])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_1424,plain,
    ( arAF0_r1_tarski_0_1(X0)
    | ~ arAF0_r2_hidden_0_1(arAF0_sK0_0)
    | ~ iProver_ARSWP_32 ),
    inference(arg_filter_abstr,[status(unp)],[c_0])).

cnf(c_1625,plain,
    ( arAF0_r1_tarski_0_1(X0) = iProver_top
    | arAF0_r2_hidden_0_1(arAF0_sK0_0) != iProver_top
    | iProver_ARSWP_32 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1424])).

cnf(c_2208,plain,
    ( arAF0_k3_xboole_0_0_1(X0) = X0
    | arAF0_r1_tarski_0_1(X1) = iProver_top
    | iProver_ARSWP_38 != iProver_top
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top ),
    inference(superposition,[status(thm)],[c_2005,c_1625])).

cnf(c_1441,plain,
    ( arAF0_r1_tarski_0_1(X0) = iProver_top
    | arAF0_r2_hidden_0_1(arAF0_sK0_0) != iProver_top
    | iProver_ARSWP_32 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1424])).

cnf(c_1453,plain,
    ( arAF0_k3_xboole_0_0_1(X0) = X0
    | arAF0_r1_tarski_0_1(X0) != iProver_top
    | iProver_ARSWP_38 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1430])).

cnf(c_2355,plain,
    ( arAF0_k3_xboole_0_0_1(X0) = X0
    | iProver_ARSWP_38 != iProver_top
    | iProver_ARSWP_33 != iProver_top
    | iProver_ARSWP_32 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2208,c_1441,c_1453,c_2005])).

cnf(c_10,negated_conjecture,
    ( r1_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1433,negated_conjecture,
    ( ~ iProver_ARSWP_41
    | arAF0_r1_xboole_0_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_10])).

cnf(c_1619,plain,
    ( iProver_ARSWP_41 != iProver_top
    | arAF0_r1_xboole_0_0 = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1433])).

cnf(c_5,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_1428,plain,
    ( ~ arAF0_r2_hidden_0_1(X0)
    | ~ iProver_ARSWP_36
    | ~ arAF0_r1_xboole_0_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_5])).

cnf(c_1623,plain,
    ( arAF0_r2_hidden_0_1(X0) != iProver_top
    | iProver_ARSWP_36 != iProver_top
    | arAF0_r1_xboole_0_0 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1428])).

cnf(c_2209,plain,
    ( arAF0_k3_xboole_0_0_1(X0) = X0
    | iProver_ARSWP_38 != iProver_top
    | iProver_ARSWP_36 != iProver_top
    | iProver_ARSWP_33 != iProver_top
    | arAF0_r1_xboole_0_0 != iProver_top ),
    inference(superposition,[status(thm)],[c_2005,c_1623])).

cnf(c_2242,plain,
    ( arAF0_k3_xboole_0_0_1(X0) = X0
    | iProver_ARSWP_41 != iProver_top
    | iProver_ARSWP_38 != iProver_top
    | iProver_ARSWP_36 != iProver_top
    | iProver_ARSWP_33 != iProver_top ),
    inference(superposition,[status(thm)],[c_1619,c_2209])).

cnf(c_8,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_1431,plain,
    ( arAF0_r1_tarski_0_1(k1_xboole_0)
    | ~ iProver_ARSWP_39 ),
    inference(arg_filter_abstr,[status(unp)],[c_8])).

cnf(c_1620,plain,
    ( arAF0_r1_tarski_0_1(k1_xboole_0) = iProver_top
    | iProver_ARSWP_39 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1431])).

cnf(c_1842,plain,
    ( arAF0_k3_xboole_0_0_1(k1_xboole_0) = k1_xboole_0
    | iProver_ARSWP_39 != iProver_top
    | iProver_ARSWP_38 != iProver_top ),
    inference(superposition,[status(thm)],[c_1620,c_1621])).

cnf(c_11,negated_conjecture,
    ( r1_tarski(sK4,sK3) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1434,negated_conjecture,
    ( arAF0_r1_tarski_0_1(sK4)
    | ~ iProver_ARSWP_42 ),
    inference(arg_filter_abstr,[status(unp)],[c_11])).

cnf(c_1618,plain,
    ( arAF0_r1_tarski_0_1(sK4) = iProver_top
    | iProver_ARSWP_42 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1434])).

cnf(c_1841,plain,
    ( arAF0_k3_xboole_0_0_1(sK4) = sK4
    | iProver_ARSWP_42 != iProver_top
    | iProver_ARSWP_38 != iProver_top ),
    inference(superposition,[status(thm)],[c_1618,c_1621])).

cnf(c_6,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_1429,plain,
    ( arAF0_r2_hidden_0_1(arAF0_sK1_0)
    | ~ iProver_ARSWP_37
    | arAF0_r1_xboole_0_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_6])).

cnf(c_1622,plain,
    ( arAF0_r2_hidden_0_1(arAF0_sK1_0) = iProver_top
    | iProver_ARSWP_37 != iProver_top
    | arAF0_r1_xboole_0_0 = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1429])).

cnf(c_3,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_1628,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_13,negated_conjecture,
    ( ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_1627,plain,
    ( v1_xboole_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 15:58:29 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running in FOF mode
% 3.47/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.47/0.99  
% 3.47/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.47/0.99  
% 3.47/0.99  ------  iProver source info
% 3.47/0.99  
% 3.47/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.47/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.47/0.99  git: non_committed_changes: false
% 3.47/0.99  git: last_make_outside_of_git: false
% 3.47/0.99  
% 3.47/0.99  ------ 
% 3.47/0.99  ------ Parsing...
% 3.47/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.47/0.99  
% 3.47/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.47/0.99  
% 3.47/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.47/0.99  
% 3.47/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.47/0.99  ------ Proving...
% 3.47/0.99  ------ Problem Properties 
% 3.47/0.99  
% 3.47/0.99  
% 3.47/0.99  clauses                                 14
% 3.47/0.99  conjectures                             4
% 3.47/0.99  EPR                                     9
% 3.47/0.99  Horn                                    12
% 3.47/0.99  unary                                   6
% 3.47/0.99  binary                                  6
% 3.47/0.99  lits                                    24
% 3.47/0.99  lits eq                                 1
% 3.47/0.99  fd_pure                                 0
% 3.47/0.99  fd_pseudo                               0
% 3.47/0.99  fd_cond                                 0
% 3.47/0.99  fd_pseudo_cond                          0
% 3.47/0.99  AC symbols                              0
% 3.47/0.99  
% 3.47/0.99  ------ Input Options Time Limit: Unbounded
% 3.47/0.99  
% 3.47/0.99  
% 3.47/0.99  
% 3.47/0.99  
% 3.47/0.99  ------ Preprocessing...
% 3.47/0.99  
% 3.47/0.99  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 3.47/0.99  Current options:
% 3.47/0.99  ------ 
% 3.47/0.99  
% 3.47/0.99  
% 3.47/0.99  
% 3.47/0.99  
% 3.47/0.99  ------ Proving...
% 3.47/0.99  
% 3.47/0.99  
% 3.47/0.99  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.47/0.99  
% 3.47/0.99  ------ Proving...
% 3.47/0.99  
% 3.47/0.99  
% 3.47/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.47/0.99  
% 3.47/0.99  ------ Proving...
% 3.47/0.99  
% 3.47/0.99  
% 3.47/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.47/0.99  
% 3.47/0.99  ------ Proving...
% 3.47/0.99  
% 3.47/0.99  
% 3.47/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.47/0.99  
% 3.47/0.99  ------ Proving...
% 3.47/0.99  
% 3.47/0.99  
% 3.47/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.47/0.99  
% 3.47/0.99  ------ Proving...
% 3.47/0.99  
% 3.47/0.99  
% 3.47/0.99  % SZS status CounterSatisfiable for theBenchmark.p
% 3.47/0.99  
% 3.47/0.99  % SZS output start Saturation for theBenchmark.p
% 3.47/0.99  
% 3.47/0.99  fof(f1,axiom,(
% 3.47/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.47/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.47/0.99  
% 3.47/0.99  fof(f11,plain,(
% 3.47/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.47/0.99    inference(ennf_transformation,[],[f1])).
% 3.47/0.99  
% 3.47/0.99  fof(f19,plain,(
% 3.47/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.47/0.99    inference(nnf_transformation,[],[f11])).
% 3.47/0.99  
% 3.47/0.99  fof(f20,plain,(
% 3.47/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.47/0.99    inference(rectify,[],[f19])).
% 3.47/0.99  
% 3.47/0.99  fof(f21,plain,(
% 3.47/0.99    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.47/0.99    introduced(choice_axiom,[])).
% 3.47/0.99  
% 3.47/0.99  fof(f22,plain,(
% 3.47/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.47/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f21])).
% 3.47/0.99  
% 3.47/0.99  fof(f28,plain,(
% 3.47/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 3.47/0.99    inference(cnf_transformation,[],[f22])).
% 3.47/0.99  
% 3.47/0.99  fof(f5,axiom,(
% 3.47/0.99    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.47/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.47/0.99  
% 3.47/0.99  fof(f14,plain,(
% 3.47/0.99    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.47/0.99    inference(ennf_transformation,[],[f5])).
% 3.47/0.99  
% 3.47/0.99  fof(f34,plain,(
% 3.47/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 3.47/0.99    inference(cnf_transformation,[],[f14])).
% 3.47/0.99  
% 3.47/0.99  fof(f29,plain,(
% 3.47/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 3.47/0.99    inference(cnf_transformation,[],[f22])).
% 3.47/0.99  
% 3.47/0.99  fof(f8,conjecture,(
% 3.47/0.99    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ~(r1_xboole_0(X0,X1) & r1_tarski(X2,X1) & r1_tarski(X2,X0)))),
% 3.47/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.47/0.99  
% 3.47/0.99  fof(f9,negated_conjecture,(
% 3.47/0.99    ~! [X0,X1,X2] : (~v1_xboole_0(X2) => ~(r1_xboole_0(X0,X1) & r1_tarski(X2,X1) & r1_tarski(X2,X0)))),
% 3.47/0.99    inference(negated_conjecture,[],[f8])).
% 3.47/0.99  
% 3.47/0.99  fof(f17,plain,(
% 3.47/0.99    ? [X0,X1,X2] : ((r1_xboole_0(X0,X1) & r1_tarski(X2,X1) & r1_tarski(X2,X0)) & ~v1_xboole_0(X2))),
% 3.47/0.99    inference(ennf_transformation,[],[f9])).
% 3.47/0.99  
% 3.47/0.99  fof(f18,plain,(
% 3.47/0.99    ? [X0,X1,X2] : (r1_xboole_0(X0,X1) & r1_tarski(X2,X1) & r1_tarski(X2,X0) & ~v1_xboole_0(X2))),
% 3.47/0.99    inference(flattening,[],[f17])).
% 3.47/0.99  
% 3.47/0.99  fof(f25,plain,(
% 3.47/0.99    ? [X0,X1,X2] : (r1_xboole_0(X0,X1) & r1_tarski(X2,X1) & r1_tarski(X2,X0) & ~v1_xboole_0(X2)) => (r1_xboole_0(sK2,sK3) & r1_tarski(sK4,sK3) & r1_tarski(sK4,sK2) & ~v1_xboole_0(sK4))),
% 3.47/0.99    introduced(choice_axiom,[])).
% 3.47/0.99  
% 3.47/0.99  fof(f26,plain,(
% 3.47/0.99    r1_xboole_0(sK2,sK3) & r1_tarski(sK4,sK3) & r1_tarski(sK4,sK2) & ~v1_xboole_0(sK4)),
% 3.47/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f18,f25])).
% 3.47/0.99  
% 3.47/0.99  fof(f40,plain,(
% 3.47/0.99    r1_xboole_0(sK2,sK3)),
% 3.47/0.99    inference(cnf_transformation,[],[f26])).
% 3.47/0.99  
% 3.47/0.99  fof(f4,axiom,(
% 3.47/0.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 3.47/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.47/0.99  
% 3.47/0.99  fof(f10,plain,(
% 3.47/0.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 3.47/0.99    inference(rectify,[],[f4])).
% 3.47/0.99  
% 3.47/0.99  fof(f13,plain,(
% 3.47/0.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 3.47/0.99    inference(ennf_transformation,[],[f10])).
% 3.47/0.99  
% 3.47/0.99  fof(f23,plain,(
% 3.47/0.99    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)))),
% 3.47/0.99    introduced(choice_axiom,[])).
% 3.47/0.99  
% 3.47/0.99  fof(f24,plain,(
% 3.47/0.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 3.47/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f13,f23])).
% 3.47/0.99  
% 3.47/0.99  fof(f33,plain,(
% 3.47/0.99    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 3.47/0.99    inference(cnf_transformation,[],[f24])).
% 3.47/0.99  
% 3.47/0.99  fof(f6,axiom,(
% 3.47/0.99    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.47/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.47/0.99  
% 3.47/0.99  fof(f35,plain,(
% 3.47/0.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.47/0.99    inference(cnf_transformation,[],[f6])).
% 3.47/0.99  
% 3.47/0.99  fof(f39,plain,(
% 3.47/0.99    r1_tarski(sK4,sK3)),
% 3.47/0.99    inference(cnf_transformation,[],[f26])).
% 3.47/0.99  
% 3.47/0.99  fof(f32,plain,(
% 3.47/0.99    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 3.47/0.99    inference(cnf_transformation,[],[f24])).
% 3.47/0.99  
% 3.47/0.99  fof(f2,axiom,(
% 3.47/0.99    v1_xboole_0(k1_xboole_0)),
% 3.47/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.47/0.99  
% 3.47/0.99  fof(f30,plain,(
% 3.47/0.99    v1_xboole_0(k1_xboole_0)),
% 3.47/0.99    inference(cnf_transformation,[],[f2])).
% 3.47/0.99  
% 3.47/0.99  fof(f37,plain,(
% 3.47/0.99    ~v1_xboole_0(sK4)),
% 3.47/0.99    inference(cnf_transformation,[],[f26])).
% 3.47/0.99  
% 3.47/0.99  cnf(c_116,plain,( X0_2 = X0_2 ),theory(equality) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1,plain,
% 3.47/0.99      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 3.47/0.99      inference(cnf_transformation,[],[f28]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1425,plain,
% 3.47/0.99      ( arAF0_r1_tarski_0_1(X0)
% 3.47/0.99      | arAF0_r2_hidden_0_1(arAF0_sK0_0)
% 3.47/0.99      | ~ iProver_ARSWP_33 ),
% 3.47/0.99      inference(arg_filter_abstr,[status(unp)],[c_1]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1624,plain,
% 3.47/0.99      ( arAF0_r1_tarski_0_1(X0) = iProver_top
% 3.47/0.99      | arAF0_r2_hidden_0_1(arAF0_sK0_0) = iProver_top
% 3.47/0.99      | iProver_ARSWP_33 != iProver_top ),
% 3.47/0.99      inference(predicate_to_equality,[status(thm)],[c_1425]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_7,plain,
% 3.47/0.99      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 3.47/0.99      inference(cnf_transformation,[],[f34]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1430,plain,
% 3.47/0.99      ( ~ arAF0_r1_tarski_0_1(X0)
% 3.47/0.99      | ~ iProver_ARSWP_38
% 3.47/0.99      | arAF0_k3_xboole_0_0_1(X0) = X0 ),
% 3.47/0.99      inference(arg_filter_abstr,[status(unp)],[c_7]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1621,plain,
% 3.47/0.99      ( arAF0_k3_xboole_0_0_1(X0) = X0
% 3.47/0.99      | arAF0_r1_tarski_0_1(X0) != iProver_top
% 3.47/0.99      | iProver_ARSWP_38 != iProver_top ),
% 3.47/0.99      inference(predicate_to_equality,[status(thm)],[c_1430]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_2005,plain,
% 3.47/0.99      ( arAF0_k3_xboole_0_0_1(X0) = X0
% 3.47/0.99      | arAF0_r2_hidden_0_1(arAF0_sK0_0) = iProver_top
% 3.47/0.99      | iProver_ARSWP_38 != iProver_top
% 3.47/0.99      | iProver_ARSWP_33 != iProver_top ),
% 3.47/0.99      inference(superposition,[status(thm)],[c_1624,c_1621]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_0,plain,
% 3.47/0.99      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 3.47/0.99      inference(cnf_transformation,[],[f29]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1424,plain,
% 3.47/0.99      ( arAF0_r1_tarski_0_1(X0)
% 3.47/0.99      | ~ arAF0_r2_hidden_0_1(arAF0_sK0_0)
% 3.47/0.99      | ~ iProver_ARSWP_32 ),
% 3.47/0.99      inference(arg_filter_abstr,[status(unp)],[c_0]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1625,plain,
% 3.47/0.99      ( arAF0_r1_tarski_0_1(X0) = iProver_top
% 3.47/0.99      | arAF0_r2_hidden_0_1(arAF0_sK0_0) != iProver_top
% 3.47/0.99      | iProver_ARSWP_32 != iProver_top ),
% 3.47/0.99      inference(predicate_to_equality,[status(thm)],[c_1424]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_2208,plain,
% 3.47/0.99      ( arAF0_k3_xboole_0_0_1(X0) = X0
% 3.47/0.99      | arAF0_r1_tarski_0_1(X1) = iProver_top
% 3.47/0.99      | iProver_ARSWP_38 != iProver_top
% 3.47/0.99      | iProver_ARSWP_33 != iProver_top
% 3.47/0.99      | iProver_ARSWP_32 != iProver_top ),
% 3.47/0.99      inference(superposition,[status(thm)],[c_2005,c_1625]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1441,plain,
% 3.47/0.99      ( arAF0_r1_tarski_0_1(X0) = iProver_top
% 3.47/0.99      | arAF0_r2_hidden_0_1(arAF0_sK0_0) != iProver_top
% 3.47/0.99      | iProver_ARSWP_32 != iProver_top ),
% 3.47/0.99      inference(predicate_to_equality,[status(thm)],[c_1424]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1453,plain,
% 3.47/0.99      ( arAF0_k3_xboole_0_0_1(X0) = X0
% 3.47/0.99      | arAF0_r1_tarski_0_1(X0) != iProver_top
% 3.47/0.99      | iProver_ARSWP_38 != iProver_top ),
% 3.47/0.99      inference(predicate_to_equality,[status(thm)],[c_1430]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_2355,plain,
% 3.47/0.99      ( arAF0_k3_xboole_0_0_1(X0) = X0
% 3.47/0.99      | iProver_ARSWP_38 != iProver_top
% 3.47/0.99      | iProver_ARSWP_33 != iProver_top
% 3.47/0.99      | iProver_ARSWP_32 != iProver_top ),
% 3.47/0.99      inference(global_propositional_subsumption,
% 3.47/0.99                [status(thm)],
% 3.47/0.99                [c_2208,c_1441,c_1453,c_2005]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_10,negated_conjecture,
% 3.47/0.99      ( r1_xboole_0(sK2,sK3) ),
% 3.47/0.99      inference(cnf_transformation,[],[f40]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1433,negated_conjecture,
% 3.47/0.99      ( ~ iProver_ARSWP_41 | arAF0_r1_xboole_0_0 ),
% 3.47/0.99      inference(arg_filter_abstr,[status(unp)],[c_10]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1619,plain,
% 3.47/0.99      ( iProver_ARSWP_41 != iProver_top | arAF0_r1_xboole_0_0 = iProver_top ),
% 3.47/0.99      inference(predicate_to_equality,[status(thm)],[c_1433]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_5,plain,
% 3.47/0.99      ( ~ r1_xboole_0(X0,X1) | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ),
% 3.47/0.99      inference(cnf_transformation,[],[f33]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1428,plain,
% 3.47/0.99      ( ~ arAF0_r2_hidden_0_1(X0)
% 3.47/0.99      | ~ iProver_ARSWP_36
% 3.47/0.99      | ~ arAF0_r1_xboole_0_0 ),
% 3.47/0.99      inference(arg_filter_abstr,[status(unp)],[c_5]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1623,plain,
% 3.47/0.99      ( arAF0_r2_hidden_0_1(X0) != iProver_top
% 3.47/0.99      | iProver_ARSWP_36 != iProver_top
% 3.47/0.99      | arAF0_r1_xboole_0_0 != iProver_top ),
% 3.47/0.99      inference(predicate_to_equality,[status(thm)],[c_1428]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_2209,plain,
% 3.47/0.99      ( arAF0_k3_xboole_0_0_1(X0) = X0
% 3.47/0.99      | iProver_ARSWP_38 != iProver_top
% 3.47/0.99      | iProver_ARSWP_36 != iProver_top
% 3.47/0.99      | iProver_ARSWP_33 != iProver_top
% 3.47/0.99      | arAF0_r1_xboole_0_0 != iProver_top ),
% 3.47/0.99      inference(superposition,[status(thm)],[c_2005,c_1623]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_2242,plain,
% 3.47/0.99      ( arAF0_k3_xboole_0_0_1(X0) = X0
% 3.47/0.99      | iProver_ARSWP_41 != iProver_top
% 3.47/0.99      | iProver_ARSWP_38 != iProver_top
% 3.47/0.99      | iProver_ARSWP_36 != iProver_top
% 3.47/0.99      | iProver_ARSWP_33 != iProver_top ),
% 3.47/0.99      inference(superposition,[status(thm)],[c_1619,c_2209]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_8,plain,
% 3.47/0.99      ( r1_tarski(k1_xboole_0,X0) ),
% 3.47/0.99      inference(cnf_transformation,[],[f35]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1431,plain,
% 3.47/0.99      ( arAF0_r1_tarski_0_1(k1_xboole_0) | ~ iProver_ARSWP_39 ),
% 3.47/0.99      inference(arg_filter_abstr,[status(unp)],[c_8]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1620,plain,
% 3.47/0.99      ( arAF0_r1_tarski_0_1(k1_xboole_0) = iProver_top
% 3.47/0.99      | iProver_ARSWP_39 != iProver_top ),
% 3.47/0.99      inference(predicate_to_equality,[status(thm)],[c_1431]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1842,plain,
% 3.47/0.99      ( arAF0_k3_xboole_0_0_1(k1_xboole_0) = k1_xboole_0
% 3.47/0.99      | iProver_ARSWP_39 != iProver_top
% 3.47/0.99      | iProver_ARSWP_38 != iProver_top ),
% 3.47/0.99      inference(superposition,[status(thm)],[c_1620,c_1621]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_11,negated_conjecture,
% 3.47/0.99      ( r1_tarski(sK4,sK3) ),
% 3.47/0.99      inference(cnf_transformation,[],[f39]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1434,negated_conjecture,
% 3.47/0.99      ( arAF0_r1_tarski_0_1(sK4) | ~ iProver_ARSWP_42 ),
% 3.47/0.99      inference(arg_filter_abstr,[status(unp)],[c_11]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1618,plain,
% 3.47/0.99      ( arAF0_r1_tarski_0_1(sK4) = iProver_top
% 3.47/0.99      | iProver_ARSWP_42 != iProver_top ),
% 3.47/0.99      inference(predicate_to_equality,[status(thm)],[c_1434]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1841,plain,
% 3.47/0.99      ( arAF0_k3_xboole_0_0_1(sK4) = sK4
% 3.47/0.99      | iProver_ARSWP_42 != iProver_top
% 3.47/0.99      | iProver_ARSWP_38 != iProver_top ),
% 3.47/0.99      inference(superposition,[status(thm)],[c_1618,c_1621]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_6,plain,
% 3.47/0.99      ( r1_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) ),
% 3.47/0.99      inference(cnf_transformation,[],[f32]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1429,plain,
% 3.47/0.99      ( arAF0_r2_hidden_0_1(arAF0_sK1_0)
% 3.47/0.99      | ~ iProver_ARSWP_37
% 3.47/0.99      | arAF0_r1_xboole_0_0 ),
% 3.47/0.99      inference(arg_filter_abstr,[status(unp)],[c_6]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1622,plain,
% 3.47/0.99      ( arAF0_r2_hidden_0_1(arAF0_sK1_0) = iProver_top
% 3.47/0.99      | iProver_ARSWP_37 != iProver_top
% 3.47/0.99      | arAF0_r1_xboole_0_0 = iProver_top ),
% 3.47/0.99      inference(predicate_to_equality,[status(thm)],[c_1429]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_3,plain,
% 3.47/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 3.47/0.99      inference(cnf_transformation,[],[f30]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1628,plain,
% 3.47/0.99      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.47/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_13,negated_conjecture,
% 3.47/0.99      ( ~ v1_xboole_0(sK4) ),
% 3.47/0.99      inference(cnf_transformation,[],[f37]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1627,plain,
% 3.47/0.99      ( v1_xboole_0(sK4) != iProver_top ),
% 3.47/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.47/0.99  
% 3.47/0.99  
% 3.47/0.99  % SZS output end Saturation for theBenchmark.p
% 3.47/0.99  
% 3.47/0.99  ------                               Statistics
% 3.47/0.99  
% 3.47/0.99  ------ Selected
% 3.47/0.99  
% 3.47/0.99  total_time:                             0.101
% 3.47/0.99  
%------------------------------------------------------------------------------
