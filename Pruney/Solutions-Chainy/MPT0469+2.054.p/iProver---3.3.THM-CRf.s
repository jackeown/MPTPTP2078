%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:43:51 EST 2020

% Result     : Theorem 2.15s
% Output     : CNFRefutation 2.15s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 166 expanded)
%              Number of clauses        :   37 (  59 expanded)
%              Number of leaves         :   16 (  37 expanded)
%              Depth                    :   11
%              Number of atoms          :  186 ( 438 expanded)
%              Number of equality atoms :   81 ( 221 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f18])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f41,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f32])).

fof(f4,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f20])).

fof(f24,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
     => r2_hidden(k4_tarski(X2,sK2(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK1(X0,X1),X3),X0)
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK1(X0,X1),X4),X0)
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK1(X0,X1),X3),X0)
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f21,f24,f23,f22])).

fof(f34,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f44,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f34])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( ! [X2] : ~ r2_hidden(X2,k1_relat_1(X1))
          & r2_hidden(X0,k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ? [X2] : r2_hidden(X2,k1_relat_1(X1))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ? [X2] : r2_hidden(X2,k1_relat_1(X1))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f26,plain,(
    ! [X1] :
      ( ? [X2] : r2_hidden(X2,k1_relat_1(X1))
     => r2_hidden(sK4(X1),k1_relat_1(X1)) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X1),k1_relat_1(X1))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f14,f26])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X1),k1_relat_1(X1))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
     => v1_xboole_0(X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f11,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ? [X1] : r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f16,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f16])).

fof(f28,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f29,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f8,conjecture,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
      & k1_xboole_0 = k1_relat_1(k1_xboole_0) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f15,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(ennf_transformation,[],[f9])).

fof(f40,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f15])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f42,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f31])).

cnf(c_221,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1289,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,k1_xboole_0))
    | ~ r2_hidden(X2,k1_xboole_0)
    | X0 != X2 ),
    inference(resolution,[status(thm)],[c_221,c_2])).

cnf(c_219,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3541,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,k1_xboole_0))
    | ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1289,c_219])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_396,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_548,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2,c_396])).

cnf(c_554,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_548])).

cnf(c_4033,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3541,c_554])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,sK3(X1,X0)),X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_4452,plain,
    ( ~ r2_hidden(X0,k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_4033,c_9])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(sK4(X1),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_118,plain,
    ( r2_hidden(sK0(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(resolution,[status(thm)],[c_0,c_1])).

cnf(c_12,negated_conjecture,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_490,plain,
    ( r2_hidden(sK0(k2_relat_1(k1_xboole_0)),k2_relat_1(k1_xboole_0))
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_118,c_12])).

cnf(c_801,plain,
    ( r2_hidden(sK4(k1_xboole_0),k1_relat_1(k1_xboole_0))
    | ~ v1_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_11,c_490])).

cnf(c_10,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_391,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_505,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2,c_391])).

cnf(c_507,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_505])).

cnf(c_812,plain,
    ( r2_hidden(sK4(k1_xboole_0),k1_relat_1(k1_xboole_0))
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_801,c_507])).

cnf(c_4,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_34,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_3,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_35,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_220,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_492,plain,
    ( k1_relat_1(k1_xboole_0) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_220])).

cnf(c_493,plain,
    ( k1_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_492])).

cnf(c_389,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK0(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_118])).

cnf(c_392,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(k4_tarski(X0,sK3(X1,X0)),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_758,plain,
    ( r2_hidden(X0,k1_relat_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_392,c_548])).

cnf(c_866,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_389,c_758])).

cnf(c_883,plain,
    ( r2_hidden(sK4(k1_xboole_0),k1_relat_1(k1_xboole_0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_812,c_34,c_35,c_493,c_507,c_801,c_866])).

cnf(c_4457,plain,
    ( $false ),
    inference(backward_subsumption_resolution,[status(thm)],[c_4452,c_883])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:05:16 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 2.15/1.02  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.15/1.02  
% 2.15/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.15/1.02  
% 2.15/1.02  ------  iProver source info
% 2.15/1.02  
% 2.15/1.02  git: date: 2020-06-30 10:37:57 +0100
% 2.15/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.15/1.02  git: non_committed_changes: false
% 2.15/1.02  git: last_make_outside_of_git: false
% 2.15/1.02  
% 2.15/1.02  ------ 
% 2.15/1.02  ------ Parsing...
% 2.15/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.15/1.02  
% 2.15/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.15/1.02  
% 2.15/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.15/1.02  
% 2.15/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.15/1.02  ------ Proving...
% 2.15/1.02  ------ Problem Properties 
% 2.15/1.02  
% 2.15/1.02  
% 2.15/1.02  clauses                                 12
% 2.15/1.02  conjectures                             1
% 2.15/1.02  EPR                                     0
% 2.15/1.02  Horn                                    9
% 2.15/1.02  unary                                   4
% 2.15/1.02  binary                                  4
% 2.15/1.02  lits                                    24
% 2.15/1.02  lits eq                                 10
% 2.15/1.02  fd_pure                                 0
% 2.15/1.02  fd_pseudo                               0
% 2.15/1.02  fd_cond                                 2
% 2.15/1.02  fd_pseudo_cond                          2
% 2.15/1.02  AC symbols                              0
% 2.15/1.02  
% 2.15/1.02  ------ Input Options Time Limit: Unbounded
% 2.15/1.02  
% 2.15/1.02  
% 2.15/1.02  ------ 
% 2.15/1.02  Current options:
% 2.15/1.02  ------ 
% 2.15/1.02  
% 2.15/1.02  
% 2.15/1.02  
% 2.15/1.02  
% 2.15/1.02  ------ Proving...
% 2.15/1.02  
% 2.15/1.02  
% 2.15/1.02  % SZS status Theorem for theBenchmark.p
% 2.15/1.02  
% 2.15/1.02   Resolution empty clause
% 2.15/1.02  
% 2.15/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 2.15/1.02  
% 2.15/1.02  fof(f3,axiom,(
% 2.15/1.02    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.15/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.15/1.02  
% 2.15/1.02  fof(f18,plain,(
% 2.15/1.02    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.15/1.02    inference(nnf_transformation,[],[f3])).
% 2.15/1.02  
% 2.15/1.02  fof(f19,plain,(
% 2.15/1.02    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.15/1.02    inference(flattening,[],[f18])).
% 2.15/1.02  
% 2.15/1.02  fof(f32,plain,(
% 2.15/1.02    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 2.15/1.02    inference(cnf_transformation,[],[f19])).
% 2.15/1.02  
% 2.15/1.02  fof(f41,plain,(
% 2.15/1.02    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 2.15/1.02    inference(equality_resolution,[],[f32])).
% 2.15/1.02  
% 2.15/1.02  fof(f4,axiom,(
% 2.15/1.02    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 2.15/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.15/1.02  
% 2.15/1.02  fof(f33,plain,(
% 2.15/1.02    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 2.15/1.02    inference(cnf_transformation,[],[f4])).
% 2.15/1.02  
% 2.15/1.02  fof(f5,axiom,(
% 2.15/1.02    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 2.15/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.15/1.02  
% 2.15/1.02  fof(f20,plain,(
% 2.15/1.02    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 2.15/1.02    inference(nnf_transformation,[],[f5])).
% 2.15/1.02  
% 2.15/1.02  fof(f21,plain,(
% 2.15/1.02    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 2.15/1.02    inference(rectify,[],[f20])).
% 2.15/1.02  
% 2.15/1.02  fof(f24,plain,(
% 2.15/1.02    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0))),
% 2.15/1.02    introduced(choice_axiom,[])).
% 2.15/1.02  
% 2.15/1.02  fof(f23,plain,(
% 2.15/1.02    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) => r2_hidden(k4_tarski(X2,sK2(X0,X1)),X0))) )),
% 2.15/1.02    introduced(choice_axiom,[])).
% 2.15/1.02  
% 2.15/1.02  fof(f22,plain,(
% 2.15/1.02    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK1(X0,X1),X3),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK1(X0,X1),X4),X0) | r2_hidden(sK1(X0,X1),X1))))),
% 2.15/1.02    introduced(choice_axiom,[])).
% 2.15/1.02  
% 2.15/1.02  fof(f25,plain,(
% 2.15/1.02    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK1(X0,X1),X3),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0) | r2_hidden(sK1(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 2.15/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f21,f24,f23,f22])).
% 2.15/1.02  
% 2.15/1.02  fof(f34,plain,(
% 2.15/1.02    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0) | ~r2_hidden(X5,X1) | k1_relat_1(X0) != X1) )),
% 2.15/1.02    inference(cnf_transformation,[],[f25])).
% 2.15/1.02  
% 2.15/1.02  fof(f44,plain,(
% 2.15/1.02    ( ! [X0,X5] : (r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0) | ~r2_hidden(X5,k1_relat_1(X0))) )),
% 2.15/1.02    inference(equality_resolution,[],[f34])).
% 2.15/1.02  
% 2.15/1.02  fof(f7,axiom,(
% 2.15/1.02    ! [X0,X1] : (v1_relat_1(X1) => ~(! [X2] : ~r2_hidden(X2,k1_relat_1(X1)) & r2_hidden(X0,k2_relat_1(X1))))),
% 2.15/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.15/1.02  
% 2.15/1.02  fof(f13,plain,(
% 2.15/1.02    ! [X0,X1] : ((? [X2] : r2_hidden(X2,k1_relat_1(X1)) | ~r2_hidden(X0,k2_relat_1(X1))) | ~v1_relat_1(X1))),
% 2.15/1.02    inference(ennf_transformation,[],[f7])).
% 2.15/1.02  
% 2.15/1.02  fof(f14,plain,(
% 2.15/1.02    ! [X0,X1] : (? [X2] : r2_hidden(X2,k1_relat_1(X1)) | ~r2_hidden(X0,k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 2.15/1.02    inference(flattening,[],[f13])).
% 2.15/1.02  
% 2.15/1.02  fof(f26,plain,(
% 2.15/1.02    ! [X1] : (? [X2] : r2_hidden(X2,k1_relat_1(X1)) => r2_hidden(sK4(X1),k1_relat_1(X1)))),
% 2.15/1.02    introduced(choice_axiom,[])).
% 2.15/1.02  
% 2.15/1.02  fof(f27,plain,(
% 2.15/1.02    ! [X0,X1] : (r2_hidden(sK4(X1),k1_relat_1(X1)) | ~r2_hidden(X0,k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 2.15/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f14,f26])).
% 2.15/1.02  
% 2.15/1.02  fof(f39,plain,(
% 2.15/1.02    ( ! [X0,X1] : (r2_hidden(sK4(X1),k1_relat_1(X1)) | ~r2_hidden(X0,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.15/1.02    inference(cnf_transformation,[],[f27])).
% 2.15/1.02  
% 2.15/1.02  fof(f1,axiom,(
% 2.15/1.02    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.15/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.15/1.02  
% 2.15/1.02  fof(f10,plain,(
% 2.15/1.02    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) => v1_xboole_0(X0))),
% 2.15/1.02    inference(unused_predicate_definition_removal,[],[f1])).
% 2.15/1.02  
% 2.15/1.02  fof(f11,plain,(
% 2.15/1.02    ! [X0] : (v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0))),
% 2.15/1.02    inference(ennf_transformation,[],[f10])).
% 2.15/1.02  
% 2.15/1.02  fof(f16,plain,(
% 2.15/1.02    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 2.15/1.02    introduced(choice_axiom,[])).
% 2.15/1.02  
% 2.15/1.02  fof(f17,plain,(
% 2.15/1.02    ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0))),
% 2.15/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f16])).
% 2.15/1.02  
% 2.15/1.02  fof(f28,plain,(
% 2.15/1.02    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 2.15/1.02    inference(cnf_transformation,[],[f17])).
% 2.15/1.02  
% 2.15/1.02  fof(f2,axiom,(
% 2.15/1.02    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 2.15/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.15/1.02  
% 2.15/1.02  fof(f12,plain,(
% 2.15/1.02    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 2.15/1.02    inference(ennf_transformation,[],[f2])).
% 2.15/1.02  
% 2.15/1.02  fof(f29,plain,(
% 2.15/1.02    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 2.15/1.02    inference(cnf_transformation,[],[f12])).
% 2.15/1.02  
% 2.15/1.02  fof(f8,conjecture,(
% 2.15/1.02    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.15/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.15/1.02  
% 2.15/1.02  fof(f9,negated_conjecture,(
% 2.15/1.02    ~(k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0))),
% 2.15/1.02    inference(negated_conjecture,[],[f8])).
% 2.15/1.02  
% 2.15/1.02  fof(f15,plain,(
% 2.15/1.02    k1_xboole_0 != k2_relat_1(k1_xboole_0) | k1_xboole_0 != k1_relat_1(k1_xboole_0)),
% 2.15/1.02    inference(ennf_transformation,[],[f9])).
% 2.15/1.02  
% 2.15/1.02  fof(f40,plain,(
% 2.15/1.02    k1_xboole_0 != k2_relat_1(k1_xboole_0) | k1_xboole_0 != k1_relat_1(k1_xboole_0)),
% 2.15/1.02    inference(cnf_transformation,[],[f15])).
% 2.15/1.02  
% 2.15/1.02  fof(f6,axiom,(
% 2.15/1.02    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.15/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.15/1.02  
% 2.15/1.02  fof(f38,plain,(
% 2.15/1.02    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.15/1.02    inference(cnf_transformation,[],[f6])).
% 2.15/1.02  
% 2.15/1.02  fof(f30,plain,(
% 2.15/1.02    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 2.15/1.02    inference(cnf_transformation,[],[f19])).
% 2.15/1.02  
% 2.15/1.02  fof(f31,plain,(
% 2.15/1.02    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 2.15/1.02    inference(cnf_transformation,[],[f19])).
% 2.15/1.02  
% 2.15/1.02  fof(f42,plain,(
% 2.15/1.02    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 2.15/1.02    inference(equality_resolution,[],[f31])).
% 2.15/1.02  
% 2.15/1.02  cnf(c_221,plain,
% 2.15/1.02      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.15/1.02      theory(equality) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_2,plain,
% 2.15/1.02      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 2.15/1.02      inference(cnf_transformation,[],[f41]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_1289,plain,
% 2.15/1.02      ( r2_hidden(X0,k2_zfmisc_1(X1,k1_xboole_0))
% 2.15/1.02      | ~ r2_hidden(X2,k1_xboole_0)
% 2.15/1.02      | X0 != X2 ),
% 2.15/1.02      inference(resolution,[status(thm)],[c_221,c_2]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_219,plain,( X0 = X0 ),theory(equality) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_3541,plain,
% 2.15/1.02      ( r2_hidden(X0,k2_zfmisc_1(X1,k1_xboole_0))
% 2.15/1.02      | ~ r2_hidden(X0,k1_xboole_0) ),
% 2.15/1.02      inference(resolution,[status(thm)],[c_1289,c_219]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_5,plain,
% 2.15/1.02      ( ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
% 2.15/1.02      inference(cnf_transformation,[],[f33]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_396,plain,
% 2.15/1.02      ( r2_hidden(X0,k2_zfmisc_1(X0,X1)) != iProver_top ),
% 2.15/1.02      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_548,plain,
% 2.15/1.02      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 2.15/1.02      inference(superposition,[status(thm)],[c_2,c_396]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_554,plain,
% 2.15/1.02      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 2.15/1.02      inference(predicate_to_equality_rev,[status(thm)],[c_548]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_4033,plain,
% 2.15/1.02      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 2.15/1.02      inference(global_propositional_subsumption,[status(thm)],[c_3541,c_554]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_9,plain,
% 2.15/1.02      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.15/1.02      | r2_hidden(k4_tarski(X0,sK3(X1,X0)),X1) ),
% 2.15/1.02      inference(cnf_transformation,[],[f44]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_4452,plain,
% 2.15/1.02      ( ~ r2_hidden(X0,k1_relat_1(k1_xboole_0)) ),
% 2.15/1.02      inference(resolution,[status(thm)],[c_4033,c_9]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_11,plain,
% 2.15/1.02      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 2.15/1.02      | r2_hidden(sK4(X1),k1_relat_1(X1))
% 2.15/1.02      | ~ v1_relat_1(X1) ),
% 2.15/1.02      inference(cnf_transformation,[],[f39]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_0,plain,
% 2.15/1.02      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 2.15/1.02      inference(cnf_transformation,[],[f28]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_1,plain,
% 2.15/1.02      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 2.15/1.02      inference(cnf_transformation,[],[f29]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_118,plain,
% 2.15/1.02      ( r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0 ),
% 2.15/1.02      inference(resolution,[status(thm)],[c_0,c_1]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_12,negated_conjecture,
% 2.15/1.02      ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
% 2.15/1.02      | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
% 2.15/1.02      inference(cnf_transformation,[],[f40]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_490,plain,
% 2.15/1.02      ( r2_hidden(sK0(k2_relat_1(k1_xboole_0)),k2_relat_1(k1_xboole_0))
% 2.15/1.02      | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
% 2.15/1.02      inference(resolution,[status(thm)],[c_118,c_12]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_801,plain,
% 2.15/1.02      ( r2_hidden(sK4(k1_xboole_0),k1_relat_1(k1_xboole_0))
% 2.15/1.02      | ~ v1_relat_1(k1_xboole_0)
% 2.15/1.02      | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
% 2.15/1.02      inference(resolution,[status(thm)],[c_11,c_490]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_10,plain,
% 2.15/1.02      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.15/1.02      inference(cnf_transformation,[],[f38]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_391,plain,
% 2.15/1.02      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 2.15/1.02      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_505,plain,
% 2.15/1.02      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 2.15/1.02      inference(superposition,[status(thm)],[c_2,c_391]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_507,plain,
% 2.15/1.02      ( v1_relat_1(k1_xboole_0) ),
% 2.15/1.02      inference(predicate_to_equality_rev,[status(thm)],[c_505]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_812,plain,
% 2.15/1.02      ( r2_hidden(sK4(k1_xboole_0),k1_relat_1(k1_xboole_0))
% 2.15/1.02      | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
% 2.15/1.02      inference(global_propositional_subsumption,[status(thm)],[c_801,c_507]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_4,plain,
% 2.15/1.02      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 2.15/1.02      | k1_xboole_0 = X0
% 2.15/1.02      | k1_xboole_0 = X1 ),
% 2.15/1.02      inference(cnf_transformation,[],[f30]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_34,plain,
% 2.15/1.02      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 2.15/1.02      | k1_xboole_0 = k1_xboole_0 ),
% 2.15/1.02      inference(instantiation,[status(thm)],[c_4]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_3,plain,
% 2.15/1.02      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.15/1.02      inference(cnf_transformation,[],[f42]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_35,plain,
% 2.15/1.02      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 2.15/1.02      inference(instantiation,[status(thm)],[c_3]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_220,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_492,plain,
% 2.15/1.02      ( k1_relat_1(k1_xboole_0) != X0
% 2.15/1.02      | k1_xboole_0 != X0
% 2.15/1.02      | k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
% 2.15/1.02      inference(instantiation,[status(thm)],[c_220]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_493,plain,
% 2.15/1.02      ( k1_relat_1(k1_xboole_0) != k1_xboole_0
% 2.15/1.02      | k1_xboole_0 = k1_relat_1(k1_xboole_0)
% 2.15/1.02      | k1_xboole_0 != k1_xboole_0 ),
% 2.15/1.02      inference(instantiation,[status(thm)],[c_492]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_389,plain,
% 2.15/1.02      ( k1_xboole_0 = X0 | r2_hidden(sK0(X0),X0) = iProver_top ),
% 2.15/1.02      inference(predicate_to_equality,[status(thm)],[c_118]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_392,plain,
% 2.15/1.02      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 2.15/1.02      | r2_hidden(k4_tarski(X0,sK3(X1,X0)),X1) = iProver_top ),
% 2.15/1.02      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_758,plain,
% 2.15/1.02      ( r2_hidden(X0,k1_relat_1(k1_xboole_0)) != iProver_top ),
% 2.15/1.02      inference(superposition,[status(thm)],[c_392,c_548]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_866,plain,
% 2.15/1.02      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 2.15/1.02      inference(superposition,[status(thm)],[c_389,c_758]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_883,plain,
% 2.15/1.02      ( r2_hidden(sK4(k1_xboole_0),k1_relat_1(k1_xboole_0)) ),
% 2.15/1.02      inference(global_propositional_subsumption,
% 2.15/1.02                [status(thm)],
% 2.15/1.02                [c_812,c_34,c_35,c_493,c_507,c_801,c_866]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_4457,plain,
% 2.15/1.02      ( $false ),
% 2.15/1.02      inference(backward_subsumption_resolution,[status(thm)],[c_4452,c_883]) ).
% 2.15/1.02  
% 2.15/1.02  
% 2.15/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 2.15/1.02  
% 2.15/1.02  ------                               Statistics
% 2.15/1.02  
% 2.15/1.02  ------ Selected
% 2.15/1.02  
% 2.15/1.02  total_time:                             0.171
% 2.15/1.02  
%------------------------------------------------------------------------------
