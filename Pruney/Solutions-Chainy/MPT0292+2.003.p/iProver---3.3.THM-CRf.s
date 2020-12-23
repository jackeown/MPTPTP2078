%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:36:49 EST 2020

% Result     : Theorem 0.74s
% Output     : CNFRefutation 0.74s
% Verified   : 
% Statistics : Number of formulae       :   73 (  79 expanded)
%              Number of clauses        :   26 (  26 expanded)
%              Number of leaves         :   14 (  17 expanded)
%              Depth                    :   14
%              Number of atoms          :  226 ( 241 expanded)
%              Number of equality atoms :   82 (  84 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f21,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f98,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_tarski(X2,X1) )
     => r1_tarski(k3_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | ? [X2] :
          ( ~ r1_tarski(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f56,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r1_tarski(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r1_tarski(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | ( ~ r1_tarski(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f35,f56])).

fof(f99,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f47])).

fof(f49,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK2(X0,X1),X0)
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( r1_tarski(sK2(X0,X1),X0)
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK2(X0,X1),X0)
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( r1_tarski(sK2(X0,X1),X0)
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f48,f49])).

fof(f80,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f127,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f80])).

fof(f100,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | ~ r1_tarski(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f41])).

fof(f66,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f20,axiom,(
    ! [X0] : r1_tarski(k1_tarski(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f97,plain,(
    ! [X0] : r1_tarski(k1_tarski(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f12,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f79,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f119,plain,(
    ! [X0] : r1_tarski(k2_tarski(X0,X0),k1_zfmisc_1(X0)) ),
    inference(definition_unfolding,[],[f97,f79])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f43])).

fof(f45,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK1(X0,X1) != X0
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( sK1(X0,X1) = X0
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK1(X0,X1) != X0
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( sK1(X0,X1) = X0
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f44,f45])).

fof(f76,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f107,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k2_tarski(X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f76,f79])).

fof(f123,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k2_tarski(X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f107])).

fof(f124,plain,(
    ! [X3] : r2_hidden(X3,k2_tarski(X3,X3)) ),
    inference(equality_resolution,[],[f123])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f37])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f38,f39])).

fof(f60,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f23,conjecture,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,negated_conjecture,(
    ~ ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(negated_conjecture,[],[f23])).

fof(f36,plain,(
    ? [X0] : k3_tarski(k1_zfmisc_1(X0)) != X0 ),
    inference(ennf_transformation,[],[f24])).

fof(f58,plain,
    ( ? [X0] : k3_tarski(k1_zfmisc_1(X0)) != X0
   => k3_tarski(k1_zfmisc_1(sK4)) != sK4 ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
    k3_tarski(k1_zfmisc_1(sK4)) != sK4 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f36,f58])).

fof(f101,plain,(
    k3_tarski(k1_zfmisc_1(sK4)) != sK4 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_35,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(X0,k3_tarski(X1)) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1538,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X0,k3_tarski(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_37,plain,
    ( r2_hidden(sK3(X0,X1),X0)
    | r1_tarski(k3_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1536,plain,
    ( r2_hidden(sK3(X0,X1),X0) = iProver_top
    | r1_tarski(k3_tarski(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_21,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f127])).

cnf(c_1550,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2830,plain,
    ( r1_tarski(sK3(k1_zfmisc_1(X0),X1),X0) = iProver_top
    | r1_tarski(k3_tarski(k1_zfmisc_1(X0)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1536,c_1550])).

cnf(c_36,plain,
    ( ~ r1_tarski(sK3(X0,X1),X1)
    | r1_tarski(k3_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_1537,plain,
    ( r1_tarski(sK3(X0,X1),X1) != iProver_top
    | r1_tarski(k3_tarski(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_6149,plain,
    ( r1_tarski(k3_tarski(k1_zfmisc_1(X0)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2830,c_1537])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1565,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_6768,plain,
    ( k3_tarski(k1_zfmisc_1(X0)) = X0
    | r1_tarski(X0,k3_tarski(k1_zfmisc_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6149,c_1565])).

cnf(c_7152,plain,
    ( k3_tarski(k1_zfmisc_1(X0)) = X0
    | r2_hidden(X0,k1_zfmisc_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1538,c_6768])).

cnf(c_34,plain,
    ( r1_tarski(k2_tarski(X0,X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_1539,plain,
    ( r1_tarski(k2_tarski(X0,X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_16,plain,
    ( r2_hidden(X0,k2_tarski(X0,X0)) ),
    inference(cnf_transformation,[],[f124])).

cnf(c_1555,plain,
    ( r2_hidden(X0,k2_tarski(X0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1566,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_4571,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r1_tarski(k2_tarski(X0,X0),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1555,c_1566])).

cnf(c_4631,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1539,c_4571])).

cnf(c_7166,plain,
    ( k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7152,c_4631])).

cnf(c_38,negated_conjecture,
    ( k3_tarski(k1_zfmisc_1(sK4)) != sK4 ),
    inference(cnf_transformation,[],[f101])).

cnf(c_7169,plain,
    ( sK4 != sK4 ),
    inference(demodulation,[status(thm)],[c_7166,c_38])).

cnf(c_7180,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_7169])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:42:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 0.74/1.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.74/1.02  
% 0.74/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.74/1.02  
% 0.74/1.02  ------  iProver source info
% 0.74/1.02  
% 0.74/1.02  git: date: 2020-06-30 10:37:57 +0100
% 0.74/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.74/1.02  git: non_committed_changes: false
% 0.74/1.02  git: last_make_outside_of_git: false
% 0.74/1.02  
% 0.74/1.02  ------ 
% 0.74/1.02  
% 0.74/1.02  ------ Input Options
% 0.74/1.02  
% 0.74/1.02  --out_options                           all
% 0.74/1.02  --tptp_safe_out                         true
% 0.74/1.02  --problem_path                          ""
% 0.74/1.02  --include_path                          ""
% 0.74/1.02  --clausifier                            res/vclausify_rel
% 0.74/1.02  --clausifier_options                    --mode clausify
% 0.74/1.02  --stdin                                 false
% 0.74/1.02  --stats_out                             all
% 0.74/1.02  
% 0.74/1.02  ------ General Options
% 0.74/1.02  
% 0.74/1.02  --fof                                   false
% 0.74/1.02  --time_out_real                         305.
% 0.74/1.02  --time_out_virtual                      -1.
% 0.74/1.02  --symbol_type_check                     false
% 0.74/1.02  --clausify_out                          false
% 0.74/1.02  --sig_cnt_out                           false
% 0.74/1.02  --trig_cnt_out                          false
% 0.74/1.02  --trig_cnt_out_tolerance                1.
% 0.74/1.02  --trig_cnt_out_sk_spl                   false
% 0.74/1.02  --abstr_cl_out                          false
% 0.74/1.02  
% 0.74/1.02  ------ Global Options
% 0.74/1.02  
% 0.74/1.02  --schedule                              default
% 0.74/1.02  --add_important_lit                     false
% 0.74/1.02  --prop_solver_per_cl                    1000
% 0.74/1.02  --min_unsat_core                        false
% 0.74/1.02  --soft_assumptions                      false
% 0.74/1.02  --soft_lemma_size                       3
% 0.74/1.02  --prop_impl_unit_size                   0
% 0.74/1.02  --prop_impl_unit                        []
% 0.74/1.02  --share_sel_clauses                     true
% 0.74/1.02  --reset_solvers                         false
% 0.74/1.02  --bc_imp_inh                            [conj_cone]
% 0.74/1.02  --conj_cone_tolerance                   3.
% 0.74/1.02  --extra_neg_conj                        none
% 0.74/1.02  --large_theory_mode                     true
% 0.74/1.02  --prolific_symb_bound                   200
% 0.74/1.02  --lt_threshold                          2000
% 0.74/1.02  --clause_weak_htbl                      true
% 0.74/1.02  --gc_record_bc_elim                     false
% 0.74/1.02  
% 0.74/1.02  ------ Preprocessing Options
% 0.74/1.02  
% 0.74/1.02  --preprocessing_flag                    true
% 0.74/1.02  --time_out_prep_mult                    0.1
% 0.74/1.02  --splitting_mode                        input
% 0.74/1.02  --splitting_grd                         true
% 0.74/1.02  --splitting_cvd                         false
% 0.74/1.02  --splitting_cvd_svl                     false
% 0.74/1.02  --splitting_nvd                         32
% 0.74/1.02  --sub_typing                            true
% 0.74/1.02  --prep_gs_sim                           true
% 0.74/1.02  --prep_unflatten                        true
% 0.74/1.02  --prep_res_sim                          true
% 0.74/1.02  --prep_upred                            true
% 0.74/1.02  --prep_sem_filter                       exhaustive
% 0.74/1.02  --prep_sem_filter_out                   false
% 0.74/1.02  --pred_elim                             true
% 0.74/1.02  --res_sim_input                         true
% 0.74/1.02  --eq_ax_congr_red                       true
% 0.74/1.02  --pure_diseq_elim                       true
% 0.74/1.02  --brand_transform                       false
% 0.74/1.02  --non_eq_to_eq                          false
% 0.74/1.02  --prep_def_merge                        true
% 0.74/1.02  --prep_def_merge_prop_impl              false
% 0.74/1.02  --prep_def_merge_mbd                    true
% 0.74/1.02  --prep_def_merge_tr_red                 false
% 0.74/1.02  --prep_def_merge_tr_cl                  false
% 0.74/1.02  --smt_preprocessing                     true
% 0.74/1.02  --smt_ac_axioms                         fast
% 0.74/1.02  --preprocessed_out                      false
% 0.74/1.02  --preprocessed_stats                    false
% 0.74/1.02  
% 0.74/1.02  ------ Abstraction refinement Options
% 0.74/1.02  
% 0.74/1.02  --abstr_ref                             []
% 0.74/1.02  --abstr_ref_prep                        false
% 0.74/1.02  --abstr_ref_until_sat                   false
% 0.74/1.02  --abstr_ref_sig_restrict                funpre
% 0.74/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 0.74/1.02  --abstr_ref_under                       []
% 0.74/1.02  
% 0.74/1.02  ------ SAT Options
% 0.74/1.02  
% 0.74/1.02  --sat_mode                              false
% 0.74/1.02  --sat_fm_restart_options                ""
% 0.74/1.02  --sat_gr_def                            false
% 0.74/1.02  --sat_epr_types                         true
% 0.74/1.02  --sat_non_cyclic_types                  false
% 0.74/1.02  --sat_finite_models                     false
% 0.74/1.02  --sat_fm_lemmas                         false
% 0.74/1.02  --sat_fm_prep                           false
% 0.74/1.02  --sat_fm_uc_incr                        true
% 0.74/1.02  --sat_out_model                         small
% 0.74/1.02  --sat_out_clauses                       false
% 0.74/1.02  
% 0.74/1.02  ------ QBF Options
% 0.74/1.02  
% 0.74/1.02  --qbf_mode                              false
% 0.74/1.02  --qbf_elim_univ                         false
% 0.74/1.02  --qbf_dom_inst                          none
% 0.74/1.02  --qbf_dom_pre_inst                      false
% 0.74/1.02  --qbf_sk_in                             false
% 0.74/1.02  --qbf_pred_elim                         true
% 0.74/1.02  --qbf_split                             512
% 0.74/1.02  
% 0.74/1.02  ------ BMC1 Options
% 0.74/1.02  
% 0.74/1.02  --bmc1_incremental                      false
% 0.74/1.02  --bmc1_axioms                           reachable_all
% 0.74/1.02  --bmc1_min_bound                        0
% 0.74/1.02  --bmc1_max_bound                        -1
% 0.74/1.02  --bmc1_max_bound_default                -1
% 0.74/1.02  --bmc1_symbol_reachability              true
% 0.74/1.02  --bmc1_property_lemmas                  false
% 0.74/1.02  --bmc1_k_induction                      false
% 0.74/1.02  --bmc1_non_equiv_states                 false
% 0.74/1.02  --bmc1_deadlock                         false
% 0.74/1.02  --bmc1_ucm                              false
% 0.74/1.02  --bmc1_add_unsat_core                   none
% 0.74/1.02  --bmc1_unsat_core_children              false
% 0.74/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 0.74/1.02  --bmc1_out_stat                         full
% 0.74/1.02  --bmc1_ground_init                      false
% 0.74/1.02  --bmc1_pre_inst_next_state              false
% 0.74/1.02  --bmc1_pre_inst_state                   false
% 0.74/1.02  --bmc1_pre_inst_reach_state             false
% 0.74/1.02  --bmc1_out_unsat_core                   false
% 0.74/1.02  --bmc1_aig_witness_out                  false
% 0.74/1.02  --bmc1_verbose                          false
% 0.74/1.02  --bmc1_dump_clauses_tptp                false
% 0.74/1.02  --bmc1_dump_unsat_core_tptp             false
% 0.74/1.02  --bmc1_dump_file                        -
% 0.74/1.02  --bmc1_ucm_expand_uc_limit              128
% 0.74/1.02  --bmc1_ucm_n_expand_iterations          6
% 0.74/1.02  --bmc1_ucm_extend_mode                  1
% 0.74/1.02  --bmc1_ucm_init_mode                    2
% 0.74/1.02  --bmc1_ucm_cone_mode                    none
% 0.74/1.02  --bmc1_ucm_reduced_relation_type        0
% 0.74/1.02  --bmc1_ucm_relax_model                  4
% 0.74/1.02  --bmc1_ucm_full_tr_after_sat            true
% 0.74/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 0.74/1.02  --bmc1_ucm_layered_model                none
% 0.74/1.02  --bmc1_ucm_max_lemma_size               10
% 0.74/1.02  
% 0.74/1.02  ------ AIG Options
% 0.74/1.02  
% 0.74/1.02  --aig_mode                              false
% 0.74/1.02  
% 0.74/1.02  ------ Instantiation Options
% 0.74/1.02  
% 0.74/1.02  --instantiation_flag                    true
% 0.74/1.02  --inst_sos_flag                         false
% 0.74/1.02  --inst_sos_phase                        true
% 0.74/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.74/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.74/1.02  --inst_lit_sel_side                     num_symb
% 0.74/1.02  --inst_solver_per_active                1400
% 0.74/1.02  --inst_solver_calls_frac                1.
% 0.74/1.02  --inst_passive_queue_type               priority_queues
% 0.74/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.74/1.02  --inst_passive_queues_freq              [25;2]
% 0.74/1.02  --inst_dismatching                      true
% 0.74/1.02  --inst_eager_unprocessed_to_passive     true
% 0.74/1.02  --inst_prop_sim_given                   true
% 0.74/1.02  --inst_prop_sim_new                     false
% 0.74/1.02  --inst_subs_new                         false
% 0.74/1.02  --inst_eq_res_simp                      false
% 0.74/1.02  --inst_subs_given                       false
% 0.74/1.02  --inst_orphan_elimination               true
% 0.74/1.02  --inst_learning_loop_flag               true
% 0.74/1.02  --inst_learning_start                   3000
% 0.74/1.02  --inst_learning_factor                  2
% 0.74/1.02  --inst_start_prop_sim_after_learn       3
% 0.74/1.02  --inst_sel_renew                        solver
% 0.74/1.02  --inst_lit_activity_flag                true
% 0.74/1.02  --inst_restr_to_given                   false
% 0.74/1.02  --inst_activity_threshold               500
% 0.74/1.02  --inst_out_proof                        true
% 0.74/1.02  
% 0.74/1.02  ------ Resolution Options
% 0.74/1.02  
% 0.74/1.02  --resolution_flag                       true
% 0.74/1.02  --res_lit_sel                           adaptive
% 0.74/1.02  --res_lit_sel_side                      none
% 0.74/1.02  --res_ordering                          kbo
% 0.74/1.02  --res_to_prop_solver                    active
% 0.74/1.02  --res_prop_simpl_new                    false
% 0.74/1.02  --res_prop_simpl_given                  true
% 0.74/1.02  --res_passive_queue_type                priority_queues
% 0.74/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.74/1.02  --res_passive_queues_freq               [15;5]
% 0.74/1.02  --res_forward_subs                      full
% 0.74/1.02  --res_backward_subs                     full
% 0.74/1.02  --res_forward_subs_resolution           true
% 0.74/1.02  --res_backward_subs_resolution          true
% 0.74/1.02  --res_orphan_elimination                true
% 0.74/1.02  --res_time_limit                        2.
% 0.74/1.02  --res_out_proof                         true
% 0.74/1.02  
% 0.74/1.02  ------ Superposition Options
% 0.74/1.02  
% 0.74/1.02  --superposition_flag                    true
% 0.74/1.02  --sup_passive_queue_type                priority_queues
% 0.74/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.74/1.02  --sup_passive_queues_freq               [8;1;4]
% 0.74/1.02  --demod_completeness_check              fast
% 0.74/1.02  --demod_use_ground                      true
% 0.74/1.02  --sup_to_prop_solver                    passive
% 0.74/1.02  --sup_prop_simpl_new                    true
% 0.74/1.02  --sup_prop_simpl_given                  true
% 0.74/1.02  --sup_fun_splitting                     false
% 0.74/1.02  --sup_smt_interval                      50000
% 0.74/1.02  
% 0.74/1.02  ------ Superposition Simplification Setup
% 0.74/1.02  
% 0.74/1.02  --sup_indices_passive                   []
% 0.74/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.74/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.74/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.74/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 0.74/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.74/1.02  --sup_full_bw                           [BwDemod]
% 0.74/1.02  --sup_immed_triv                        [TrivRules]
% 0.74/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.74/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.74/1.02  --sup_immed_bw_main                     []
% 0.74/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.74/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 0.74/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.74/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.74/1.02  
% 0.74/1.02  ------ Combination Options
% 0.74/1.02  
% 0.74/1.02  --comb_res_mult                         3
% 0.74/1.02  --comb_sup_mult                         2
% 0.74/1.02  --comb_inst_mult                        10
% 0.74/1.02  
% 0.74/1.02  ------ Debug Options
% 0.74/1.02  
% 0.74/1.02  --dbg_backtrace                         false
% 0.74/1.02  --dbg_dump_prop_clauses                 false
% 0.74/1.02  --dbg_dump_prop_clauses_file            -
% 0.74/1.02  --dbg_out_stat                          false
% 0.74/1.02  ------ Parsing...
% 0.74/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.74/1.02  
% 0.74/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 0.74/1.02  
% 0.74/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.74/1.02  
% 0.74/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 0.74/1.02  ------ Proving...
% 0.74/1.02  ------ Problem Properties 
% 0.74/1.02  
% 0.74/1.02  
% 0.74/1.02  clauses                                 38
% 0.74/1.02  conjectures                             1
% 0.74/1.02  EPR                                     7
% 0.74/1.02  Horn                                    29
% 0.74/1.02  unary                                   16
% 0.74/1.02  binary                                  12
% 0.74/1.02  lits                                    73
% 0.74/1.02  lits eq                                 23
% 0.74/1.02  fd_pure                                 0
% 0.74/1.02  fd_pseudo                               0
% 0.74/1.02  fd_cond                                 3
% 0.74/1.02  fd_pseudo_cond                          8
% 0.74/1.02  AC symbols                              0
% 0.74/1.02  
% 0.74/1.02  ------ Schedule dynamic 5 is on 
% 0.74/1.02  
% 0.74/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 0.74/1.02  
% 0.74/1.02  
% 0.74/1.02  ------ 
% 0.74/1.02  Current options:
% 0.74/1.02  ------ 
% 0.74/1.02  
% 0.74/1.02  ------ Input Options
% 0.74/1.02  
% 0.74/1.02  --out_options                           all
% 0.74/1.02  --tptp_safe_out                         true
% 0.74/1.02  --problem_path                          ""
% 0.74/1.02  --include_path                          ""
% 0.74/1.02  --clausifier                            res/vclausify_rel
% 0.74/1.02  --clausifier_options                    --mode clausify
% 0.74/1.02  --stdin                                 false
% 0.74/1.02  --stats_out                             all
% 0.74/1.02  
% 0.74/1.02  ------ General Options
% 0.74/1.02  
% 0.74/1.02  --fof                                   false
% 0.74/1.02  --time_out_real                         305.
% 0.74/1.02  --time_out_virtual                      -1.
% 0.74/1.02  --symbol_type_check                     false
% 0.74/1.02  --clausify_out                          false
% 0.74/1.02  --sig_cnt_out                           false
% 0.74/1.02  --trig_cnt_out                          false
% 0.74/1.02  --trig_cnt_out_tolerance                1.
% 0.74/1.02  --trig_cnt_out_sk_spl                   false
% 0.74/1.02  --abstr_cl_out                          false
% 0.74/1.02  
% 0.74/1.02  ------ Global Options
% 0.74/1.02  
% 0.74/1.02  --schedule                              default
% 0.74/1.02  --add_important_lit                     false
% 0.74/1.02  --prop_solver_per_cl                    1000
% 0.74/1.02  --min_unsat_core                        false
% 0.74/1.02  --soft_assumptions                      false
% 0.74/1.02  --soft_lemma_size                       3
% 0.74/1.02  --prop_impl_unit_size                   0
% 0.74/1.02  --prop_impl_unit                        []
% 0.74/1.02  --share_sel_clauses                     true
% 0.74/1.02  --reset_solvers                         false
% 0.74/1.02  --bc_imp_inh                            [conj_cone]
% 0.74/1.02  --conj_cone_tolerance                   3.
% 0.74/1.02  --extra_neg_conj                        none
% 0.74/1.02  --large_theory_mode                     true
% 0.74/1.02  --prolific_symb_bound                   200
% 0.74/1.02  --lt_threshold                          2000
% 0.74/1.02  --clause_weak_htbl                      true
% 0.74/1.02  --gc_record_bc_elim                     false
% 0.74/1.02  
% 0.74/1.02  ------ Preprocessing Options
% 0.74/1.02  
% 0.74/1.02  --preprocessing_flag                    true
% 0.74/1.02  --time_out_prep_mult                    0.1
% 0.74/1.02  --splitting_mode                        input
% 0.74/1.02  --splitting_grd                         true
% 0.74/1.02  --splitting_cvd                         false
% 0.74/1.02  --splitting_cvd_svl                     false
% 0.74/1.02  --splitting_nvd                         32
% 0.74/1.02  --sub_typing                            true
% 0.74/1.02  --prep_gs_sim                           true
% 0.74/1.02  --prep_unflatten                        true
% 0.74/1.02  --prep_res_sim                          true
% 0.74/1.02  --prep_upred                            true
% 0.74/1.02  --prep_sem_filter                       exhaustive
% 0.74/1.02  --prep_sem_filter_out                   false
% 0.74/1.02  --pred_elim                             true
% 0.74/1.02  --res_sim_input                         true
% 0.74/1.02  --eq_ax_congr_red                       true
% 0.74/1.02  --pure_diseq_elim                       true
% 0.74/1.02  --brand_transform                       false
% 0.74/1.02  --non_eq_to_eq                          false
% 0.74/1.02  --prep_def_merge                        true
% 0.74/1.02  --prep_def_merge_prop_impl              false
% 0.74/1.02  --prep_def_merge_mbd                    true
% 0.74/1.02  --prep_def_merge_tr_red                 false
% 0.74/1.02  --prep_def_merge_tr_cl                  false
% 0.74/1.02  --smt_preprocessing                     true
% 0.74/1.02  --smt_ac_axioms                         fast
% 0.74/1.02  --preprocessed_out                      false
% 0.74/1.02  --preprocessed_stats                    false
% 0.74/1.02  
% 0.74/1.02  ------ Abstraction refinement Options
% 0.74/1.02  
% 0.74/1.02  --abstr_ref                             []
% 0.74/1.02  --abstr_ref_prep                        false
% 0.74/1.02  --abstr_ref_until_sat                   false
% 0.74/1.02  --abstr_ref_sig_restrict                funpre
% 0.74/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 0.74/1.02  --abstr_ref_under                       []
% 0.74/1.02  
% 0.74/1.02  ------ SAT Options
% 0.74/1.02  
% 0.74/1.02  --sat_mode                              false
% 0.74/1.02  --sat_fm_restart_options                ""
% 0.74/1.02  --sat_gr_def                            false
% 0.74/1.02  --sat_epr_types                         true
% 0.74/1.02  --sat_non_cyclic_types                  false
% 0.74/1.02  --sat_finite_models                     false
% 0.74/1.02  --sat_fm_lemmas                         false
% 0.74/1.02  --sat_fm_prep                           false
% 0.74/1.02  --sat_fm_uc_incr                        true
% 0.74/1.02  --sat_out_model                         small
% 0.74/1.02  --sat_out_clauses                       false
% 0.74/1.02  
% 0.74/1.02  ------ QBF Options
% 0.74/1.02  
% 0.74/1.02  --qbf_mode                              false
% 0.74/1.02  --qbf_elim_univ                         false
% 0.74/1.02  --qbf_dom_inst                          none
% 0.74/1.02  --qbf_dom_pre_inst                      false
% 0.74/1.02  --qbf_sk_in                             false
% 0.74/1.02  --qbf_pred_elim                         true
% 0.74/1.02  --qbf_split                             512
% 0.74/1.02  
% 0.74/1.02  ------ BMC1 Options
% 0.74/1.02  
% 0.74/1.02  --bmc1_incremental                      false
% 0.74/1.02  --bmc1_axioms                           reachable_all
% 0.74/1.02  --bmc1_min_bound                        0
% 0.74/1.02  --bmc1_max_bound                        -1
% 0.74/1.02  --bmc1_max_bound_default                -1
% 0.74/1.02  --bmc1_symbol_reachability              true
% 0.74/1.02  --bmc1_property_lemmas                  false
% 0.74/1.02  --bmc1_k_induction                      false
% 0.74/1.02  --bmc1_non_equiv_states                 false
% 0.74/1.02  --bmc1_deadlock                         false
% 0.74/1.02  --bmc1_ucm                              false
% 0.74/1.02  --bmc1_add_unsat_core                   none
% 0.74/1.02  --bmc1_unsat_core_children              false
% 0.74/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 0.74/1.02  --bmc1_out_stat                         full
% 0.74/1.02  --bmc1_ground_init                      false
% 0.74/1.02  --bmc1_pre_inst_next_state              false
% 0.74/1.02  --bmc1_pre_inst_state                   false
% 0.74/1.02  --bmc1_pre_inst_reach_state             false
% 0.74/1.02  --bmc1_out_unsat_core                   false
% 0.74/1.02  --bmc1_aig_witness_out                  false
% 0.74/1.02  --bmc1_verbose                          false
% 0.74/1.02  --bmc1_dump_clauses_tptp                false
% 0.74/1.02  --bmc1_dump_unsat_core_tptp             false
% 0.74/1.02  --bmc1_dump_file                        -
% 0.74/1.02  --bmc1_ucm_expand_uc_limit              128
% 0.74/1.02  --bmc1_ucm_n_expand_iterations          6
% 0.74/1.02  --bmc1_ucm_extend_mode                  1
% 0.74/1.02  --bmc1_ucm_init_mode                    2
% 0.74/1.02  --bmc1_ucm_cone_mode                    none
% 0.74/1.02  --bmc1_ucm_reduced_relation_type        0
% 0.74/1.02  --bmc1_ucm_relax_model                  4
% 0.74/1.02  --bmc1_ucm_full_tr_after_sat            true
% 0.74/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 0.74/1.02  --bmc1_ucm_layered_model                none
% 0.74/1.02  --bmc1_ucm_max_lemma_size               10
% 0.74/1.02  
% 0.74/1.02  ------ AIG Options
% 0.74/1.02  
% 0.74/1.02  --aig_mode                              false
% 0.74/1.02  
% 0.74/1.02  ------ Instantiation Options
% 0.74/1.02  
% 0.74/1.02  --instantiation_flag                    true
% 0.74/1.02  --inst_sos_flag                         false
% 0.74/1.02  --inst_sos_phase                        true
% 0.74/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.74/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.74/1.02  --inst_lit_sel_side                     none
% 0.74/1.02  --inst_solver_per_active                1400
% 0.74/1.02  --inst_solver_calls_frac                1.
% 0.74/1.02  --inst_passive_queue_type               priority_queues
% 0.74/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.74/1.02  --inst_passive_queues_freq              [25;2]
% 0.74/1.02  --inst_dismatching                      true
% 0.74/1.02  --inst_eager_unprocessed_to_passive     true
% 0.74/1.02  --inst_prop_sim_given                   true
% 0.74/1.02  --inst_prop_sim_new                     false
% 0.74/1.02  --inst_subs_new                         false
% 0.74/1.02  --inst_eq_res_simp                      false
% 0.74/1.02  --inst_subs_given                       false
% 0.74/1.02  --inst_orphan_elimination               true
% 0.74/1.02  --inst_learning_loop_flag               true
% 0.74/1.02  --inst_learning_start                   3000
% 0.74/1.02  --inst_learning_factor                  2
% 0.74/1.02  --inst_start_prop_sim_after_learn       3
% 0.74/1.02  --inst_sel_renew                        solver
% 0.74/1.02  --inst_lit_activity_flag                true
% 0.74/1.02  --inst_restr_to_given                   false
% 0.74/1.02  --inst_activity_threshold               500
% 0.74/1.02  --inst_out_proof                        true
% 0.74/1.02  
% 0.74/1.02  ------ Resolution Options
% 0.74/1.02  
% 0.74/1.02  --resolution_flag                       false
% 0.74/1.02  --res_lit_sel                           adaptive
% 0.74/1.02  --res_lit_sel_side                      none
% 0.74/1.02  --res_ordering                          kbo
% 0.74/1.02  --res_to_prop_solver                    active
% 0.74/1.02  --res_prop_simpl_new                    false
% 0.74/1.02  --res_prop_simpl_given                  true
% 0.74/1.02  --res_passive_queue_type                priority_queues
% 0.74/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.74/1.02  --res_passive_queues_freq               [15;5]
% 0.74/1.02  --res_forward_subs                      full
% 0.74/1.02  --res_backward_subs                     full
% 0.74/1.02  --res_forward_subs_resolution           true
% 0.74/1.02  --res_backward_subs_resolution          true
% 0.74/1.02  --res_orphan_elimination                true
% 0.74/1.02  --res_time_limit                        2.
% 0.74/1.02  --res_out_proof                         true
% 0.74/1.02  
% 0.74/1.02  ------ Superposition Options
% 0.74/1.02  
% 0.74/1.02  --superposition_flag                    true
% 0.74/1.02  --sup_passive_queue_type                priority_queues
% 0.74/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.74/1.02  --sup_passive_queues_freq               [8;1;4]
% 0.74/1.02  --demod_completeness_check              fast
% 0.74/1.02  --demod_use_ground                      true
% 0.74/1.02  --sup_to_prop_solver                    passive
% 0.74/1.02  --sup_prop_simpl_new                    true
% 0.74/1.02  --sup_prop_simpl_given                  true
% 0.74/1.02  --sup_fun_splitting                     false
% 0.74/1.02  --sup_smt_interval                      50000
% 0.74/1.02  
% 0.74/1.02  ------ Superposition Simplification Setup
% 0.74/1.02  
% 0.74/1.02  --sup_indices_passive                   []
% 0.74/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.74/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.74/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.74/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 0.74/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.74/1.02  --sup_full_bw                           [BwDemod]
% 0.74/1.02  --sup_immed_triv                        [TrivRules]
% 0.74/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.74/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.74/1.02  --sup_immed_bw_main                     []
% 0.74/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.74/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 0.74/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.74/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.74/1.02  
% 0.74/1.02  ------ Combination Options
% 0.74/1.02  
% 0.74/1.02  --comb_res_mult                         3
% 0.74/1.02  --comb_sup_mult                         2
% 0.74/1.02  --comb_inst_mult                        10
% 0.74/1.02  
% 0.74/1.02  ------ Debug Options
% 0.74/1.02  
% 0.74/1.02  --dbg_backtrace                         false
% 0.74/1.02  --dbg_dump_prop_clauses                 false
% 0.74/1.02  --dbg_dump_prop_clauses_file            -
% 0.74/1.02  --dbg_out_stat                          false
% 0.74/1.02  
% 0.74/1.02  
% 0.74/1.02  
% 0.74/1.02  
% 0.74/1.02  ------ Proving...
% 0.74/1.02  
% 0.74/1.02  
% 0.74/1.02  % SZS status Theorem for theBenchmark.p
% 0.74/1.02  
% 0.74/1.02   Resolution empty clause
% 0.74/1.02  
% 0.74/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 0.74/1.02  
% 0.74/1.02  fof(f21,axiom,(
% 0.74/1.02    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(X0,k3_tarski(X1)))),
% 0.74/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.74/1.02  
% 0.74/1.02  fof(f34,plain,(
% 0.74/1.02    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1))),
% 0.74/1.02    inference(ennf_transformation,[],[f21])).
% 0.74/1.02  
% 0.74/1.02  fof(f98,plain,(
% 0.74/1.02    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1)) )),
% 0.74/1.02    inference(cnf_transformation,[],[f34])).
% 0.74/1.02  
% 0.74/1.02  fof(f22,axiom,(
% 0.74/1.02    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r1_tarski(X2,X1)) => r1_tarski(k3_tarski(X0),X1))),
% 0.74/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.74/1.02  
% 0.74/1.02  fof(f35,plain,(
% 0.74/1.02    ! [X0,X1] : (r1_tarski(k3_tarski(X0),X1) | ? [X2] : (~r1_tarski(X2,X1) & r2_hidden(X2,X0)))),
% 0.74/1.02    inference(ennf_transformation,[],[f22])).
% 0.74/1.02  
% 0.74/1.02  fof(f56,plain,(
% 0.74/1.02    ! [X1,X0] : (? [X2] : (~r1_tarski(X2,X1) & r2_hidden(X2,X0)) => (~r1_tarski(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 0.74/1.02    introduced(choice_axiom,[])).
% 0.74/1.02  
% 0.74/1.02  fof(f57,plain,(
% 0.74/1.02    ! [X0,X1] : (r1_tarski(k3_tarski(X0),X1) | (~r1_tarski(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 0.74/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f35,f56])).
% 0.74/1.02  
% 0.74/1.02  fof(f99,plain,(
% 0.74/1.02    ( ! [X0,X1] : (r1_tarski(k3_tarski(X0),X1) | r2_hidden(sK3(X0,X1),X0)) )),
% 0.74/1.02    inference(cnf_transformation,[],[f57])).
% 0.74/1.02  
% 0.74/1.02  fof(f13,axiom,(
% 0.74/1.02    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.74/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.74/1.02  
% 0.74/1.02  fof(f47,plain,(
% 0.74/1.02    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.74/1.02    inference(nnf_transformation,[],[f13])).
% 0.74/1.02  
% 0.74/1.02  fof(f48,plain,(
% 0.74/1.02    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.74/1.02    inference(rectify,[],[f47])).
% 0.74/1.02  
% 0.74/1.02  fof(f49,plain,(
% 0.74/1.02    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 0.74/1.02    introduced(choice_axiom,[])).
% 0.74/1.02  
% 0.74/1.02  fof(f50,plain,(
% 0.74/1.02    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.74/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f48,f49])).
% 0.74/1.02  
% 0.74/1.02  fof(f80,plain,(
% 0.74/1.02    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.74/1.02    inference(cnf_transformation,[],[f50])).
% 0.74/1.02  
% 0.74/1.02  fof(f127,plain,(
% 0.74/1.02    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 0.74/1.02    inference(equality_resolution,[],[f80])).
% 0.74/1.02  
% 0.74/1.02  fof(f100,plain,(
% 0.74/1.02    ( ! [X0,X1] : (r1_tarski(k3_tarski(X0),X1) | ~r1_tarski(sK3(X0,X1),X1)) )),
% 0.74/1.02    inference(cnf_transformation,[],[f57])).
% 0.74/1.02  
% 0.74/1.02  fof(f3,axiom,(
% 0.74/1.02    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.74/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.74/1.02  
% 0.74/1.02  fof(f41,plain,(
% 0.74/1.02    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.74/1.02    inference(nnf_transformation,[],[f3])).
% 0.74/1.02  
% 0.74/1.02  fof(f42,plain,(
% 0.74/1.02    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.74/1.02    inference(flattening,[],[f41])).
% 0.74/1.02  
% 0.74/1.02  fof(f66,plain,(
% 0.74/1.02    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 0.74/1.02    inference(cnf_transformation,[],[f42])).
% 0.74/1.02  
% 0.74/1.02  fof(f20,axiom,(
% 0.74/1.02    ! [X0] : r1_tarski(k1_tarski(X0),k1_zfmisc_1(X0))),
% 0.74/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.74/1.02  
% 0.74/1.02  fof(f97,plain,(
% 0.74/1.02    ( ! [X0] : (r1_tarski(k1_tarski(X0),k1_zfmisc_1(X0))) )),
% 0.74/1.02    inference(cnf_transformation,[],[f20])).
% 0.74/1.02  
% 0.74/1.02  fof(f12,axiom,(
% 0.74/1.02    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.74/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.74/1.02  
% 0.74/1.02  fof(f79,plain,(
% 0.74/1.02    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.74/1.02    inference(cnf_transformation,[],[f12])).
% 0.74/1.02  
% 0.74/1.02  fof(f119,plain,(
% 0.74/1.02    ( ! [X0] : (r1_tarski(k2_tarski(X0,X0),k1_zfmisc_1(X0))) )),
% 0.74/1.02    inference(definition_unfolding,[],[f97,f79])).
% 0.74/1.02  
% 0.74/1.02  fof(f11,axiom,(
% 0.74/1.02    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.74/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.74/1.02  
% 0.74/1.02  fof(f43,plain,(
% 0.74/1.02    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 0.74/1.02    inference(nnf_transformation,[],[f11])).
% 0.74/1.02  
% 0.74/1.02  fof(f44,plain,(
% 0.74/1.02    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.74/1.02    inference(rectify,[],[f43])).
% 0.74/1.02  
% 0.74/1.02  fof(f45,plain,(
% 0.74/1.02    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1))))),
% 0.74/1.02    introduced(choice_axiom,[])).
% 0.74/1.02  
% 0.74/1.02  fof(f46,plain,(
% 0.74/1.02    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.74/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f44,f45])).
% 0.74/1.02  
% 0.74/1.02  fof(f76,plain,(
% 0.74/1.02    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 0.74/1.02    inference(cnf_transformation,[],[f46])).
% 0.74/1.02  
% 0.74/1.02  fof(f107,plain,(
% 0.74/1.02    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k2_tarski(X0,X0) != X1) )),
% 0.74/1.02    inference(definition_unfolding,[],[f76,f79])).
% 0.74/1.02  
% 0.74/1.02  fof(f123,plain,(
% 0.74/1.02    ( ! [X3,X1] : (r2_hidden(X3,X1) | k2_tarski(X3,X3) != X1) )),
% 0.74/1.02    inference(equality_resolution,[],[f107])).
% 0.74/1.02  
% 0.74/1.02  fof(f124,plain,(
% 0.74/1.02    ( ! [X3] : (r2_hidden(X3,k2_tarski(X3,X3))) )),
% 0.74/1.02    inference(equality_resolution,[],[f123])).
% 0.74/1.02  
% 0.74/1.02  fof(f1,axiom,(
% 0.74/1.02    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.74/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.74/1.02  
% 0.74/1.02  fof(f25,plain,(
% 0.74/1.02    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.74/1.02    inference(ennf_transformation,[],[f1])).
% 0.74/1.02  
% 0.74/1.02  fof(f37,plain,(
% 0.74/1.02    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.74/1.02    inference(nnf_transformation,[],[f25])).
% 0.74/1.02  
% 0.74/1.02  fof(f38,plain,(
% 0.74/1.02    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.74/1.02    inference(rectify,[],[f37])).
% 0.74/1.02  
% 0.74/1.02  fof(f39,plain,(
% 0.74/1.02    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 0.74/1.02    introduced(choice_axiom,[])).
% 0.74/1.02  
% 0.74/1.02  fof(f40,plain,(
% 0.74/1.02    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.74/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f38,f39])).
% 0.74/1.02  
% 0.74/1.02  fof(f60,plain,(
% 0.74/1.02    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 0.74/1.02    inference(cnf_transformation,[],[f40])).
% 0.74/1.02  
% 0.74/1.02  fof(f23,conjecture,(
% 0.74/1.02    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0),
% 0.74/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.74/1.02  
% 0.74/1.02  fof(f24,negated_conjecture,(
% 0.74/1.02    ~! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0),
% 0.74/1.02    inference(negated_conjecture,[],[f23])).
% 0.74/1.02  
% 0.74/1.02  fof(f36,plain,(
% 0.74/1.02    ? [X0] : k3_tarski(k1_zfmisc_1(X0)) != X0),
% 0.74/1.02    inference(ennf_transformation,[],[f24])).
% 0.74/1.02  
% 0.74/1.02  fof(f58,plain,(
% 0.74/1.02    ? [X0] : k3_tarski(k1_zfmisc_1(X0)) != X0 => k3_tarski(k1_zfmisc_1(sK4)) != sK4),
% 0.74/1.02    introduced(choice_axiom,[])).
% 0.74/1.02  
% 0.74/1.02  fof(f59,plain,(
% 0.74/1.02    k3_tarski(k1_zfmisc_1(sK4)) != sK4),
% 0.74/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f36,f58])).
% 0.74/1.02  
% 0.74/1.02  fof(f101,plain,(
% 0.74/1.02    k3_tarski(k1_zfmisc_1(sK4)) != sK4),
% 0.74/1.02    inference(cnf_transformation,[],[f59])).
% 0.74/1.02  
% 0.74/1.02  cnf(c_35,plain,
% 0.74/1.02      ( ~ r2_hidden(X0,X1) | r1_tarski(X0,k3_tarski(X1)) ),
% 0.74/1.02      inference(cnf_transformation,[],[f98]) ).
% 0.74/1.02  
% 0.74/1.02  cnf(c_1538,plain,
% 0.74/1.02      ( r2_hidden(X0,X1) != iProver_top
% 0.74/1.02      | r1_tarski(X0,k3_tarski(X1)) = iProver_top ),
% 0.74/1.02      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 0.74/1.02  
% 0.74/1.02  cnf(c_37,plain,
% 0.74/1.02      ( r2_hidden(sK3(X0,X1),X0) | r1_tarski(k3_tarski(X0),X1) ),
% 0.74/1.02      inference(cnf_transformation,[],[f99]) ).
% 0.74/1.02  
% 0.74/1.02  cnf(c_1536,plain,
% 0.74/1.02      ( r2_hidden(sK3(X0,X1),X0) = iProver_top
% 0.74/1.02      | r1_tarski(k3_tarski(X0),X1) = iProver_top ),
% 0.74/1.02      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 0.74/1.02  
% 0.74/1.02  cnf(c_21,plain,
% 0.74/1.02      ( ~ r2_hidden(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 0.74/1.02      inference(cnf_transformation,[],[f127]) ).
% 0.74/1.02  
% 0.74/1.02  cnf(c_1550,plain,
% 0.74/1.02      ( r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top
% 0.74/1.02      | r1_tarski(X0,X1) = iProver_top ),
% 0.74/1.02      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 0.74/1.02  
% 0.74/1.02  cnf(c_2830,plain,
% 0.74/1.02      ( r1_tarski(sK3(k1_zfmisc_1(X0),X1),X0) = iProver_top
% 0.74/1.02      | r1_tarski(k3_tarski(k1_zfmisc_1(X0)),X1) = iProver_top ),
% 0.74/1.02      inference(superposition,[status(thm)],[c_1536,c_1550]) ).
% 0.74/1.02  
% 0.74/1.02  cnf(c_36,plain,
% 0.74/1.02      ( ~ r1_tarski(sK3(X0,X1),X1) | r1_tarski(k3_tarski(X0),X1) ),
% 0.74/1.02      inference(cnf_transformation,[],[f100]) ).
% 0.74/1.02  
% 0.74/1.02  cnf(c_1537,plain,
% 0.74/1.02      ( r1_tarski(sK3(X0,X1),X1) != iProver_top
% 0.74/1.02      | r1_tarski(k3_tarski(X0),X1) = iProver_top ),
% 0.74/1.02      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 0.74/1.02  
% 0.74/1.02  cnf(c_6149,plain,
% 0.74/1.02      ( r1_tarski(k3_tarski(k1_zfmisc_1(X0)),X0) = iProver_top ),
% 0.74/1.02      inference(superposition,[status(thm)],[c_2830,c_1537]) ).
% 0.74/1.02  
% 0.74/1.02  cnf(c_3,plain,
% 0.74/1.02      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 0.74/1.02      inference(cnf_transformation,[],[f66]) ).
% 0.74/1.02  
% 0.74/1.02  cnf(c_1565,plain,
% 0.74/1.02      ( X0 = X1
% 0.74/1.02      | r1_tarski(X1,X0) != iProver_top
% 0.74/1.02      | r1_tarski(X0,X1) != iProver_top ),
% 0.74/1.02      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 0.74/1.02  
% 0.74/1.02  cnf(c_6768,plain,
% 0.74/1.02      ( k3_tarski(k1_zfmisc_1(X0)) = X0
% 0.74/1.02      | r1_tarski(X0,k3_tarski(k1_zfmisc_1(X0))) != iProver_top ),
% 0.74/1.02      inference(superposition,[status(thm)],[c_6149,c_1565]) ).
% 0.74/1.02  
% 0.74/1.02  cnf(c_7152,plain,
% 0.74/1.02      ( k3_tarski(k1_zfmisc_1(X0)) = X0
% 0.74/1.02      | r2_hidden(X0,k1_zfmisc_1(X0)) != iProver_top ),
% 0.74/1.02      inference(superposition,[status(thm)],[c_1538,c_6768]) ).
% 0.74/1.02  
% 0.74/1.02  cnf(c_34,plain,
% 0.74/1.02      ( r1_tarski(k2_tarski(X0,X0),k1_zfmisc_1(X0)) ),
% 0.74/1.02      inference(cnf_transformation,[],[f119]) ).
% 0.74/1.02  
% 0.74/1.02  cnf(c_1539,plain,
% 0.74/1.02      ( r1_tarski(k2_tarski(X0,X0),k1_zfmisc_1(X0)) = iProver_top ),
% 0.74/1.02      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 0.74/1.02  
% 0.74/1.02  cnf(c_16,plain,
% 0.74/1.02      ( r2_hidden(X0,k2_tarski(X0,X0)) ),
% 0.74/1.02      inference(cnf_transformation,[],[f124]) ).
% 0.74/1.02  
% 0.74/1.02  cnf(c_1555,plain,
% 0.74/1.02      ( r2_hidden(X0,k2_tarski(X0,X0)) = iProver_top ),
% 0.74/1.02      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 0.74/1.02  
% 0.74/1.02  cnf(c_2,plain,
% 0.74/1.02      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 0.74/1.02      inference(cnf_transformation,[],[f60]) ).
% 0.74/1.02  
% 0.74/1.02  cnf(c_1566,plain,
% 0.74/1.02      ( r2_hidden(X0,X1) != iProver_top
% 0.74/1.02      | r2_hidden(X0,X2) = iProver_top
% 0.74/1.02      | r1_tarski(X1,X2) != iProver_top ),
% 0.74/1.02      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 0.74/1.02  
% 0.74/1.02  cnf(c_4571,plain,
% 0.74/1.02      ( r2_hidden(X0,X1) = iProver_top
% 0.74/1.02      | r1_tarski(k2_tarski(X0,X0),X1) != iProver_top ),
% 0.74/1.02      inference(superposition,[status(thm)],[c_1555,c_1566]) ).
% 0.74/1.02  
% 0.74/1.02  cnf(c_4631,plain,
% 0.74/1.02      ( r2_hidden(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 0.74/1.02      inference(superposition,[status(thm)],[c_1539,c_4571]) ).
% 0.74/1.02  
% 0.74/1.02  cnf(c_7166,plain,
% 0.74/1.02      ( k3_tarski(k1_zfmisc_1(X0)) = X0 ),
% 0.74/1.02      inference(global_propositional_subsumption,[status(thm)],[c_7152,c_4631]) ).
% 0.74/1.02  
% 0.74/1.02  cnf(c_38,negated_conjecture,
% 0.74/1.02      ( k3_tarski(k1_zfmisc_1(sK4)) != sK4 ),
% 0.74/1.02      inference(cnf_transformation,[],[f101]) ).
% 0.74/1.02  
% 0.74/1.02  cnf(c_7169,plain,
% 0.74/1.02      ( sK4 != sK4 ),
% 0.74/1.02      inference(demodulation,[status(thm)],[c_7166,c_38]) ).
% 0.74/1.02  
% 0.74/1.02  cnf(c_7180,plain,
% 0.74/1.02      ( $false ),
% 0.74/1.02      inference(equality_resolution_simp,[status(thm)],[c_7169]) ).
% 0.74/1.02  
% 0.74/1.02  
% 0.74/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 0.74/1.02  
% 0.74/1.02  ------                               Statistics
% 0.74/1.02  
% 0.74/1.02  ------ General
% 0.74/1.02  
% 0.74/1.02  abstr_ref_over_cycles:                  0
% 0.74/1.02  abstr_ref_under_cycles:                 0
% 0.74/1.02  gc_basic_clause_elim:                   0
% 0.74/1.02  forced_gc_time:                         0
% 0.74/1.02  parsing_time:                           0.011
% 0.74/1.02  unif_index_cands_time:                  0.
% 0.74/1.02  unif_index_add_time:                    0.
% 0.74/1.02  orderings_time:                         0.
% 0.74/1.02  out_proof_time:                         0.013
% 0.74/1.02  total_time:                             0.258
% 0.74/1.02  num_of_symbols:                         44
% 0.74/1.02  num_of_terms:                           7401
% 0.74/1.02  
% 0.74/1.02  ------ Preprocessing
% 0.74/1.02  
% 0.74/1.02  num_of_splits:                          0
% 0.74/1.02  num_of_split_atoms:                     0
% 0.74/1.02  num_of_reused_defs:                     0
% 0.74/1.02  num_eq_ax_congr_red:                    24
% 0.74/1.02  num_of_sem_filtered_clauses:            1
% 0.74/1.02  num_of_subtypes:                        0
% 0.74/1.02  monotx_restored_types:                  0
% 0.74/1.02  sat_num_of_epr_types:                   0
% 0.74/1.02  sat_num_of_non_cyclic_types:            0
% 0.74/1.02  sat_guarded_non_collapsed_types:        0
% 0.74/1.02  num_pure_diseq_elim:                    0
% 0.74/1.02  simp_replaced_by:                       0
% 0.74/1.02  res_preprocessed:                       171
% 0.74/1.02  prep_upred:                             0
% 0.74/1.02  prep_unflattend:                        20
% 0.74/1.02  smt_new_axioms:                         0
% 0.74/1.02  pred_elim_cands:                        3
% 0.74/1.02  pred_elim:                              0
% 0.74/1.02  pred_elim_cl:                           0
% 0.74/1.02  pred_elim_cycles:                       2
% 0.74/1.02  merged_defs:                            8
% 0.74/1.02  merged_defs_ncl:                        0
% 0.74/1.02  bin_hyper_res:                          8
% 0.74/1.02  prep_cycles:                            4
% 0.74/1.02  pred_elim_time:                         0.003
% 0.74/1.02  splitting_time:                         0.
% 0.74/1.02  sem_filter_time:                        0.
% 0.74/1.02  monotx_time:                            0.
% 0.74/1.02  subtype_inf_time:                       0.
% 0.74/1.02  
% 0.74/1.02  ------ Problem properties
% 0.74/1.02  
% 0.74/1.02  clauses:                                38
% 0.74/1.02  conjectures:                            1
% 0.74/1.02  epr:                                    7
% 0.74/1.02  horn:                                   29
% 0.74/1.02  ground:                                 2
% 0.74/1.02  unary:                                  16
% 0.74/1.02  binary:                                 12
% 0.74/1.02  lits:                                   73
% 0.74/1.02  lits_eq:                                23
% 0.74/1.02  fd_pure:                                0
% 0.74/1.02  fd_pseudo:                              0
% 0.74/1.02  fd_cond:                                3
% 0.74/1.02  fd_pseudo_cond:                         8
% 0.74/1.02  ac_symbols:                             0
% 0.74/1.02  
% 0.74/1.02  ------ Propositional Solver
% 0.74/1.02  
% 0.74/1.02  prop_solver_calls:                      26
% 0.74/1.02  prop_fast_solver_calls:                 848
% 0.74/1.02  smt_solver_calls:                       0
% 0.74/1.02  smt_fast_solver_calls:                  0
% 0.74/1.02  prop_num_of_clauses:                    2618
% 0.74/1.02  prop_preprocess_simplified:             8467
% 0.74/1.02  prop_fo_subsumed:                       1
% 0.74/1.02  prop_solver_time:                       0.
% 0.74/1.02  smt_solver_time:                        0.
% 0.74/1.02  smt_fast_solver_time:                   0.
% 0.74/1.02  prop_fast_solver_time:                  0.
% 0.74/1.02  prop_unsat_core_time:                   0.
% 0.74/1.02  
% 0.74/1.02  ------ QBF
% 0.74/1.02  
% 0.74/1.02  qbf_q_res:                              0
% 0.74/1.02  qbf_num_tautologies:                    0
% 0.74/1.02  qbf_prep_cycles:                        0
% 0.74/1.02  
% 0.74/1.02  ------ BMC1
% 0.74/1.02  
% 0.74/1.02  bmc1_current_bound:                     -1
% 0.74/1.02  bmc1_last_solved_bound:                 -1
% 0.74/1.02  bmc1_unsat_core_size:                   -1
% 0.74/1.02  bmc1_unsat_core_parents_size:           -1
% 0.74/1.02  bmc1_merge_next_fun:                    0
% 0.74/1.02  bmc1_unsat_core_clauses_time:           0.
% 0.74/1.02  
% 0.74/1.02  ------ Instantiation
% 0.74/1.02  
% 0.74/1.02  inst_num_of_clauses:                    666
% 0.74/1.02  inst_num_in_passive:                    100
% 0.74/1.02  inst_num_in_active:                     302
% 0.74/1.02  inst_num_in_unprocessed:                264
% 0.74/1.02  inst_num_of_loops:                      400
% 0.74/1.02  inst_num_of_learning_restarts:          0
% 0.74/1.02  inst_num_moves_active_passive:          97
% 0.74/1.02  inst_lit_activity:                      0
% 0.74/1.02  inst_lit_activity_moves:                0
% 0.74/1.02  inst_num_tautologies:                   0
% 0.74/1.02  inst_num_prop_implied:                  0
% 0.74/1.02  inst_num_existing_simplified:           0
% 0.74/1.02  inst_num_eq_res_simplified:             0
% 0.74/1.02  inst_num_child_elim:                    0
% 0.74/1.02  inst_num_of_dismatching_blockings:      289
% 0.74/1.02  inst_num_of_non_proper_insts:           643
% 0.74/1.02  inst_num_of_duplicates:                 0
% 0.74/1.02  inst_inst_num_from_inst_to_res:         0
% 0.74/1.02  inst_dismatching_checking_time:         0.
% 0.74/1.02  
% 0.74/1.02  ------ Resolution
% 0.74/1.02  
% 0.74/1.02  res_num_of_clauses:                     0
% 0.74/1.02  res_num_in_passive:                     0
% 0.74/1.02  res_num_in_active:                      0
% 0.74/1.02  res_num_of_loops:                       175
% 0.74/1.02  res_forward_subset_subsumed:            69
% 0.74/1.02  res_backward_subset_subsumed:           0
% 0.74/1.02  res_forward_subsumed:                   0
% 0.74/1.02  res_backward_subsumed:                  0
% 0.74/1.02  res_forward_subsumption_resolution:     0
% 0.74/1.02  res_backward_subsumption_resolution:    0
% 0.74/1.02  res_clause_to_clause_subsumption:       553
% 0.74/1.02  res_orphan_elimination:                 0
% 0.74/1.02  res_tautology_del:                      34
% 0.74/1.02  res_num_eq_res_simplified:              0
% 0.74/1.02  res_num_sel_changes:                    0
% 0.74/1.02  res_moves_from_active_to_pass:          0
% 0.74/1.02  
% 0.74/1.02  ------ Superposition
% 0.74/1.02  
% 0.74/1.02  sup_time_total:                         0.
% 0.74/1.02  sup_time_generating:                    0.
% 0.74/1.02  sup_time_sim_full:                      0.
% 0.74/1.02  sup_time_sim_immed:                     0.
% 0.74/1.02  
% 0.74/1.02  sup_num_of_clauses:                     157
% 0.74/1.02  sup_num_in_active:                      69
% 0.74/1.02  sup_num_in_passive:                     88
% 0.74/1.02  sup_num_of_loops:                       79
% 0.74/1.02  sup_fw_superposition:                   129
% 0.74/1.02  sup_bw_superposition:                   83
% 0.74/1.02  sup_immediate_simplified:               17
% 0.74/1.02  sup_given_eliminated:                   0
% 0.74/1.02  comparisons_done:                       0
% 0.74/1.02  comparisons_avoided:                    4
% 0.74/1.02  
% 0.74/1.02  ------ Simplifications
% 0.74/1.02  
% 0.74/1.02  
% 0.74/1.02  sim_fw_subset_subsumed:                 2
% 0.74/1.02  sim_bw_subset_subsumed:                 1
% 0.74/1.02  sim_fw_subsumed:                        12
% 0.74/1.02  sim_bw_subsumed:                        0
% 0.74/1.02  sim_fw_subsumption_res:                 0
% 0.74/1.02  sim_bw_subsumption_res:                 0
% 0.74/1.02  sim_tautology_del:                      4
% 0.74/1.02  sim_eq_tautology_del:                   25
% 0.74/1.02  sim_eq_res_simp:                        0
% 0.74/1.02  sim_fw_demodulated:                     0
% 0.74/1.02  sim_bw_demodulated:                     9
% 0.74/1.02  sim_light_normalised:                   9
% 0.74/1.02  sim_joinable_taut:                      0
% 0.74/1.02  sim_joinable_simp:                      0
% 0.74/1.02  sim_ac_normalised:                      0
% 0.74/1.02  sim_smt_subsumption:                    0
% 0.74/1.02  
%------------------------------------------------------------------------------
