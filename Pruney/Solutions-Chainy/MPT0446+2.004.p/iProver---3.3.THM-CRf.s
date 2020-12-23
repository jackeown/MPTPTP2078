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
% DateTime   : Thu Dec  3 11:43:08 EST 2020

% Result     : Theorem 1.23s
% Output     : CNFRefutation 1.23s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 110 expanded)
%              Number of clauses        :   26 (  37 expanded)
%              Number of leaves         :   14 (  25 expanded)
%              Depth                    :   11
%              Number of atoms          :  198 ( 352 expanded)
%              Number of equality atoms :   47 (  59 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k3_relat_1(X2))
          & r2_hidden(X0,k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r2_hidden(k4_tarski(X0,X1),X2)
         => ( r2_hidden(X1,k3_relat_1(X2))
            & r2_hidden(X0,k3_relat_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(X1,k3_relat_1(X2))
        | ~ r2_hidden(X0,k3_relat_1(X2)) )
      & r2_hidden(k4_tarski(X0,X1),X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(X1,k3_relat_1(X2))
        | ~ r2_hidden(X0,k3_relat_1(X2)) )
      & r2_hidden(k4_tarski(X0,X1),X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f12])).

fof(f26,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r2_hidden(X1,k3_relat_1(X2))
          | ~ r2_hidden(X0,k3_relat_1(X2)) )
        & r2_hidden(k4_tarski(X0,X1),X2)
        & v1_relat_1(X2) )
   => ( ( ~ r2_hidden(sK7,k3_relat_1(sK8))
        | ~ r2_hidden(sK6,k3_relat_1(sK8)) )
      & r2_hidden(k4_tarski(sK6,sK7),sK8)
      & v1_relat_1(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ( ~ r2_hidden(sK7,k3_relat_1(sK8))
      | ~ r2_hidden(sK6,k3_relat_1(sK8)) )
    & r2_hidden(k4_tarski(sK6,sK7),sK8)
    & v1_relat_1(sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f13,f26])).

fof(f41,plain,(
    r2_hidden(k4_tarski(sK6,sK7),sK8) ),
    inference(cnf_transformation,[],[f27])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
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
    inference(nnf_transformation,[],[f4])).

fof(f15,plain,(
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
    inference(rectify,[],[f14])).

fof(f18,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK2(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
     => r2_hidden(k4_tarski(X2,sK1(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK0(X0,X1),X3),X0)
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK0(X0,X1),X4),X0)
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK0(X0,X1),X3),X0)
            | ~ r2_hidden(sK0(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X0)
            | r2_hidden(sK0(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK2(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f18,f17,f16])).

fof(f32,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f43,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k1_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X6),X0) ) ),
    inference(equality_resolution,[],[f32])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f39,plain,(
    ! [X0] :
      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f40,plain,(
    v1_relat_1(sK8) ),
    inference(cnf_transformation,[],[f27])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f20])).

fof(f24,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK5(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
     => r2_hidden(k4_tarski(sK4(X0,X1),X2),X0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0)
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK3(X0,X1)),X0)
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0)
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0)
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK5(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f21,f24,f23,f22])).

fof(f36,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X6,X5),X0)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f45,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k2_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X6,X5),X0) ) ),
    inference(equality_resolution,[],[f36])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f42,plain,
    ( ~ r2_hidden(sK7,k3_relat_1(sK8))
    | ~ r2_hidden(sK6,k3_relat_1(sK8)) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_13,negated_conjecture,
    ( r2_hidden(k4_tarski(sK6,sK7),sK8) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_461,plain,
    ( r2_hidden(k4_tarski(sK6,sK7),sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_5,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_468,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1237,plain,
    ( r2_hidden(sK6,k1_relat_1(sK8)) = iProver_top ),
    inference(superposition,[status(thm)],[c_461,c_468])).

cnf(c_11,plain,
    ( ~ v1_relat_1(X0)
    | k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_14,negated_conjecture,
    ( v1_relat_1(sK8) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_163,plain,
    ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_14])).

cnf(c_164,plain,
    ( k2_xboole_0(k1_relat_1(sK8),k2_relat_1(sK8)) = k3_relat_1(sK8) ),
    inference(unflattening,[status(thm)],[c_163])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_2,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_169,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | X3 != X1
    | k2_xboole_0(X3,X4) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_2])).

cnf(c_170,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k2_xboole_0(X1,X2)) ),
    inference(unflattening,[status(thm)],[c_169])).

cnf(c_460,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k2_xboole_0(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_170])).

cnf(c_726,plain,
    ( r2_hidden(X0,k3_relat_1(sK8)) = iProver_top
    | r2_hidden(X0,k1_relat_1(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_164,c_460])).

cnf(c_1503,plain,
    ( r2_hidden(sK6,k3_relat_1(sK8)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1237,c_726])).

cnf(c_9,plain,
    ( r2_hidden(X0,k2_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_464,plain,
    ( r2_hidden(X0,k2_relat_1(X1)) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1107,plain,
    ( r2_hidden(sK7,k2_relat_1(sK8)) = iProver_top ),
    inference(superposition,[status(thm)],[c_461,c_464])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_724,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k2_xboole_0(X2,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_460])).

cnf(c_1012,plain,
    ( r2_hidden(X0,k3_relat_1(sK8)) = iProver_top
    | r2_hidden(X0,k2_relat_1(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_164,c_724])).

cnf(c_1432,plain,
    ( r2_hidden(sK7,k3_relat_1(sK8)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1107,c_1012])).

cnf(c_12,negated_conjecture,
    ( ~ r2_hidden(sK6,k3_relat_1(sK8))
    | ~ r2_hidden(sK7,k3_relat_1(sK8)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_17,plain,
    ( r2_hidden(sK6,k3_relat_1(sK8)) != iProver_top
    | r2_hidden(sK7,k3_relat_1(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1503,c_1432,c_17])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.09  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.10  % Command    : iproveropt_run.sh %d %s
% 0.11/0.31  % Computer   : n021.cluster.edu
% 0.11/0.31  % Model      : x86_64 x86_64
% 0.11/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.31  % Memory     : 8042.1875MB
% 0.11/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.31  % CPULimit   : 60
% 0.11/0.31  % WCLimit    : 600
% 0.11/0.31  % DateTime   : Tue Dec  1 12:25:04 EST 2020
% 0.11/0.31  % CPUTime    : 
% 0.11/0.31  % Running in FOF mode
% 1.23/0.91  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.23/0.91  
% 1.23/0.91  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.23/0.91  
% 1.23/0.91  ------  iProver source info
% 1.23/0.91  
% 1.23/0.91  git: date: 2020-06-30 10:37:57 +0100
% 1.23/0.91  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.23/0.91  git: non_committed_changes: false
% 1.23/0.91  git: last_make_outside_of_git: false
% 1.23/0.91  
% 1.23/0.91  ------ 
% 1.23/0.91  
% 1.23/0.91  ------ Input Options
% 1.23/0.91  
% 1.23/0.91  --out_options                           all
% 1.23/0.91  --tptp_safe_out                         true
% 1.23/0.91  --problem_path                          ""
% 1.23/0.91  --include_path                          ""
% 1.23/0.91  --clausifier                            res/vclausify_rel
% 1.23/0.91  --clausifier_options                    --mode clausify
% 1.23/0.91  --stdin                                 false
% 1.23/0.91  --stats_out                             all
% 1.23/0.91  
% 1.23/0.91  ------ General Options
% 1.23/0.91  
% 1.23/0.91  --fof                                   false
% 1.23/0.91  --time_out_real                         305.
% 1.23/0.91  --time_out_virtual                      -1.
% 1.23/0.91  --symbol_type_check                     false
% 1.23/0.91  --clausify_out                          false
% 1.23/0.91  --sig_cnt_out                           false
% 1.23/0.91  --trig_cnt_out                          false
% 1.23/0.91  --trig_cnt_out_tolerance                1.
% 1.23/0.91  --trig_cnt_out_sk_spl                   false
% 1.23/0.91  --abstr_cl_out                          false
% 1.23/0.91  
% 1.23/0.91  ------ Global Options
% 1.23/0.91  
% 1.23/0.91  --schedule                              default
% 1.23/0.91  --add_important_lit                     false
% 1.23/0.91  --prop_solver_per_cl                    1000
% 1.23/0.91  --min_unsat_core                        false
% 1.23/0.91  --soft_assumptions                      false
% 1.23/0.91  --soft_lemma_size                       3
% 1.23/0.91  --prop_impl_unit_size                   0
% 1.23/0.91  --prop_impl_unit                        []
% 1.23/0.91  --share_sel_clauses                     true
% 1.23/0.91  --reset_solvers                         false
% 1.23/0.91  --bc_imp_inh                            [conj_cone]
% 1.23/0.91  --conj_cone_tolerance                   3.
% 1.23/0.91  --extra_neg_conj                        none
% 1.23/0.91  --large_theory_mode                     true
% 1.23/0.91  --prolific_symb_bound                   200
% 1.23/0.91  --lt_threshold                          2000
% 1.23/0.91  --clause_weak_htbl                      true
% 1.23/0.91  --gc_record_bc_elim                     false
% 1.23/0.91  
% 1.23/0.91  ------ Preprocessing Options
% 1.23/0.91  
% 1.23/0.91  --preprocessing_flag                    true
% 1.23/0.91  --time_out_prep_mult                    0.1
% 1.23/0.91  --splitting_mode                        input
% 1.23/0.91  --splitting_grd                         true
% 1.23/0.91  --splitting_cvd                         false
% 1.23/0.91  --splitting_cvd_svl                     false
% 1.23/0.91  --splitting_nvd                         32
% 1.23/0.91  --sub_typing                            true
% 1.23/0.91  --prep_gs_sim                           true
% 1.23/0.91  --prep_unflatten                        true
% 1.23/0.91  --prep_res_sim                          true
% 1.23/0.91  --prep_upred                            true
% 1.23/0.91  --prep_sem_filter                       exhaustive
% 1.23/0.91  --prep_sem_filter_out                   false
% 1.23/0.91  --pred_elim                             true
% 1.23/0.91  --res_sim_input                         true
% 1.23/0.91  --eq_ax_congr_red                       true
% 1.23/0.91  --pure_diseq_elim                       true
% 1.23/0.91  --brand_transform                       false
% 1.23/0.91  --non_eq_to_eq                          false
% 1.23/0.91  --prep_def_merge                        true
% 1.23/0.91  --prep_def_merge_prop_impl              false
% 1.23/0.91  --prep_def_merge_mbd                    true
% 1.23/0.91  --prep_def_merge_tr_red                 false
% 1.23/0.91  --prep_def_merge_tr_cl                  false
% 1.23/0.91  --smt_preprocessing                     true
% 1.23/0.91  --smt_ac_axioms                         fast
% 1.23/0.91  --preprocessed_out                      false
% 1.23/0.91  --preprocessed_stats                    false
% 1.23/0.91  
% 1.23/0.91  ------ Abstraction refinement Options
% 1.23/0.91  
% 1.23/0.91  --abstr_ref                             []
% 1.23/0.91  --abstr_ref_prep                        false
% 1.23/0.91  --abstr_ref_until_sat                   false
% 1.23/0.91  --abstr_ref_sig_restrict                funpre
% 1.23/0.91  --abstr_ref_af_restrict_to_split_sk     false
% 1.23/0.91  --abstr_ref_under                       []
% 1.23/0.91  
% 1.23/0.91  ------ SAT Options
% 1.23/0.91  
% 1.23/0.91  --sat_mode                              false
% 1.23/0.91  --sat_fm_restart_options                ""
% 1.23/0.91  --sat_gr_def                            false
% 1.23/0.91  --sat_epr_types                         true
% 1.23/0.91  --sat_non_cyclic_types                  false
% 1.23/0.91  --sat_finite_models                     false
% 1.23/0.91  --sat_fm_lemmas                         false
% 1.23/0.91  --sat_fm_prep                           false
% 1.23/0.91  --sat_fm_uc_incr                        true
% 1.23/0.91  --sat_out_model                         small
% 1.23/0.91  --sat_out_clauses                       false
% 1.23/0.91  
% 1.23/0.91  ------ QBF Options
% 1.23/0.91  
% 1.23/0.91  --qbf_mode                              false
% 1.23/0.91  --qbf_elim_univ                         false
% 1.23/0.91  --qbf_dom_inst                          none
% 1.23/0.91  --qbf_dom_pre_inst                      false
% 1.23/0.91  --qbf_sk_in                             false
% 1.23/0.91  --qbf_pred_elim                         true
% 1.23/0.91  --qbf_split                             512
% 1.23/0.91  
% 1.23/0.91  ------ BMC1 Options
% 1.23/0.91  
% 1.23/0.91  --bmc1_incremental                      false
% 1.23/0.91  --bmc1_axioms                           reachable_all
% 1.23/0.91  --bmc1_min_bound                        0
% 1.23/0.91  --bmc1_max_bound                        -1
% 1.23/0.91  --bmc1_max_bound_default                -1
% 1.23/0.91  --bmc1_symbol_reachability              true
% 1.23/0.91  --bmc1_property_lemmas                  false
% 1.23/0.91  --bmc1_k_induction                      false
% 1.23/0.91  --bmc1_non_equiv_states                 false
% 1.23/0.91  --bmc1_deadlock                         false
% 1.23/0.91  --bmc1_ucm                              false
% 1.23/0.91  --bmc1_add_unsat_core                   none
% 1.23/0.91  --bmc1_unsat_core_children              false
% 1.23/0.91  --bmc1_unsat_core_extrapolate_axioms    false
% 1.23/0.91  --bmc1_out_stat                         full
% 1.23/0.91  --bmc1_ground_init                      false
% 1.23/0.91  --bmc1_pre_inst_next_state              false
% 1.23/0.91  --bmc1_pre_inst_state                   false
% 1.23/0.91  --bmc1_pre_inst_reach_state             false
% 1.23/0.91  --bmc1_out_unsat_core                   false
% 1.23/0.91  --bmc1_aig_witness_out                  false
% 1.23/0.91  --bmc1_verbose                          false
% 1.23/0.91  --bmc1_dump_clauses_tptp                false
% 1.23/0.91  --bmc1_dump_unsat_core_tptp             false
% 1.23/0.91  --bmc1_dump_file                        -
% 1.23/0.91  --bmc1_ucm_expand_uc_limit              128
% 1.23/0.91  --bmc1_ucm_n_expand_iterations          6
% 1.23/0.91  --bmc1_ucm_extend_mode                  1
% 1.23/0.91  --bmc1_ucm_init_mode                    2
% 1.23/0.91  --bmc1_ucm_cone_mode                    none
% 1.23/0.91  --bmc1_ucm_reduced_relation_type        0
% 1.23/0.91  --bmc1_ucm_relax_model                  4
% 1.23/0.91  --bmc1_ucm_full_tr_after_sat            true
% 1.23/0.91  --bmc1_ucm_expand_neg_assumptions       false
% 1.23/0.91  --bmc1_ucm_layered_model                none
% 1.23/0.91  --bmc1_ucm_max_lemma_size               10
% 1.23/0.91  
% 1.23/0.91  ------ AIG Options
% 1.23/0.91  
% 1.23/0.91  --aig_mode                              false
% 1.23/0.91  
% 1.23/0.91  ------ Instantiation Options
% 1.23/0.91  
% 1.23/0.91  --instantiation_flag                    true
% 1.23/0.91  --inst_sos_flag                         false
% 1.23/0.91  --inst_sos_phase                        true
% 1.23/0.91  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.23/0.91  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.23/0.91  --inst_lit_sel_side                     num_symb
% 1.23/0.91  --inst_solver_per_active                1400
% 1.23/0.91  --inst_solver_calls_frac                1.
% 1.23/0.91  --inst_passive_queue_type               priority_queues
% 1.23/0.91  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.23/0.91  --inst_passive_queues_freq              [25;2]
% 1.23/0.91  --inst_dismatching                      true
% 1.23/0.91  --inst_eager_unprocessed_to_passive     true
% 1.23/0.91  --inst_prop_sim_given                   true
% 1.23/0.91  --inst_prop_sim_new                     false
% 1.23/0.91  --inst_subs_new                         false
% 1.23/0.91  --inst_eq_res_simp                      false
% 1.23/0.91  --inst_subs_given                       false
% 1.23/0.91  --inst_orphan_elimination               true
% 1.23/0.91  --inst_learning_loop_flag               true
% 1.23/0.91  --inst_learning_start                   3000
% 1.23/0.91  --inst_learning_factor                  2
% 1.23/0.91  --inst_start_prop_sim_after_learn       3
% 1.23/0.91  --inst_sel_renew                        solver
% 1.23/0.91  --inst_lit_activity_flag                true
% 1.23/0.91  --inst_restr_to_given                   false
% 1.23/0.91  --inst_activity_threshold               500
% 1.23/0.91  --inst_out_proof                        true
% 1.23/0.91  
% 1.23/0.91  ------ Resolution Options
% 1.23/0.91  
% 1.23/0.91  --resolution_flag                       true
% 1.23/0.91  --res_lit_sel                           adaptive
% 1.23/0.91  --res_lit_sel_side                      none
% 1.23/0.91  --res_ordering                          kbo
% 1.23/0.91  --res_to_prop_solver                    active
% 1.23/0.91  --res_prop_simpl_new                    false
% 1.23/0.91  --res_prop_simpl_given                  true
% 1.23/0.91  --res_passive_queue_type                priority_queues
% 1.23/0.91  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.23/0.91  --res_passive_queues_freq               [15;5]
% 1.23/0.91  --res_forward_subs                      full
% 1.23/0.91  --res_backward_subs                     full
% 1.23/0.91  --res_forward_subs_resolution           true
% 1.23/0.91  --res_backward_subs_resolution          true
% 1.23/0.91  --res_orphan_elimination                true
% 1.23/0.91  --res_time_limit                        2.
% 1.23/0.91  --res_out_proof                         true
% 1.23/0.91  
% 1.23/0.91  ------ Superposition Options
% 1.23/0.91  
% 1.23/0.91  --superposition_flag                    true
% 1.23/0.91  --sup_passive_queue_type                priority_queues
% 1.23/0.91  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.23/0.91  --sup_passive_queues_freq               [8;1;4]
% 1.23/0.91  --demod_completeness_check              fast
% 1.23/0.91  --demod_use_ground                      true
% 1.23/0.91  --sup_to_prop_solver                    passive
% 1.23/0.91  --sup_prop_simpl_new                    true
% 1.23/0.91  --sup_prop_simpl_given                  true
% 1.23/0.91  --sup_fun_splitting                     false
% 1.23/0.91  --sup_smt_interval                      50000
% 1.23/0.91  
% 1.23/0.91  ------ Superposition Simplification Setup
% 1.23/0.91  
% 1.23/0.91  --sup_indices_passive                   []
% 1.23/0.91  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.23/0.91  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.23/0.91  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.23/0.91  --sup_full_triv                         [TrivRules;PropSubs]
% 1.23/0.91  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.23/0.91  --sup_full_bw                           [BwDemod]
% 1.23/0.91  --sup_immed_triv                        [TrivRules]
% 1.23/0.91  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.23/0.91  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.23/0.91  --sup_immed_bw_main                     []
% 1.23/0.91  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.23/0.91  --sup_input_triv                        [Unflattening;TrivRules]
% 1.23/0.91  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.23/0.91  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.23/0.91  
% 1.23/0.91  ------ Combination Options
% 1.23/0.91  
% 1.23/0.91  --comb_res_mult                         3
% 1.23/0.91  --comb_sup_mult                         2
% 1.23/0.91  --comb_inst_mult                        10
% 1.23/0.91  
% 1.23/0.91  ------ Debug Options
% 1.23/0.91  
% 1.23/0.91  --dbg_backtrace                         false
% 1.23/0.91  --dbg_dump_prop_clauses                 false
% 1.23/0.91  --dbg_dump_prop_clauses_file            -
% 1.23/0.91  --dbg_out_stat                          false
% 1.23/0.91  ------ Parsing...
% 1.23/0.91  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.23/0.91  
% 1.23/0.91  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 1.23/0.91  
% 1.23/0.91  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.23/0.91  
% 1.23/0.91  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.23/0.91  ------ Proving...
% 1.23/0.91  ------ Problem Properties 
% 1.23/0.91  
% 1.23/0.91  
% 1.23/0.91  clauses                                 13
% 1.23/0.91  conjectures                             2
% 1.23/0.91  EPR                                     0
% 1.23/0.91  Horn                                    11
% 1.23/0.91  unary                                   3
% 1.23/0.91  binary                                  6
% 1.23/0.91  lits                                    27
% 1.23/0.91  lits eq                                 6
% 1.23/0.91  fd_pure                                 0
% 1.23/0.91  fd_pseudo                               0
% 1.23/0.91  fd_cond                                 0
% 1.23/0.91  fd_pseudo_cond                          4
% 1.23/0.91  AC symbols                              0
% 1.23/0.91  
% 1.23/0.91  ------ Schedule dynamic 5 is on 
% 1.23/0.91  
% 1.23/0.91  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.23/0.91  
% 1.23/0.91  
% 1.23/0.91  ------ 
% 1.23/0.91  Current options:
% 1.23/0.91  ------ 
% 1.23/0.91  
% 1.23/0.91  ------ Input Options
% 1.23/0.91  
% 1.23/0.91  --out_options                           all
% 1.23/0.91  --tptp_safe_out                         true
% 1.23/0.91  --problem_path                          ""
% 1.23/0.91  --include_path                          ""
% 1.23/0.91  --clausifier                            res/vclausify_rel
% 1.23/0.91  --clausifier_options                    --mode clausify
% 1.23/0.91  --stdin                                 false
% 1.23/0.91  --stats_out                             all
% 1.23/0.91  
% 1.23/0.91  ------ General Options
% 1.23/0.91  
% 1.23/0.91  --fof                                   false
% 1.23/0.91  --time_out_real                         305.
% 1.23/0.91  --time_out_virtual                      -1.
% 1.23/0.91  --symbol_type_check                     false
% 1.23/0.91  --clausify_out                          false
% 1.23/0.91  --sig_cnt_out                           false
% 1.23/0.91  --trig_cnt_out                          false
% 1.23/0.91  --trig_cnt_out_tolerance                1.
% 1.23/0.91  --trig_cnt_out_sk_spl                   false
% 1.23/0.91  --abstr_cl_out                          false
% 1.23/0.91  
% 1.23/0.91  ------ Global Options
% 1.23/0.91  
% 1.23/0.91  --schedule                              default
% 1.23/0.91  --add_important_lit                     false
% 1.23/0.91  --prop_solver_per_cl                    1000
% 1.23/0.91  --min_unsat_core                        false
% 1.23/0.91  --soft_assumptions                      false
% 1.23/0.91  --soft_lemma_size                       3
% 1.23/0.91  --prop_impl_unit_size                   0
% 1.23/0.91  --prop_impl_unit                        []
% 1.23/0.91  --share_sel_clauses                     true
% 1.23/0.91  --reset_solvers                         false
% 1.23/0.91  --bc_imp_inh                            [conj_cone]
% 1.23/0.91  --conj_cone_tolerance                   3.
% 1.23/0.91  --extra_neg_conj                        none
% 1.23/0.91  --large_theory_mode                     true
% 1.23/0.91  --prolific_symb_bound                   200
% 1.23/0.91  --lt_threshold                          2000
% 1.23/0.91  --clause_weak_htbl                      true
% 1.23/0.91  --gc_record_bc_elim                     false
% 1.23/0.91  
% 1.23/0.91  ------ Preprocessing Options
% 1.23/0.91  
% 1.23/0.91  --preprocessing_flag                    true
% 1.23/0.91  --time_out_prep_mult                    0.1
% 1.23/0.91  --splitting_mode                        input
% 1.23/0.91  --splitting_grd                         true
% 1.23/0.91  --splitting_cvd                         false
% 1.23/0.91  --splitting_cvd_svl                     false
% 1.23/0.91  --splitting_nvd                         32
% 1.23/0.91  --sub_typing                            true
% 1.23/0.91  --prep_gs_sim                           true
% 1.23/0.91  --prep_unflatten                        true
% 1.23/0.91  --prep_res_sim                          true
% 1.23/0.91  --prep_upred                            true
% 1.23/0.91  --prep_sem_filter                       exhaustive
% 1.23/0.91  --prep_sem_filter_out                   false
% 1.23/0.91  --pred_elim                             true
% 1.23/0.91  --res_sim_input                         true
% 1.23/0.92  --eq_ax_congr_red                       true
% 1.23/0.92  --pure_diseq_elim                       true
% 1.23/0.92  --brand_transform                       false
% 1.23/0.92  --non_eq_to_eq                          false
% 1.23/0.92  --prep_def_merge                        true
% 1.23/0.92  --prep_def_merge_prop_impl              false
% 1.23/0.92  --prep_def_merge_mbd                    true
% 1.23/0.92  --prep_def_merge_tr_red                 false
% 1.23/0.92  --prep_def_merge_tr_cl                  false
% 1.23/0.92  --smt_preprocessing                     true
% 1.23/0.92  --smt_ac_axioms                         fast
% 1.23/0.92  --preprocessed_out                      false
% 1.23/0.92  --preprocessed_stats                    false
% 1.23/0.92  
% 1.23/0.92  ------ Abstraction refinement Options
% 1.23/0.92  
% 1.23/0.92  --abstr_ref                             []
% 1.23/0.92  --abstr_ref_prep                        false
% 1.23/0.92  --abstr_ref_until_sat                   false
% 1.23/0.92  --abstr_ref_sig_restrict                funpre
% 1.23/0.92  --abstr_ref_af_restrict_to_split_sk     false
% 1.23/0.92  --abstr_ref_under                       []
% 1.23/0.92  
% 1.23/0.92  ------ SAT Options
% 1.23/0.92  
% 1.23/0.92  --sat_mode                              false
% 1.23/0.92  --sat_fm_restart_options                ""
% 1.23/0.92  --sat_gr_def                            false
% 1.23/0.92  --sat_epr_types                         true
% 1.23/0.92  --sat_non_cyclic_types                  false
% 1.23/0.92  --sat_finite_models                     false
% 1.23/0.92  --sat_fm_lemmas                         false
% 1.23/0.92  --sat_fm_prep                           false
% 1.23/0.92  --sat_fm_uc_incr                        true
% 1.23/0.92  --sat_out_model                         small
% 1.23/0.92  --sat_out_clauses                       false
% 1.23/0.92  
% 1.23/0.92  ------ QBF Options
% 1.23/0.92  
% 1.23/0.92  --qbf_mode                              false
% 1.23/0.92  --qbf_elim_univ                         false
% 1.23/0.92  --qbf_dom_inst                          none
% 1.23/0.92  --qbf_dom_pre_inst                      false
% 1.23/0.92  --qbf_sk_in                             false
% 1.23/0.92  --qbf_pred_elim                         true
% 1.23/0.92  --qbf_split                             512
% 1.23/0.92  
% 1.23/0.92  ------ BMC1 Options
% 1.23/0.92  
% 1.23/0.92  --bmc1_incremental                      false
% 1.23/0.92  --bmc1_axioms                           reachable_all
% 1.23/0.92  --bmc1_min_bound                        0
% 1.23/0.92  --bmc1_max_bound                        -1
% 1.23/0.92  --bmc1_max_bound_default                -1
% 1.23/0.92  --bmc1_symbol_reachability              true
% 1.23/0.92  --bmc1_property_lemmas                  false
% 1.23/0.92  --bmc1_k_induction                      false
% 1.23/0.92  --bmc1_non_equiv_states                 false
% 1.23/0.92  --bmc1_deadlock                         false
% 1.23/0.92  --bmc1_ucm                              false
% 1.23/0.92  --bmc1_add_unsat_core                   none
% 1.23/0.92  --bmc1_unsat_core_children              false
% 1.23/0.92  --bmc1_unsat_core_extrapolate_axioms    false
% 1.23/0.92  --bmc1_out_stat                         full
% 1.23/0.92  --bmc1_ground_init                      false
% 1.23/0.92  --bmc1_pre_inst_next_state              false
% 1.23/0.92  --bmc1_pre_inst_state                   false
% 1.23/0.92  --bmc1_pre_inst_reach_state             false
% 1.23/0.92  --bmc1_out_unsat_core                   false
% 1.23/0.92  --bmc1_aig_witness_out                  false
% 1.23/0.92  --bmc1_verbose                          false
% 1.23/0.92  --bmc1_dump_clauses_tptp                false
% 1.23/0.92  --bmc1_dump_unsat_core_tptp             false
% 1.23/0.92  --bmc1_dump_file                        -
% 1.23/0.92  --bmc1_ucm_expand_uc_limit              128
% 1.23/0.92  --bmc1_ucm_n_expand_iterations          6
% 1.23/0.92  --bmc1_ucm_extend_mode                  1
% 1.23/0.92  --bmc1_ucm_init_mode                    2
% 1.23/0.92  --bmc1_ucm_cone_mode                    none
% 1.23/0.92  --bmc1_ucm_reduced_relation_type        0
% 1.23/0.92  --bmc1_ucm_relax_model                  4
% 1.23/0.92  --bmc1_ucm_full_tr_after_sat            true
% 1.23/0.92  --bmc1_ucm_expand_neg_assumptions       false
% 1.23/0.92  --bmc1_ucm_layered_model                none
% 1.23/0.92  --bmc1_ucm_max_lemma_size               10
% 1.23/0.92  
% 1.23/0.92  ------ AIG Options
% 1.23/0.92  
% 1.23/0.92  --aig_mode                              false
% 1.23/0.92  
% 1.23/0.92  ------ Instantiation Options
% 1.23/0.92  
% 1.23/0.92  --instantiation_flag                    true
% 1.23/0.92  --inst_sos_flag                         false
% 1.23/0.92  --inst_sos_phase                        true
% 1.23/0.92  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.23/0.92  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.23/0.92  --inst_lit_sel_side                     none
% 1.23/0.92  --inst_solver_per_active                1400
% 1.23/0.92  --inst_solver_calls_frac                1.
% 1.23/0.92  --inst_passive_queue_type               priority_queues
% 1.23/0.92  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.23/0.92  --inst_passive_queues_freq              [25;2]
% 1.23/0.92  --inst_dismatching                      true
% 1.23/0.92  --inst_eager_unprocessed_to_passive     true
% 1.23/0.92  --inst_prop_sim_given                   true
% 1.23/0.92  --inst_prop_sim_new                     false
% 1.23/0.92  --inst_subs_new                         false
% 1.23/0.92  --inst_eq_res_simp                      false
% 1.23/0.92  --inst_subs_given                       false
% 1.23/0.92  --inst_orphan_elimination               true
% 1.23/0.92  --inst_learning_loop_flag               true
% 1.23/0.92  --inst_learning_start                   3000
% 1.23/0.92  --inst_learning_factor                  2
% 1.23/0.92  --inst_start_prop_sim_after_learn       3
% 1.23/0.92  --inst_sel_renew                        solver
% 1.23/0.92  --inst_lit_activity_flag                true
% 1.23/0.92  --inst_restr_to_given                   false
% 1.23/0.92  --inst_activity_threshold               500
% 1.23/0.92  --inst_out_proof                        true
% 1.23/0.92  
% 1.23/0.92  ------ Resolution Options
% 1.23/0.92  
% 1.23/0.92  --resolution_flag                       false
% 1.23/0.92  --res_lit_sel                           adaptive
% 1.23/0.92  --res_lit_sel_side                      none
% 1.23/0.92  --res_ordering                          kbo
% 1.23/0.92  --res_to_prop_solver                    active
% 1.23/0.92  --res_prop_simpl_new                    false
% 1.23/0.92  --res_prop_simpl_given                  true
% 1.23/0.92  --res_passive_queue_type                priority_queues
% 1.23/0.92  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.23/0.92  --res_passive_queues_freq               [15;5]
% 1.23/0.92  --res_forward_subs                      full
% 1.23/0.92  --res_backward_subs                     full
% 1.23/0.92  --res_forward_subs_resolution           true
% 1.23/0.92  --res_backward_subs_resolution          true
% 1.23/0.92  --res_orphan_elimination                true
% 1.23/0.92  --res_time_limit                        2.
% 1.23/0.92  --res_out_proof                         true
% 1.23/0.92  
% 1.23/0.92  ------ Superposition Options
% 1.23/0.92  
% 1.23/0.92  --superposition_flag                    true
% 1.23/0.92  --sup_passive_queue_type                priority_queues
% 1.23/0.92  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.23/0.92  --sup_passive_queues_freq               [8;1;4]
% 1.23/0.92  --demod_completeness_check              fast
% 1.23/0.92  --demod_use_ground                      true
% 1.23/0.92  --sup_to_prop_solver                    passive
% 1.23/0.92  --sup_prop_simpl_new                    true
% 1.23/0.92  --sup_prop_simpl_given                  true
% 1.23/0.92  --sup_fun_splitting                     false
% 1.23/0.92  --sup_smt_interval                      50000
% 1.23/0.92  
% 1.23/0.92  ------ Superposition Simplification Setup
% 1.23/0.92  
% 1.23/0.92  --sup_indices_passive                   []
% 1.23/0.92  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.23/0.92  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.23/0.92  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.23/0.92  --sup_full_triv                         [TrivRules;PropSubs]
% 1.23/0.92  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.23/0.92  --sup_full_bw                           [BwDemod]
% 1.23/0.92  --sup_immed_triv                        [TrivRules]
% 1.23/0.92  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.23/0.92  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.23/0.92  --sup_immed_bw_main                     []
% 1.23/0.92  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.23/0.92  --sup_input_triv                        [Unflattening;TrivRules]
% 1.23/0.92  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.23/0.92  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.23/0.92  
% 1.23/0.92  ------ Combination Options
% 1.23/0.92  
% 1.23/0.92  --comb_res_mult                         3
% 1.23/0.92  --comb_sup_mult                         2
% 1.23/0.92  --comb_inst_mult                        10
% 1.23/0.92  
% 1.23/0.92  ------ Debug Options
% 1.23/0.92  
% 1.23/0.92  --dbg_backtrace                         false
% 1.23/0.92  --dbg_dump_prop_clauses                 false
% 1.23/0.92  --dbg_dump_prop_clauses_file            -
% 1.23/0.92  --dbg_out_stat                          false
% 1.23/0.92  
% 1.23/0.92  
% 1.23/0.92  
% 1.23/0.92  
% 1.23/0.92  ------ Proving...
% 1.23/0.92  
% 1.23/0.92  
% 1.23/0.92  % SZS status Theorem for theBenchmark.p
% 1.23/0.92  
% 1.23/0.92  % SZS output start CNFRefutation for theBenchmark.p
% 1.23/0.92  
% 1.23/0.92  fof(f7,conjecture,(
% 1.23/0.92    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)))))),
% 1.23/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.23/0.92  
% 1.23/0.92  fof(f8,negated_conjecture,(
% 1.23/0.92    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)))))),
% 1.23/0.92    inference(negated_conjecture,[],[f7])).
% 1.23/0.92  
% 1.23/0.92  fof(f12,plain,(
% 1.23/0.92    ? [X0,X1,X2] : (((~r2_hidden(X1,k3_relat_1(X2)) | ~r2_hidden(X0,k3_relat_1(X2))) & r2_hidden(k4_tarski(X0,X1),X2)) & v1_relat_1(X2))),
% 1.23/0.92    inference(ennf_transformation,[],[f8])).
% 1.23/0.92  
% 1.23/0.92  fof(f13,plain,(
% 1.23/0.92    ? [X0,X1,X2] : ((~r2_hidden(X1,k3_relat_1(X2)) | ~r2_hidden(X0,k3_relat_1(X2))) & r2_hidden(k4_tarski(X0,X1),X2) & v1_relat_1(X2))),
% 1.23/0.92    inference(flattening,[],[f12])).
% 1.23/0.92  
% 1.23/0.92  fof(f26,plain,(
% 1.23/0.92    ? [X0,X1,X2] : ((~r2_hidden(X1,k3_relat_1(X2)) | ~r2_hidden(X0,k3_relat_1(X2))) & r2_hidden(k4_tarski(X0,X1),X2) & v1_relat_1(X2)) => ((~r2_hidden(sK7,k3_relat_1(sK8)) | ~r2_hidden(sK6,k3_relat_1(sK8))) & r2_hidden(k4_tarski(sK6,sK7),sK8) & v1_relat_1(sK8))),
% 1.23/0.92    introduced(choice_axiom,[])).
% 1.23/0.92  
% 1.23/0.92  fof(f27,plain,(
% 1.23/0.92    (~r2_hidden(sK7,k3_relat_1(sK8)) | ~r2_hidden(sK6,k3_relat_1(sK8))) & r2_hidden(k4_tarski(sK6,sK7),sK8) & v1_relat_1(sK8)),
% 1.23/0.92    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f13,f26])).
% 1.23/0.92  
% 1.23/0.92  fof(f41,plain,(
% 1.23/0.92    r2_hidden(k4_tarski(sK6,sK7),sK8)),
% 1.23/0.92    inference(cnf_transformation,[],[f27])).
% 1.23/0.92  
% 1.23/0.92  fof(f4,axiom,(
% 1.23/0.92    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 1.23/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.23/0.92  
% 1.23/0.92  fof(f14,plain,(
% 1.23/0.92    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 1.23/0.92    inference(nnf_transformation,[],[f4])).
% 1.23/0.92  
% 1.23/0.92  fof(f15,plain,(
% 1.23/0.92    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 1.23/0.92    inference(rectify,[],[f14])).
% 1.23/0.92  
% 1.23/0.92  fof(f18,plain,(
% 1.23/0.92    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK2(X0,X5)),X0))),
% 1.23/0.92    introduced(choice_axiom,[])).
% 1.23/0.92  
% 1.23/0.92  fof(f17,plain,(
% 1.23/0.92    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) => r2_hidden(k4_tarski(X2,sK1(X0,X1)),X0))) )),
% 1.23/0.92    introduced(choice_axiom,[])).
% 1.23/0.92  
% 1.23/0.92  fof(f16,plain,(
% 1.23/0.92    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK0(X0,X1),X3),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK0(X0,X1),X4),X0) | r2_hidden(sK0(X0,X1),X1))))),
% 1.23/0.92    introduced(choice_axiom,[])).
% 1.23/0.92  
% 1.23/0.92  fof(f19,plain,(
% 1.23/0.92    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK0(X0,X1),X3),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X0) | r2_hidden(sK0(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK2(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 1.23/0.92    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f18,f17,f16])).
% 1.23/0.92  
% 1.23/0.92  fof(f32,plain,(
% 1.23/0.92    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X6),X0) | k1_relat_1(X0) != X1) )),
% 1.23/0.92    inference(cnf_transformation,[],[f19])).
% 1.23/0.92  
% 1.23/0.92  fof(f43,plain,(
% 1.23/0.92    ( ! [X6,X0,X5] : (r2_hidden(X5,k1_relat_1(X0)) | ~r2_hidden(k4_tarski(X5,X6),X0)) )),
% 1.23/0.92    inference(equality_resolution,[],[f32])).
% 1.23/0.92  
% 1.23/0.92  fof(f6,axiom,(
% 1.23/0.92    ! [X0] : (v1_relat_1(X0) => k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0))),
% 1.23/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.23/0.92  
% 1.23/0.92  fof(f11,plain,(
% 1.23/0.92    ! [X0] : (k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) | ~v1_relat_1(X0))),
% 1.23/0.92    inference(ennf_transformation,[],[f6])).
% 1.23/0.92  
% 1.23/0.92  fof(f39,plain,(
% 1.23/0.92    ( ! [X0] : (k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) | ~v1_relat_1(X0)) )),
% 1.23/0.92    inference(cnf_transformation,[],[f11])).
% 1.23/0.92  
% 1.23/0.92  fof(f40,plain,(
% 1.23/0.92    v1_relat_1(sK8)),
% 1.23/0.92    inference(cnf_transformation,[],[f27])).
% 1.23/0.92  
% 1.23/0.92  fof(f2,axiom,(
% 1.23/0.92    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.23/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.23/0.92  
% 1.23/0.92  fof(f9,plain,(
% 1.23/0.92    ! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.23/0.92    inference(unused_predicate_definition_removal,[],[f2])).
% 1.23/0.92  
% 1.23/0.92  fof(f10,plain,(
% 1.23/0.92    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1))),
% 1.23/0.92    inference(ennf_transformation,[],[f9])).
% 1.23/0.92  
% 1.23/0.92  fof(f29,plain,(
% 1.23/0.92    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(X0,X1)) )),
% 1.23/0.92    inference(cnf_transformation,[],[f10])).
% 1.23/0.92  
% 1.23/0.92  fof(f3,axiom,(
% 1.23/0.92    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.23/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.23/0.92  
% 1.23/0.92  fof(f30,plain,(
% 1.23/0.92    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.23/0.92    inference(cnf_transformation,[],[f3])).
% 1.23/0.92  
% 1.23/0.92  fof(f5,axiom,(
% 1.23/0.92    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 1.23/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.23/0.92  
% 1.23/0.92  fof(f20,plain,(
% 1.23/0.92    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 1.23/0.92    inference(nnf_transformation,[],[f5])).
% 1.23/0.92  
% 1.23/0.92  fof(f21,plain,(
% 1.23/0.92    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 1.23/0.92    inference(rectify,[],[f20])).
% 1.23/0.92  
% 1.23/0.92  fof(f24,plain,(
% 1.23/0.92    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK5(X0,X5),X5),X0))),
% 1.23/0.92    introduced(choice_axiom,[])).
% 1.23/0.92  
% 1.23/0.92  fof(f23,plain,(
% 1.23/0.92    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) => r2_hidden(k4_tarski(sK4(X0,X1),X2),X0))) )),
% 1.23/0.92    introduced(choice_axiom,[])).
% 1.23/0.92  
% 1.23/0.92  fof(f22,plain,(
% 1.23/0.92    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK3(X0,X1)),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 1.23/0.92    introduced(choice_axiom,[])).
% 1.23/0.92  
% 1.23/0.92  fof(f25,plain,(
% 1.23/0.92    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK5(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 1.23/0.92    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f21,f24,f23,f22])).
% 1.23/0.92  
% 1.23/0.92  fof(f36,plain,(
% 1.23/0.92    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X6,X5),X0) | k2_relat_1(X0) != X1) )),
% 1.23/0.92    inference(cnf_transformation,[],[f25])).
% 1.23/0.92  
% 1.23/0.92  fof(f45,plain,(
% 1.23/0.92    ( ! [X6,X0,X5] : (r2_hidden(X5,k2_relat_1(X0)) | ~r2_hidden(k4_tarski(X6,X5),X0)) )),
% 1.23/0.92    inference(equality_resolution,[],[f36])).
% 1.23/0.92  
% 1.23/0.92  fof(f1,axiom,(
% 1.23/0.92    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.23/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.23/0.92  
% 1.23/0.92  fof(f28,plain,(
% 1.23/0.92    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.23/0.92    inference(cnf_transformation,[],[f1])).
% 1.23/0.92  
% 1.23/0.92  fof(f42,plain,(
% 1.23/0.92    ~r2_hidden(sK7,k3_relat_1(sK8)) | ~r2_hidden(sK6,k3_relat_1(sK8))),
% 1.23/0.92    inference(cnf_transformation,[],[f27])).
% 1.23/0.92  
% 1.23/0.92  cnf(c_13,negated_conjecture,
% 1.23/0.92      ( r2_hidden(k4_tarski(sK6,sK7),sK8) ),
% 1.23/0.92      inference(cnf_transformation,[],[f41]) ).
% 1.23/0.92  
% 1.23/0.92  cnf(c_461,plain,
% 1.23/0.92      ( r2_hidden(k4_tarski(sK6,sK7),sK8) = iProver_top ),
% 1.23/0.92      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 1.23/0.92  
% 1.23/0.92  cnf(c_5,plain,
% 1.23/0.92      ( r2_hidden(X0,k1_relat_1(X1)) | ~ r2_hidden(k4_tarski(X0,X2),X1) ),
% 1.23/0.92      inference(cnf_transformation,[],[f43]) ).
% 1.23/0.92  
% 1.23/0.92  cnf(c_468,plain,
% 1.23/0.92      ( r2_hidden(X0,k1_relat_1(X1)) = iProver_top
% 1.23/0.92      | r2_hidden(k4_tarski(X0,X2),X1) != iProver_top ),
% 1.23/0.92      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 1.23/0.92  
% 1.23/0.92  cnf(c_1237,plain,
% 1.23/0.92      ( r2_hidden(sK6,k1_relat_1(sK8)) = iProver_top ),
% 1.23/0.92      inference(superposition,[status(thm)],[c_461,c_468]) ).
% 1.23/0.92  
% 1.23/0.92  cnf(c_11,plain,
% 1.23/0.92      ( ~ v1_relat_1(X0)
% 1.23/0.92      | k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) ),
% 1.23/0.92      inference(cnf_transformation,[],[f39]) ).
% 1.23/0.92  
% 1.23/0.92  cnf(c_14,negated_conjecture,
% 1.23/0.92      ( v1_relat_1(sK8) ),
% 1.23/0.92      inference(cnf_transformation,[],[f40]) ).
% 1.23/0.92  
% 1.23/0.92  cnf(c_163,plain,
% 1.23/0.92      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
% 1.23/0.92      | sK8 != X0 ),
% 1.23/0.92      inference(resolution_lifted,[status(thm)],[c_11,c_14]) ).
% 1.23/0.92  
% 1.23/0.92  cnf(c_164,plain,
% 1.23/0.92      ( k2_xboole_0(k1_relat_1(sK8),k2_relat_1(sK8)) = k3_relat_1(sK8) ),
% 1.23/0.92      inference(unflattening,[status(thm)],[c_163]) ).
% 1.23/0.92  
% 1.23/0.92  cnf(c_1,plain,
% 1.23/0.92      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 1.23/0.92      inference(cnf_transformation,[],[f29]) ).
% 1.23/0.92  
% 1.23/0.92  cnf(c_2,plain,
% 1.23/0.92      ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
% 1.23/0.92      inference(cnf_transformation,[],[f30]) ).
% 1.23/0.92  
% 1.23/0.92  cnf(c_169,plain,
% 1.23/0.92      ( ~ r2_hidden(X0,X1)
% 1.23/0.92      | r2_hidden(X0,X2)
% 1.23/0.92      | X3 != X1
% 1.23/0.92      | k2_xboole_0(X3,X4) != X2 ),
% 1.23/0.92      inference(resolution_lifted,[status(thm)],[c_1,c_2]) ).
% 1.23/0.92  
% 1.23/0.92  cnf(c_170,plain,
% 1.23/0.92      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,k2_xboole_0(X1,X2)) ),
% 1.23/0.92      inference(unflattening,[status(thm)],[c_169]) ).
% 1.23/0.92  
% 1.23/0.92  cnf(c_460,plain,
% 1.23/0.92      ( r2_hidden(X0,X1) != iProver_top
% 1.23/0.92      | r2_hidden(X0,k2_xboole_0(X1,X2)) = iProver_top ),
% 1.23/0.92      inference(predicate_to_equality,[status(thm)],[c_170]) ).
% 1.23/0.92  
% 1.23/0.92  cnf(c_726,plain,
% 1.23/0.92      ( r2_hidden(X0,k3_relat_1(sK8)) = iProver_top
% 1.23/0.92      | r2_hidden(X0,k1_relat_1(sK8)) != iProver_top ),
% 1.23/0.92      inference(superposition,[status(thm)],[c_164,c_460]) ).
% 1.23/0.92  
% 1.23/0.92  cnf(c_1503,plain,
% 1.23/0.92      ( r2_hidden(sK6,k3_relat_1(sK8)) = iProver_top ),
% 1.23/0.92      inference(superposition,[status(thm)],[c_1237,c_726]) ).
% 1.23/0.92  
% 1.23/0.92  cnf(c_9,plain,
% 1.23/0.92      ( r2_hidden(X0,k2_relat_1(X1)) | ~ r2_hidden(k4_tarski(X2,X0),X1) ),
% 1.23/0.92      inference(cnf_transformation,[],[f45]) ).
% 1.23/0.92  
% 1.23/0.92  cnf(c_464,plain,
% 1.23/0.92      ( r2_hidden(X0,k2_relat_1(X1)) = iProver_top
% 1.23/0.92      | r2_hidden(k4_tarski(X2,X0),X1) != iProver_top ),
% 1.23/0.92      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 1.23/0.92  
% 1.23/0.92  cnf(c_1107,plain,
% 1.23/0.92      ( r2_hidden(sK7,k2_relat_1(sK8)) = iProver_top ),
% 1.23/0.92      inference(superposition,[status(thm)],[c_461,c_464]) ).
% 1.23/0.92  
% 1.23/0.92  cnf(c_0,plain,
% 1.23/0.92      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 1.23/0.92      inference(cnf_transformation,[],[f28]) ).
% 1.23/0.92  
% 1.23/0.92  cnf(c_724,plain,
% 1.23/0.92      ( r2_hidden(X0,X1) != iProver_top
% 1.23/0.92      | r2_hidden(X0,k2_xboole_0(X2,X1)) = iProver_top ),
% 1.23/0.92      inference(superposition,[status(thm)],[c_0,c_460]) ).
% 1.23/0.92  
% 1.23/0.92  cnf(c_1012,plain,
% 1.23/0.92      ( r2_hidden(X0,k3_relat_1(sK8)) = iProver_top
% 1.23/0.92      | r2_hidden(X0,k2_relat_1(sK8)) != iProver_top ),
% 1.23/0.92      inference(superposition,[status(thm)],[c_164,c_724]) ).
% 1.23/0.92  
% 1.23/0.92  cnf(c_1432,plain,
% 1.23/0.92      ( r2_hidden(sK7,k3_relat_1(sK8)) = iProver_top ),
% 1.23/0.92      inference(superposition,[status(thm)],[c_1107,c_1012]) ).
% 1.23/0.92  
% 1.23/0.92  cnf(c_12,negated_conjecture,
% 1.23/0.92      ( ~ r2_hidden(sK6,k3_relat_1(sK8))
% 1.23/0.92      | ~ r2_hidden(sK7,k3_relat_1(sK8)) ),
% 1.23/0.92      inference(cnf_transformation,[],[f42]) ).
% 1.23/0.92  
% 1.23/0.92  cnf(c_17,plain,
% 1.23/0.92      ( r2_hidden(sK6,k3_relat_1(sK8)) != iProver_top
% 1.23/0.92      | r2_hidden(sK7,k3_relat_1(sK8)) != iProver_top ),
% 1.23/0.92      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 1.23/0.92  
% 1.23/0.92  cnf(contradiction,plain,
% 1.23/0.92      ( $false ),
% 1.23/0.92      inference(minisat,[status(thm)],[c_1503,c_1432,c_17]) ).
% 1.23/0.92  
% 1.23/0.92  
% 1.23/0.92  % SZS output end CNFRefutation for theBenchmark.p
% 1.23/0.92  
% 1.23/0.92  ------                               Statistics
% 1.23/0.92  
% 1.23/0.92  ------ General
% 1.23/0.92  
% 1.23/0.92  abstr_ref_over_cycles:                  0
% 1.23/0.92  abstr_ref_under_cycles:                 0
% 1.23/0.92  gc_basic_clause_elim:                   0
% 1.23/0.92  forced_gc_time:                         0
% 1.23/0.92  parsing_time:                           0.006
% 1.23/0.92  unif_index_cands_time:                  0.
% 1.23/0.92  unif_index_add_time:                    0.
% 1.23/0.92  orderings_time:                         0.
% 1.23/0.92  out_proof_time:                         0.008
% 1.23/0.92  total_time:                             0.062
% 1.23/0.92  num_of_symbols:                         48
% 1.23/0.92  num_of_terms:                           2061
% 1.23/0.92  
% 1.23/0.92  ------ Preprocessing
% 1.23/0.92  
% 1.23/0.92  num_of_splits:                          0
% 1.23/0.92  num_of_split_atoms:                     0
% 1.23/0.92  num_of_reused_defs:                     0
% 1.23/0.92  num_eq_ax_congr_red:                    39
% 1.23/0.92  num_of_sem_filtered_clauses:            1
% 1.23/0.92  num_of_subtypes:                        0
% 1.23/0.92  monotx_restored_types:                  0
% 1.23/0.92  sat_num_of_epr_types:                   0
% 1.23/0.92  sat_num_of_non_cyclic_types:            0
% 1.23/0.92  sat_guarded_non_collapsed_types:        0
% 1.23/0.92  num_pure_diseq_elim:                    0
% 1.23/0.92  simp_replaced_by:                       0
% 1.23/0.92  res_preprocessed:                       71
% 1.23/0.92  prep_upred:                             0
% 1.23/0.92  prep_unflattend:                        3
% 1.23/0.92  smt_new_axioms:                         0
% 1.23/0.92  pred_elim_cands:                        1
% 1.23/0.92  pred_elim:                              2
% 1.23/0.92  pred_elim_cl:                           2
% 1.23/0.92  pred_elim_cycles:                       4
% 1.23/0.92  merged_defs:                            0
% 1.23/0.92  merged_defs_ncl:                        0
% 1.23/0.92  bin_hyper_res:                          0
% 1.23/0.92  prep_cycles:                            4
% 1.23/0.92  pred_elim_time:                         0.
% 1.23/0.92  splitting_time:                         0.
% 1.23/0.92  sem_filter_time:                        0.
% 1.23/0.92  monotx_time:                            0.
% 1.23/0.92  subtype_inf_time:                       0.
% 1.23/0.92  
% 1.23/0.92  ------ Problem properties
% 1.23/0.92  
% 1.23/0.92  clauses:                                13
% 1.23/0.92  conjectures:                            2
% 1.23/0.92  epr:                                    0
% 1.23/0.92  horn:                                   11
% 1.23/0.92  ground:                                 3
% 1.23/0.92  unary:                                  3
% 1.23/0.92  binary:                                 6
% 1.23/0.92  lits:                                   27
% 1.23/0.92  lits_eq:                                6
% 1.23/0.92  fd_pure:                                0
% 1.23/0.92  fd_pseudo:                              0
% 1.23/0.92  fd_cond:                                0
% 1.23/0.92  fd_pseudo_cond:                         4
% 1.23/0.92  ac_symbols:                             0
% 1.23/0.92  
% 1.23/0.92  ------ Propositional Solver
% 1.23/0.92  
% 1.23/0.92  prop_solver_calls:                      25
% 1.23/0.92  prop_fast_solver_calls:                 335
% 1.23/0.92  smt_solver_calls:                       0
% 1.23/0.92  smt_fast_solver_calls:                  0
% 1.23/0.92  prop_num_of_clauses:                    647
% 1.23/0.92  prop_preprocess_simplified:             2582
% 1.23/0.92  prop_fo_subsumed:                       0
% 1.23/0.92  prop_solver_time:                       0.
% 1.23/0.92  smt_solver_time:                        0.
% 1.23/0.92  smt_fast_solver_time:                   0.
% 1.23/0.92  prop_fast_solver_time:                  0.
% 1.23/0.92  prop_unsat_core_time:                   0.
% 1.23/0.92  
% 1.23/0.92  ------ QBF
% 1.23/0.92  
% 1.23/0.92  qbf_q_res:                              0
% 1.23/0.92  qbf_num_tautologies:                    0
% 1.23/0.92  qbf_prep_cycles:                        0
% 1.23/0.92  
% 1.23/0.92  ------ BMC1
% 1.23/0.92  
% 1.23/0.92  bmc1_current_bound:                     -1
% 1.23/0.92  bmc1_last_solved_bound:                 -1
% 1.23/0.92  bmc1_unsat_core_size:                   -1
% 1.23/0.92  bmc1_unsat_core_parents_size:           -1
% 1.23/0.92  bmc1_merge_next_fun:                    0
% 1.23/0.92  bmc1_unsat_core_clauses_time:           0.
% 1.23/0.92  
% 1.23/0.92  ------ Instantiation
% 1.23/0.92  
% 1.23/0.92  inst_num_of_clauses:                    178
% 1.23/0.92  inst_num_in_passive:                    21
% 1.23/0.92  inst_num_in_active:                     75
% 1.23/0.92  inst_num_in_unprocessed:                82
% 1.23/0.92  inst_num_of_loops:                      80
% 1.23/0.92  inst_num_of_learning_restarts:          0
% 1.23/0.92  inst_num_moves_active_passive:          4
% 1.23/0.92  inst_lit_activity:                      0
% 1.23/0.92  inst_lit_activity_moves:                0
% 1.23/0.92  inst_num_tautologies:                   0
% 1.23/0.92  inst_num_prop_implied:                  0
% 1.23/0.92  inst_num_existing_simplified:           0
% 1.23/0.92  inst_num_eq_res_simplified:             0
% 1.23/0.92  inst_num_child_elim:                    0
% 1.23/0.92  inst_num_of_dismatching_blockings:      9
% 1.23/0.92  inst_num_of_non_proper_insts:           95
% 1.23/0.92  inst_num_of_duplicates:                 0
% 1.23/0.92  inst_inst_num_from_inst_to_res:         0
% 1.23/0.92  inst_dismatching_checking_time:         0.
% 1.23/0.92  
% 1.23/0.92  ------ Resolution
% 1.23/0.92  
% 1.23/0.92  res_num_of_clauses:                     0
% 1.23/0.92  res_num_in_passive:                     0
% 1.23/0.92  res_num_in_active:                      0
% 1.23/0.92  res_num_of_loops:                       75
% 1.23/0.92  res_forward_subset_subsumed:            0
% 1.23/0.92  res_backward_subset_subsumed:           0
% 1.23/0.92  res_forward_subsumed:                   0
% 1.23/0.92  res_backward_subsumed:                  0
% 1.23/0.92  res_forward_subsumption_resolution:     0
% 1.23/0.92  res_backward_subsumption_resolution:    0
% 1.23/0.92  res_clause_to_clause_subsumption:       60
% 1.23/0.92  res_orphan_elimination:                 0
% 1.23/0.92  res_tautology_del:                      8
% 1.23/0.92  res_num_eq_res_simplified:              0
% 1.23/0.92  res_num_sel_changes:                    0
% 1.23/0.92  res_moves_from_active_to_pass:          0
% 1.23/0.92  
% 1.23/0.92  ------ Superposition
% 1.23/0.92  
% 1.23/0.92  sup_time_total:                         0.
% 1.23/0.92  sup_time_generating:                    0.
% 1.23/0.92  sup_time_sim_full:                      0.
% 1.23/0.92  sup_time_sim_immed:                     0.
% 1.23/0.92  
% 1.23/0.92  sup_num_of_clauses:                     34
% 1.23/0.92  sup_num_in_active:                      15
% 1.23/0.92  sup_num_in_passive:                     19
% 1.23/0.92  sup_num_of_loops:                       14
% 1.23/0.92  sup_fw_superposition:                   14
% 1.23/0.92  sup_bw_superposition:                   12
% 1.23/0.92  sup_immediate_simplified:               0
% 1.23/0.92  sup_given_eliminated:                   0
% 1.23/0.92  comparisons_done:                       0
% 1.23/0.92  comparisons_avoided:                    0
% 1.23/0.92  
% 1.23/0.92  ------ Simplifications
% 1.23/0.92  
% 1.23/0.92  
% 1.23/0.92  sim_fw_subset_subsumed:                 0
% 1.23/0.92  sim_bw_subset_subsumed:                 0
% 1.23/0.92  sim_fw_subsumed:                        0
% 1.23/0.92  sim_bw_subsumed:                        0
% 1.23/0.92  sim_fw_subsumption_res:                 0
% 1.23/0.92  sim_bw_subsumption_res:                 0
% 1.23/0.92  sim_tautology_del:                      2
% 1.23/0.92  sim_eq_tautology_del:                   0
% 1.23/0.92  sim_eq_res_simp:                        0
% 1.23/0.92  sim_fw_demodulated:                     0
% 1.23/0.92  sim_bw_demodulated:                     0
% 1.23/0.92  sim_light_normalised:                   0
% 1.23/0.92  sim_joinable_taut:                      0
% 1.23/0.92  sim_joinable_simp:                      0
% 1.23/0.92  sim_ac_normalised:                      0
% 1.23/0.92  sim_smt_subsumption:                    0
% 1.23/0.92  
%------------------------------------------------------------------------------
