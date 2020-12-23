%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0403+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:13 EST 2020

% Result     : Theorem 2.38s
% Output     : CNFRefutation 2.38s
% Verified   : 
% Statistics : Number of formulae       :   60 (  97 expanded)
%              Number of clauses        :   27 (  29 expanded)
%              Number of leaves         :   11 (  25 expanded)
%              Depth                    :   12
%              Number of atoms          :  227 ( 407 expanded)
%              Number of equality atoms :   74 (  74 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f36,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_setfam_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k2_xboole_0(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( k2_setfam_1(X0,X1) = X2
        | ? [X3] :
            ( ( ! [X4,X5] :
                  ( k2_xboole_0(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X4,X5] :
                  ( k2_xboole_0(X4,X5) = X3
                  & r2_hidden(X5,X1)
                  & r2_hidden(X4,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ! [X4,X5] :
                  ( k2_xboole_0(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) ) )
            & ( ? [X4,X5] :
                  ( k2_xboole_0(X4,X5) = X3
                  & r2_hidden(X5,X1)
                  & r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k2_setfam_1(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( k2_setfam_1(X0,X1) = X2
        | ? [X3] :
            ( ( ! [X4,X5] :
                  ( k2_xboole_0(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X6,X7] :
                  ( k2_xboole_0(X6,X7) = X3
                  & r2_hidden(X7,X1)
                  & r2_hidden(X6,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k2_xboole_0(X9,X10) != X8
                  | ~ r2_hidden(X10,X1)
                  | ~ r2_hidden(X9,X0) ) )
            & ( ? [X11,X12] :
                  ( k2_xboole_0(X11,X12) = X8
                  & r2_hidden(X12,X1)
                  & r2_hidden(X11,X0) )
              | ~ r2_hidden(X8,X2) ) )
        | k2_setfam_1(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f16])).

fof(f20,plain,(
    ! [X8,X1,X0] :
      ( ? [X11,X12] :
          ( k2_xboole_0(X11,X12) = X8
          & r2_hidden(X12,X1)
          & r2_hidden(X11,X0) )
     => ( k2_xboole_0(sK5(X0,X1,X8),sK6(X0,X1,X8)) = X8
        & r2_hidden(sK6(X0,X1,X8),X1)
        & r2_hidden(sK5(X0,X1,X8),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X6,X7] :
          ( k2_xboole_0(X6,X7) = X3
          & r2_hidden(X7,X1)
          & r2_hidden(X6,X0) )
     => ( k2_xboole_0(sK3(X0,X1,X2),sK4(X0,X1,X2)) = X3
        & r2_hidden(sK4(X0,X1,X2),X1)
        & r2_hidden(sK3(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4,X5] :
                ( k2_xboole_0(X4,X5) != X3
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X6,X7] :
                ( k2_xboole_0(X6,X7) = X3
                & r2_hidden(X7,X1)
                & r2_hidden(X6,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X5,X4] :
              ( k2_xboole_0(X4,X5) != sK2(X0,X1,X2)
              | ~ r2_hidden(X5,X1)
              | ~ r2_hidden(X4,X0) )
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ? [X7,X6] :
              ( k2_xboole_0(X6,X7) = sK2(X0,X1,X2)
              & r2_hidden(X7,X1)
              & r2_hidden(X6,X0) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( k2_setfam_1(X0,X1) = X2
        | ( ( ! [X4,X5] :
                ( k2_xboole_0(X4,X5) != sK2(X0,X1,X2)
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X0) )
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( ( k2_xboole_0(sK3(X0,X1,X2),sK4(X0,X1,X2)) = sK2(X0,X1,X2)
              & r2_hidden(sK4(X0,X1,X2),X1)
              & r2_hidden(sK3(X0,X1,X2),X0) )
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k2_xboole_0(X9,X10) != X8
                  | ~ r2_hidden(X10,X1)
                  | ~ r2_hidden(X9,X0) ) )
            & ( ( k2_xboole_0(sK5(X0,X1,X8),sK6(X0,X1,X8)) = X8
                & r2_hidden(sK6(X0,X1,X8),X1)
                & r2_hidden(sK5(X0,X1,X8),X0) )
              | ~ r2_hidden(X8,X2) ) )
        | k2_setfam_1(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f17,f20,f19,f18])).

fof(f31,plain,(
    ! [X2,X0,X10,X8,X1,X9] :
      ( r2_hidden(X8,X2)
      | k2_xboole_0(X9,X10) != X8
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0)
      | k2_setfam_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f39,plain,(
    ! [X2,X0,X10,X1,X9] :
      ( r2_hidden(k2_xboole_0(X9,X10),X2)
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0)
      | k2_setfam_1(X0,X1) != X2 ) ),
    inference(equality_resolution,[],[f31])).

fof(f40,plain,(
    ! [X0,X10,X1,X9] :
      ( r2_hidden(k2_xboole_0(X9,X10),k2_setfam_1(X0,X1))
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0) ) ),
    inference(equality_resolution,[],[f39])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
    <=> ! [X2] :
          ~ ( ! [X3] :
                ~ ( r1_tarski(X2,X3)
                  & r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
    <=> ! [X2] :
          ( ? [X3] :
              ( r1_tarski(X2,X3)
              & r2_hidden(X3,X1) )
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( r1_setfam_1(X0,X1)
        | ? [X2] :
            ( ! [X3] :
                ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( ? [X3] :
                ( r1_tarski(X2,X3)
                & r2_hidden(X3,X1) )
            | ~ r2_hidden(X2,X0) )
        | ~ r1_setfam_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( r1_setfam_1(X0,X1)
        | ? [X2] :
            ( ! [X3] :
                ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) )
      & ( ! [X4] :
            ( ? [X5] :
                ( r1_tarski(X4,X5)
                & r2_hidden(X5,X1) )
            | ~ r2_hidden(X4,X0) )
        | ~ r1_setfam_1(X0,X1) ) ) ),
    inference(rectify,[],[f11])).

fof(f14,plain,(
    ! [X4,X1] :
      ( ? [X5] :
          ( r1_tarski(X4,X5)
          & r2_hidden(X5,X1) )
     => ( r1_tarski(X4,sK1(X1,X4))
        & r2_hidden(sK1(X1,X4),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r1_tarski(X2,X3)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X0) )
     => ( ! [X3] :
            ( ~ r1_tarski(sK0(X0,X1),X3)
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( r1_setfam_1(X0,X1)
        | ( ! [X3] :
              ( ~ r1_tarski(sK0(X0,X1),X3)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X4] :
            ( ( r1_tarski(X4,sK1(X1,X4))
              & r2_hidden(sK1(X1,X4),X1) )
            | ~ r2_hidden(X4,X0) )
        | ~ r1_setfam_1(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f14,f13])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f25,plain,(
    ! [X4,X0,X1] :
      ( r1_tarski(X4,sK1(X1,X4))
      | ~ r2_hidden(X4,X0)
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f27,plain,(
    ! [X0,X3,X1] :
      ( r1_setfam_1(X0,X1)
      | ~ r1_tarski(sK0(X0,X1),X3)
      | ~ r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f24,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(sK1(X1,X4),X1)
      | ~ r2_hidden(X4,X0)
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f5,conjecture,(
    ! [X0] : r1_setfam_1(X0,k2_setfam_1(X0,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0] : r1_setfam_1(X0,k2_setfam_1(X0,X0)) ),
    inference(negated_conjecture,[],[f5])).

fof(f10,plain,(
    ? [X0] : ~ r1_setfam_1(X0,k2_setfam_1(X0,X0)) ),
    inference(ennf_transformation,[],[f6])).

fof(f22,plain,
    ( ? [X0] : ~ r1_setfam_1(X0,k2_setfam_1(X0,X0))
   => ~ r1_setfam_1(sK7,k2_setfam_1(sK7,sK7)) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ~ r1_setfam_1(sK7,k2_setfam_1(sK7,sK7)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f10,f22])).

fof(f38,plain,(
    ~ r1_setfam_1(sK7,k2_setfam_1(sK7,sK7)) ),
    inference(cnf_transformation,[],[f23])).

fof(f4,axiom,(
    ! [X0,X1] : r1_setfam_1(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0] : r1_setfam_1(X0,X0) ),
    inference(rectify,[],[f4])).

fof(f37,plain,(
    ! [X0] : r1_setfam_1(X0,X0) ),
    inference(cnf_transformation,[],[f8])).

cnf(c_12,plain,
    ( k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X3)
    | r2_hidden(k2_xboole_0(X2,X0),k2_setfam_1(X3,X1)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_581,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X3) != iProver_top
    | r2_hidden(k2_xboole_0(X2,X0),k2_setfam_1(X3,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1280,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X0,k2_setfam_1(X1,X2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_12,c_581])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_setfam_1(X0,X1) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_588,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_setfam_1(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(X0,sK1(X2,X0))
    | ~ r1_setfam_1(X1,X2) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_587,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X0,sK1(X2,X0)) = iProver_top
    | r1_setfam_1(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1327,plain,
    ( r1_tarski(sK0(X0,X1),sK1(X2,sK0(X0,X1))) = iProver_top
    | r1_setfam_1(X0,X2) != iProver_top
    | r1_setfam_1(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_588,c_587])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(sK0(X2,X1),X0)
    | r1_setfam_1(X2,X1) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_589,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(sK0(X2,X1),X0) != iProver_top
    | r1_setfam_1(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_5549,plain,
    ( r2_hidden(sK1(X0,sK0(X1,X2)),X2) != iProver_top
    | r1_setfam_1(X1,X0) != iProver_top
    | r1_setfam_1(X1,X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1327,c_589])).

cnf(c_6137,plain,
    ( r2_hidden(sK1(X0,sK0(X1,k2_setfam_1(X2,X3))),X2) != iProver_top
    | r2_hidden(sK1(X0,sK0(X1,k2_setfam_1(X2,X3))),X3) != iProver_top
    | r1_setfam_1(X1,X0) != iProver_top
    | r1_setfam_1(X1,k2_setfam_1(X2,X3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1280,c_5549])).

cnf(c_6149,plain,
    ( r2_hidden(sK1(sK7,sK0(sK7,k2_setfam_1(sK7,sK7))),sK7) != iProver_top
    | r1_setfam_1(sK7,k2_setfam_1(sK7,sK7)) = iProver_top
    | r1_setfam_1(sK7,sK7) != iProver_top ),
    inference(instantiation,[status(thm)],[c_6137])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK1(X2,X0),X2)
    | ~ r1_setfam_1(X1,X2) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_716,plain,
    ( r2_hidden(sK1(X0,sK0(sK7,k2_setfam_1(sK7,sK7))),X0)
    | ~ r2_hidden(sK0(sK7,k2_setfam_1(sK7,sK7)),sK7)
    | ~ r1_setfam_1(sK7,X0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_722,plain,
    ( r2_hidden(sK1(X0,sK0(sK7,k2_setfam_1(sK7,sK7))),X0) = iProver_top
    | r2_hidden(sK0(sK7,k2_setfam_1(sK7,sK7)),sK7) != iProver_top
    | r1_setfam_1(sK7,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_716])).

cnf(c_724,plain,
    ( r2_hidden(sK1(sK7,sK0(sK7,k2_setfam_1(sK7,sK7))),sK7) = iProver_top
    | r2_hidden(sK0(sK7,k2_setfam_1(sK7,sK7)),sK7) != iProver_top
    | r1_setfam_1(sK7,sK7) != iProver_top ),
    inference(instantiation,[status(thm)],[c_722])).

cnf(c_14,negated_conjecture,
    ( ~ r1_setfam_1(sK7,k2_setfam_1(sK7,sK7)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_212,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | k2_setfam_1(sK7,sK7) != X1
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_14])).

cnf(c_213,plain,
    ( r2_hidden(sK0(sK7,k2_setfam_1(sK7,sK7)),sK7) ),
    inference(unflattening,[status(thm)],[c_212])).

cnf(c_214,plain,
    ( r2_hidden(sK0(sK7,k2_setfam_1(sK7,sK7)),sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_213])).

cnf(c_13,plain,
    ( r1_setfam_1(X0,X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_16,plain,
    ( r1_setfam_1(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_18,plain,
    ( r1_setfam_1(sK7,sK7) = iProver_top ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_15,plain,
    ( r1_setfam_1(sK7,k2_setfam_1(sK7,sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6149,c_724,c_214,c_18,c_15])).


%------------------------------------------------------------------------------
