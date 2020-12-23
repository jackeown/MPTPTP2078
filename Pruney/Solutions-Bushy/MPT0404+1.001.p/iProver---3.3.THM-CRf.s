%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0404+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:14 EST 2020

% Result     : Theorem 1.75s
% Output     : CNFRefutation 1.75s
% Verified   : 
% Statistics : Number of formulae       :   47 (  82 expanded)
%              Number of clauses        :   21 (  26 expanded)
%              Number of leaves         :    9 (  21 expanded)
%              Depth                    :   12
%              Number of atoms          :  172 ( 327 expanded)
%              Number of equality atoms :   50 (  80 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
    <=> ! [X2] :
          ~ ( ! [X3] :
                ~ ( r1_tarski(X2,X3)
                  & r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ~ ( ! [X3] :
                ~ ( r1_tarski(X2,X3)
                  & r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) )
     => r1_setfam_1(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f7,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
      | ? [X2] :
          ( ! [X3] :
              ( ~ r1_tarski(X2,X3)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f9,plain,(
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

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
      | ( ! [X3] :
            ( ~ r1_tarski(sK0(X0,X1),X3)
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f7,f9])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f4,conjecture,(
    ! [X0] : r1_setfam_1(k3_setfam_1(X0,X0),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0] : r1_setfam_1(k3_setfam_1(X0,X0),X0) ),
    inference(negated_conjecture,[],[f4])).

fof(f8,plain,(
    ? [X0] : ~ r1_setfam_1(k3_setfam_1(X0,X0),X0) ),
    inference(ennf_transformation,[],[f5])).

fof(f17,plain,
    ( ? [X0] : ~ r1_setfam_1(k3_setfam_1(X0,X0),X0)
   => ~ r1_setfam_1(k3_setfam_1(sK6,sK6),sK6) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ~ r1_setfam_1(k3_setfam_1(sK6,sK6),sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f8,f17])).

fof(f30,plain,(
    ~ r1_setfam_1(k3_setfam_1(sK6,sK6),sK6) ),
    inference(cnf_transformation,[],[f18])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_setfam_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k3_xboole_0(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( k3_setfam_1(X0,X1) = X2
        | ? [X3] :
            ( ( ! [X4,X5] :
                  ( k3_xboole_0(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X4,X5] :
                  ( k3_xboole_0(X4,X5) = X3
                  & r2_hidden(X5,X1)
                  & r2_hidden(X4,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ! [X4,X5] :
                  ( k3_xboole_0(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) ) )
            & ( ? [X4,X5] :
                  ( k3_xboole_0(X4,X5) = X3
                  & r2_hidden(X5,X1)
                  & r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_setfam_1(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( k3_setfam_1(X0,X1) = X2
        | ? [X3] :
            ( ( ! [X4,X5] :
                  ( k3_xboole_0(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X6,X7] :
                  ( k3_xboole_0(X6,X7) = X3
                  & r2_hidden(X7,X1)
                  & r2_hidden(X6,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k3_xboole_0(X9,X10) != X8
                  | ~ r2_hidden(X10,X1)
                  | ~ r2_hidden(X9,X0) ) )
            & ( ? [X11,X12] :
                  ( k3_xboole_0(X11,X12) = X8
                  & r2_hidden(X12,X1)
                  & r2_hidden(X11,X0) )
              | ~ r2_hidden(X8,X2) ) )
        | k3_setfam_1(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f11])).

fof(f15,plain,(
    ! [X8,X1,X0] :
      ( ? [X11,X12] :
          ( k3_xboole_0(X11,X12) = X8
          & r2_hidden(X12,X1)
          & r2_hidden(X11,X0) )
     => ( k3_xboole_0(sK4(X0,X1,X8),sK5(X0,X1,X8)) = X8
        & r2_hidden(sK5(X0,X1,X8),X1)
        & r2_hidden(sK4(X0,X1,X8),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X6,X7] :
          ( k3_xboole_0(X6,X7) = X3
          & r2_hidden(X7,X1)
          & r2_hidden(X6,X0) )
     => ( k3_xboole_0(sK2(X0,X1,X2),sK3(X0,X1,X2)) = X3
        & r2_hidden(sK3(X0,X1,X2),X1)
        & r2_hidden(sK2(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4,X5] :
                ( k3_xboole_0(X4,X5) != X3
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X6,X7] :
                ( k3_xboole_0(X6,X7) = X3
                & r2_hidden(X7,X1)
                & r2_hidden(X6,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X5,X4] :
              ( k3_xboole_0(X4,X5) != sK1(X0,X1,X2)
              | ~ r2_hidden(X5,X1)
              | ~ r2_hidden(X4,X0) )
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( ? [X7,X6] :
              ( k3_xboole_0(X6,X7) = sK1(X0,X1,X2)
              & r2_hidden(X7,X1)
              & r2_hidden(X6,X0) )
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( k3_setfam_1(X0,X1) = X2
        | ( ( ! [X4,X5] :
                ( k3_xboole_0(X4,X5) != sK1(X0,X1,X2)
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X0) )
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( ( k3_xboole_0(sK2(X0,X1,X2),sK3(X0,X1,X2)) = sK1(X0,X1,X2)
              & r2_hidden(sK3(X0,X1,X2),X1)
              & r2_hidden(sK2(X0,X1,X2),X0) )
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k3_xboole_0(X9,X10) != X8
                  | ~ r2_hidden(X10,X1)
                  | ~ r2_hidden(X9,X0) ) )
            & ( ( k3_xboole_0(sK4(X0,X1,X8),sK5(X0,X1,X8)) = X8
                & r2_hidden(sK5(X0,X1,X8),X1)
                & r2_hidden(sK4(X0,X1,X8),X0) )
              | ~ r2_hidden(X8,X2) ) )
        | k3_setfam_1(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f12,f15,f14,f13])).

fof(f23,plain,(
    ! [X2,X0,X8,X1] :
      ( k3_xboole_0(sK4(X0,X1,X8),sK5(X0,X1,X8)) = X8
      | ~ r2_hidden(X8,X2)
      | k3_setfam_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f33,plain,(
    ! [X0,X8,X1] :
      ( k3_xboole_0(sK4(X0,X1,X8),sK5(X0,X1,X8)) = X8
      | ~ r2_hidden(X8,k3_setfam_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f23])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f20,plain,(
    ! [X0,X3,X1] :
      ( r1_setfam_1(X0,X1)
      | ~ r1_tarski(sK0(X0,X1),X3)
      | ~ r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f21,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK4(X0,X1,X8),X0)
      | ~ r2_hidden(X8,X2)
      | k3_setfam_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f35,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK4(X0,X1,X8),X0)
      | ~ r2_hidden(X8,k3_setfam_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f21])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_setfam_1(X0,X1) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_11,negated_conjecture,
    ( ~ r1_setfam_1(k3_setfam_1(sK6,sK6),sK6) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_160,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | k3_setfam_1(sK6,sK6) != X0
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_11])).

cnf(c_161,plain,
    ( r2_hidden(sK0(k3_setfam_1(sK6,sK6),sK6),k3_setfam_1(sK6,sK6)) ),
    inference(unflattening,[status(thm)],[c_160])).

cnf(c_445,plain,
    ( r2_hidden(sK0(k3_setfam_1(sK6,sK6),sK6),k3_setfam_1(sK6,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_161])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,k3_setfam_1(X1,X2))
    | k3_xboole_0(sK4(X1,X2,X0),sK5(X1,X2,X0)) = X0 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_448,plain,
    ( k3_xboole_0(sK4(X0,X1,X2),sK5(X0,X1,X2)) = X2
    | r2_hidden(X2,k3_setfam_1(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_736,plain,
    ( k3_xboole_0(sK4(sK6,sK6,sK0(k3_setfam_1(sK6,sK6),sK6)),sK5(sK6,sK6,sK0(k3_setfam_1(sK6,sK6),sK6))) = sK0(k3_setfam_1(sK6,sK6),sK6) ),
    inference(superposition,[status(thm)],[c_445,c_448])).

cnf(c_10,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(sK0(X2,X1),X0)
    | r1_setfam_1(X2,X1) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_167,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(sK0(X2,X1),X0)
    | k3_setfam_1(sK6,sK6) != X2
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_11])).

cnf(c_168,plain,
    ( ~ r2_hidden(X0,sK6)
    | ~ r1_tarski(sK0(k3_setfam_1(sK6,sK6),sK6),X0) ),
    inference(unflattening,[status(thm)],[c_167])).

cnf(c_184,plain,
    ( ~ r2_hidden(X0,sK6)
    | X0 != X1
    | sK0(k3_setfam_1(sK6,sK6),sK6) != k3_xboole_0(X1,X2) ),
    inference(resolution_lifted,[status(thm)],[c_10,c_168])).

cnf(c_185,plain,
    ( ~ r2_hidden(X0,sK6)
    | sK0(k3_setfam_1(sK6,sK6),sK6) != k3_xboole_0(X0,X1) ),
    inference(unflattening,[status(thm)],[c_184])).

cnf(c_444,plain,
    ( sK0(k3_setfam_1(sK6,sK6),sK6) != k3_xboole_0(X0,X1)
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_185])).

cnf(c_754,plain,
    ( r2_hidden(sK4(sK6,sK6,sK0(k3_setfam_1(sK6,sK6),sK6)),sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_736,c_444])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k3_setfam_1(X1,X2))
    | r2_hidden(sK4(X1,X2,X0),X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_530,plain,
    ( r2_hidden(sK4(sK6,sK6,sK0(k3_setfam_1(sK6,sK6),sK6)),sK6)
    | ~ r2_hidden(sK0(k3_setfam_1(sK6,sK6),sK6),k3_setfam_1(sK6,sK6)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_531,plain,
    ( r2_hidden(sK4(sK6,sK6,sK0(k3_setfam_1(sK6,sK6),sK6)),sK6) = iProver_top
    | r2_hidden(sK0(k3_setfam_1(sK6,sK6),sK6),k3_setfam_1(sK6,sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_530])).

cnf(c_162,plain,
    ( r2_hidden(sK0(k3_setfam_1(sK6,sK6),sK6),k3_setfam_1(sK6,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_161])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_754,c_531,c_162])).


%------------------------------------------------------------------------------
