%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0290+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:56 EST 2020

% Result     : Theorem 2.08s
% Output     : CNFRefutation 2.08s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 112 expanded)
%              Number of clauses        :   26 (  28 expanded)
%              Number of leaves         :   10 (  30 expanded)
%              Depth                    :   11
%              Number of atoms          :  255 ( 631 expanded)
%              Number of equality atoms :   32 (  72 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] :
                  ( r2_hidden(X3,X0)
                  & r2_hidden(X2,X3) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) ) )
            & ( ? [X3] :
                  ( r2_hidden(X3,X0)
                  & r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] :
                  ( r2_hidden(X4,X0)
                  & r2_hidden(X2,X4) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ? [X7] :
                  ( r2_hidden(X7,X0)
                  & r2_hidden(X5,X7) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f11])).

fof(f15,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( r2_hidden(X7,X0)
          & r2_hidden(X5,X7) )
     => ( r2_hidden(sK3(X0,X5),X0)
        & r2_hidden(X5,sK3(X0,X5)) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X0)
          & r2_hidden(X2,X4) )
     => ( r2_hidden(sK2(X0,X1),X0)
        & r2_hidden(X2,sK2(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(X2,X3) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( r2_hidden(X4,X0)
                & r2_hidden(X2,X4) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( ~ r2_hidden(X3,X0)
              | ~ r2_hidden(sK1(X0,X1),X3) )
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( ? [X4] :
              ( r2_hidden(X4,X0)
              & r2_hidden(sK1(X0,X1),X4) )
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(sK1(X0,X1),X3) )
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( ( r2_hidden(sK2(X0,X1),X0)
              & r2_hidden(sK1(X0,X1),sK2(X0,X1)) )
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ( r2_hidden(sK3(X0,X5),X0)
                & r2_hidden(X5,sK3(X0,X5)) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f12,f15,f14,f13])).

fof(f28,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(X6,X0)
      | ~ r2_hidden(X5,X6)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f39,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k3_tarski(X0))
      | ~ r2_hidden(X6,X0)
      | ~ r2_hidden(X5,X6) ) ),
    inference(equality_resolution,[],[f28])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f17])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f18])).

fof(f20,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
          | ~ r2_hidden(sK4(X0,X1,X2),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK4(X0,X1,X2),X1)
            & r2_hidden(sK4(X0,X1,X2),X0) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
            | ~ r2_hidden(sK4(X0,X1,X2),X0)
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK4(X0,X1,X2),X1)
              & r2_hidden(sK4(X0,X1,X2),X0) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f20])).

fof(f34,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f42,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f34])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f7,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f9,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f7,f9])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f4,conjecture,(
    ! [X0,X1] : r1_tarski(k3_tarski(k3_xboole_0(X0,X1)),k3_xboole_0(k3_tarski(X0),k3_tarski(X1))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] : r1_tarski(k3_tarski(k3_xboole_0(X0,X1)),k3_xboole_0(k3_tarski(X0),k3_tarski(X1))) ),
    inference(negated_conjecture,[],[f4])).

fof(f8,plain,(
    ? [X0,X1] : ~ r1_tarski(k3_tarski(k3_xboole_0(X0,X1)),k3_xboole_0(k3_tarski(X0),k3_tarski(X1))) ),
    inference(ennf_transformation,[],[f5])).

fof(f22,plain,
    ( ? [X0,X1] : ~ r1_tarski(k3_tarski(k3_xboole_0(X0,X1)),k3_xboole_0(k3_tarski(X0),k3_tarski(X1)))
   => ~ r1_tarski(k3_tarski(k3_xboole_0(sK5,sK6)),k3_xboole_0(k3_tarski(sK5),k3_tarski(sK6))) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ~ r1_tarski(k3_tarski(k3_xboole_0(sK5,sK6)),k3_xboole_0(k3_tarski(sK5),k3_tarski(sK6))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f8,f22])).

fof(f38,plain,(
    ~ r1_tarski(k3_tarski(k3_xboole_0(sK5,sK6)),k3_xboole_0(k3_tarski(sK5),k3_tarski(sK6))) ),
    inference(cnf_transformation,[],[f23])).

fof(f32,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f44,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f32])).

fof(f33,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f43,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f33])).

fof(f26,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(X5,sK3(X0,X5))
      | ~ r2_hidden(X5,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f41,plain,(
    ! [X0,X5] :
      ( r2_hidden(X5,sK3(X0,X5))
      | ~ r2_hidden(X5,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f26])).

fof(f27,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK3(X0,X5),X0)
      | ~ r2_hidden(X5,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f40,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK3(X0,X5),X0)
      | ~ r2_hidden(X5,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f27])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f10])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,k3_tarski(X1)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_815,plain,
    ( ~ r2_hidden(X0,sK3(k3_xboole_0(sK5,sK6),sK0(k3_tarski(k3_xboole_0(sK5,sK6)),k3_xboole_0(k3_tarski(sK5),k3_tarski(sK6)))))
    | r2_hidden(X0,k3_tarski(sK5))
    | ~ r2_hidden(sK3(k3_xboole_0(sK5,sK6),sK0(k3_tarski(k3_xboole_0(sK5,sK6)),k3_xboole_0(k3_tarski(sK5),k3_tarski(sK6)))),sK5) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1272,plain,
    ( ~ r2_hidden(sK3(k3_xboole_0(sK5,sK6),sK0(k3_tarski(k3_xboole_0(sK5,sK6)),k3_xboole_0(k3_tarski(sK5),k3_tarski(sK6)))),sK5)
    | ~ r2_hidden(sK0(k3_tarski(k3_xboole_0(sK5,sK6)),k3_xboole_0(k3_tarski(sK5),k3_tarski(sK6))),sK3(k3_xboole_0(sK5,sK6),sK0(k3_tarski(k3_xboole_0(sK5,sK6)),k3_xboole_0(k3_tarski(sK5),k3_tarski(sK6)))))
    | r2_hidden(sK0(k3_tarski(k3_xboole_0(sK5,sK6)),k3_xboole_0(k3_tarski(sK5),k3_tarski(sK6))),k3_tarski(sK5)) ),
    inference(instantiation,[status(thm)],[c_815])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_519,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X0,k3_xboole_0(X2,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_14,negated_conjecture,
    ( ~ r1_tarski(k3_tarski(k3_xboole_0(sK5,sK6)),k3_xboole_0(k3_tarski(sK5),k3_tarski(sK6))) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_179,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | k3_xboole_0(k3_tarski(sK5),k3_tarski(sK6)) != X1
    | k3_tarski(k3_xboole_0(sK5,sK6)) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_14])).

cnf(c_180,plain,
    ( ~ r2_hidden(sK0(k3_tarski(k3_xboole_0(sK5,sK6)),k3_xboole_0(k3_tarski(sK5),k3_tarski(sK6))),k3_xboole_0(k3_tarski(sK5),k3_tarski(sK6))) ),
    inference(unflattening,[status(thm)],[c_179])).

cnf(c_515,plain,
    ( r2_hidden(sK0(k3_tarski(k3_xboole_0(sK5,sK6)),k3_xboole_0(k3_tarski(sK5),k3_tarski(sK6))),k3_xboole_0(k3_tarski(sK5),k3_tarski(sK6))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_180])).

cnf(c_1206,plain,
    ( r2_hidden(sK0(k3_tarski(k3_xboole_0(sK5,sK6)),k3_xboole_0(k3_tarski(sK5),k3_tarski(sK6))),k3_tarski(sK6)) != iProver_top
    | r2_hidden(sK0(k3_tarski(k3_xboole_0(sK5,sK6)),k3_xboole_0(k3_tarski(sK5),k3_tarski(sK6))),k3_tarski(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_519,c_515])).

cnf(c_1211,plain,
    ( ~ r2_hidden(sK0(k3_tarski(k3_xboole_0(sK5,sK6)),k3_xboole_0(k3_tarski(sK5),k3_tarski(sK6))),k3_tarski(sK6))
    | ~ r2_hidden(sK0(k3_tarski(k3_xboole_0(sK5,sK6)),k3_xboole_0(k3_tarski(sK5),k3_tarski(sK6))),k3_tarski(sK5)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1206])).

cnf(c_762,plain,
    ( ~ r2_hidden(X0,sK3(k3_xboole_0(sK5,sK6),sK0(k3_tarski(k3_xboole_0(sK5,sK6)),k3_xboole_0(k3_tarski(sK5),k3_tarski(sK6)))))
    | r2_hidden(X0,k3_tarski(sK6))
    | ~ r2_hidden(sK3(k3_xboole_0(sK5,sK6),sK0(k3_tarski(k3_xboole_0(sK5,sK6)),k3_xboole_0(k3_tarski(sK5),k3_tarski(sK6)))),sK6) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1174,plain,
    ( ~ r2_hidden(sK3(k3_xboole_0(sK5,sK6),sK0(k3_tarski(k3_xboole_0(sK5,sK6)),k3_xboole_0(k3_tarski(sK5),k3_tarski(sK6)))),sK6)
    | ~ r2_hidden(sK0(k3_tarski(k3_xboole_0(sK5,sK6)),k3_xboole_0(k3_tarski(sK5),k3_tarski(sK6))),sK3(k3_xboole_0(sK5,sK6),sK0(k3_tarski(k3_xboole_0(sK5,sK6)),k3_xboole_0(k3_tarski(sK5),k3_tarski(sK6)))))
    | r2_hidden(sK0(k3_tarski(k3_xboole_0(sK5,sK6)),k3_xboole_0(k3_tarski(sK5),k3_tarski(sK6))),k3_tarski(sK6)) ),
    inference(instantiation,[status(thm)],[c_762])).

cnf(c_13,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_679,plain,
    ( ~ r2_hidden(sK3(k3_xboole_0(sK5,sK6),sK0(k3_tarski(k3_xboole_0(sK5,sK6)),k3_xboole_0(k3_tarski(sK5),k3_tarski(sK6)))),k3_xboole_0(sK5,sK6))
    | r2_hidden(sK3(k3_xboole_0(sK5,sK6),sK0(k3_tarski(k3_xboole_0(sK5,sK6)),k3_xboole_0(k3_tarski(sK5),k3_tarski(sK6)))),sK5) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_12,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_676,plain,
    ( ~ r2_hidden(sK3(k3_xboole_0(sK5,sK6),sK0(k3_tarski(k3_xboole_0(sK5,sK6)),k3_xboole_0(k3_tarski(sK5),k3_tarski(sK6)))),k3_xboole_0(sK5,sK6))
    | r2_hidden(sK3(k3_xboole_0(sK5,sK6),sK0(k3_tarski(k3_xboole_0(sK5,sK6)),k3_xboole_0(k3_tarski(sK5),k3_tarski(sK6)))),sK6) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_7,plain,
    ( r2_hidden(X0,sK3(X1,X0))
    | ~ r2_hidden(X0,k3_tarski(X1)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_633,plain,
    ( r2_hidden(sK0(k3_tarski(k3_xboole_0(sK5,sK6)),k3_xboole_0(k3_tarski(sK5),k3_tarski(sK6))),sK3(k3_xboole_0(sK5,sK6),sK0(k3_tarski(k3_xboole_0(sK5,sK6)),k3_xboole_0(k3_tarski(sK5),k3_tarski(sK6)))))
    | ~ r2_hidden(sK0(k3_tarski(k3_xboole_0(sK5,sK6)),k3_xboole_0(k3_tarski(sK5),k3_tarski(sK6))),k3_tarski(k3_xboole_0(sK5,sK6))) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,k3_tarski(X1))
    | r2_hidden(sK3(X1,X0),X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_630,plain,
    ( r2_hidden(sK3(k3_xboole_0(sK5,sK6),sK0(k3_tarski(k3_xboole_0(sK5,sK6)),k3_xboole_0(k3_tarski(sK5),k3_tarski(sK6)))),k3_xboole_0(sK5,sK6))
    | ~ r2_hidden(sK0(k3_tarski(k3_xboole_0(sK5,sK6)),k3_xboole_0(k3_tarski(sK5),k3_tarski(sK6))),k3_tarski(k3_xboole_0(sK5,sK6))) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_172,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | k3_xboole_0(k3_tarski(sK5),k3_tarski(sK6)) != X1
    | k3_tarski(k3_xboole_0(sK5,sK6)) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_14])).

cnf(c_173,plain,
    ( r2_hidden(sK0(k3_tarski(k3_xboole_0(sK5,sK6)),k3_xboole_0(k3_tarski(sK5),k3_tarski(sK6))),k3_tarski(k3_xboole_0(sK5,sK6))) ),
    inference(unflattening,[status(thm)],[c_172])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1272,c_1211,c_1174,c_679,c_676,c_633,c_630,c_173])).


%------------------------------------------------------------------------------
