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
% DateTime   : Thu Dec  3 11:36:45 EST 2020

% Result     : Theorem 7.66s
% Output     : CNFRefutation 7.66s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 293 expanded)
%              Number of clauses        :   44 (  73 expanded)
%              Number of leaves         :   13 (  78 expanded)
%              Depth                    :   15
%              Number of atoms          :  351 (1720 expanded)
%              Number of equality atoms :   44 ( 234 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f14])).

fof(f16,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f16])).

fof(f33,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_tarski(X0),k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),k3_tarski(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),k3_tarski(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f18])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f19])).

fof(f21,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
            & ~ r2_hidden(sK1(X0,X1,X2),X0) )
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( r2_hidden(sK1(X0,X1,X2),X1)
          | r2_hidden(sK1(X0,X1,X2),X0)
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
              & ~ r2_hidden(sK1(X0,X1,X2),X0) )
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( r2_hidden(sK1(X0,X1,X2),X1)
            | r2_hidden(sK1(X0,X1,X2),X0)
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f20,f21])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | r2_hidden(sK1(X0,X1,X2),X1)
      | r2_hidden(sK1(X0,X1,X2),X0)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f8,conjecture,(
    ! [X0,X1] : k2_xboole_0(k3_tarski(X0),k3_tarski(X1)) = k3_tarski(k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] : k2_xboole_0(k3_tarski(X0),k3_tarski(X1)) = k3_tarski(k2_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f8])).

fof(f13,plain,(
    ? [X0,X1] : k2_xboole_0(k3_tarski(X0),k3_tarski(X1)) != k3_tarski(k2_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f9])).

fof(f31,plain,
    ( ? [X0,X1] : k2_xboole_0(k3_tarski(X0),k3_tarski(X1)) != k3_tarski(k2_xboole_0(X0,X1))
   => k2_xboole_0(k3_tarski(sK5),k3_tarski(sK6)) != k3_tarski(k2_xboole_0(sK5,sK6)) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    k2_xboole_0(k3_tarski(sK5),k3_tarski(sK6)) != k3_tarski(k2_xboole_0(sK5,sK6)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f13,f31])).

fof(f54,plain,(
    k2_xboole_0(k3_tarski(sK5),k3_tarski(sK6)) != k3_tarski(k2_xboole_0(sK5,sK6)) ),
    inference(cnf_transformation,[],[f32])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
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
    inference(nnf_transformation,[],[f6])).

fof(f26,plain,(
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
    inference(rectify,[],[f25])).

fof(f29,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( r2_hidden(X7,X0)
          & r2_hidden(X5,X7) )
     => ( r2_hidden(sK4(X0,X5),X0)
        & r2_hidden(X5,sK4(X0,X5)) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X0)
          & r2_hidden(X2,X4) )
     => ( r2_hidden(sK3(X0,X1),X0)
        & r2_hidden(X2,sK3(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
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
              | ~ r2_hidden(sK2(X0,X1),X3) )
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( ? [X4] :
              ( r2_hidden(X4,X0)
              & r2_hidden(sK2(X0,X1),X4) )
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(sK2(X0,X1),X3) )
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( ( r2_hidden(sK3(X0,X1),X0)
              & r2_hidden(sK2(X0,X1),sK3(X0,X1)) )
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ( r2_hidden(sK4(X0,X5),X0)
                & r2_hidden(X5,sK4(X0,X5)) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f26,f29,f28,f27])).

fof(f48,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK4(X0,X5),X0)
      | ~ r2_hidden(X5,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f61,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK4(X0,X5),X0)
      | ~ r2_hidden(X5,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f48])).

fof(f47,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(X5,sK4(X0,X5))
      | ~ r2_hidden(X5,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f62,plain,(
    ! [X0,X5] :
      ( r2_hidden(X5,sK4(X0,X5))
      | ~ r2_hidden(X5,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f47])).

fof(f37,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f56,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f37])).

fof(f49,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(X6,X0)
      | ~ r2_hidden(X5,X6)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f60,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k3_tarski(X0))
      | ~ r2_hidden(X6,X0)
      | ~ r2_hidden(X5,X6) ) ),
    inference(equality_resolution,[],[f49])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK1(X0,X1,X2),X0)
      | ~ r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f36,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f57,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f36])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f23])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f59,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f42])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK1(X0,X1,X2),X1)
      | ~ r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_12,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_5658,plain,
    ( r1_tarski(X0,k2_xboole_0(sK5,sK6))
    | ~ r1_tarski(X0,sK6) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_21100,plain,
    ( r1_tarski(sK6,k2_xboole_0(sK5,sK6))
    | ~ r1_tarski(sK6,sK6) ),
    inference(instantiation,[status(thm)],[c_5658])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_935,plain,
    ( r2_hidden(sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6))),X0)
    | ~ r2_hidden(sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6))),k3_tarski(sK6))
    | ~ r1_tarski(k3_tarski(sK6),X0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1906,plain,
    ( r2_hidden(sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6))),k3_tarski(X0))
    | ~ r2_hidden(sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6))),k3_tarski(sK6))
    | ~ r1_tarski(k3_tarski(sK6),k3_tarski(X0)) ),
    inference(instantiation,[status(thm)],[c_935])).

cnf(c_13277,plain,
    ( r2_hidden(sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6))),k3_tarski(k2_xboole_0(sK5,sK6)))
    | ~ r2_hidden(sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6))),k3_tarski(sK6))
    | ~ r1_tarski(k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6))) ),
    inference(instantiation,[status(thm)],[c_1906])).

cnf(c_20,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k3_tarski(X0),k3_tarski(X1)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_2051,plain,
    ( ~ r1_tarski(X0,k2_xboole_0(sK5,sK6))
    | r1_tarski(k3_tarski(X0),k3_tarski(k2_xboole_0(sK5,sK6))) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_13276,plain,
    ( r1_tarski(k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6)))
    | ~ r1_tarski(sK6,k2_xboole_0(sK5,sK6)) ),
    inference(instantiation,[status(thm)],[c_2051])).

cnf(c_5,plain,
    ( r2_hidden(sK1(X0,X1,X2),X1)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | r2_hidden(sK1(X0,X1,X2),X0)
    | k2_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_21,negated_conjecture,
    ( k2_xboole_0(k3_tarski(sK5),k3_tarski(sK6)) != k3_tarski(k2_xboole_0(sK5,sK6)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_5954,plain,
    ( r2_hidden(sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6))),k3_tarski(k2_xboole_0(sK5,sK6)))
    | r2_hidden(sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6))),k3_tarski(sK6))
    | r2_hidden(sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6))),k3_tarski(sK5)) ),
    inference(resolution,[status(thm)],[c_5,c_21])).

cnf(c_813,plain,
    ( r2_hidden(sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6))),k3_tarski(k2_xboole_0(sK5,sK6)))
    | r2_hidden(sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6))),k3_tarski(sK6))
    | r2_hidden(sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6))),k3_tarski(sK5))
    | k2_xboole_0(k3_tarski(sK5),k3_tarski(sK6)) = k3_tarski(k2_xboole_0(sK5,sK6)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,k3_tarski(X1))
    | r2_hidden(sK4(X1,X0),X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1073,plain,
    ( ~ r2_hidden(sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6))),k3_tarski(sK5))
    | r2_hidden(sK4(sK5,sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6)))),sK5) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_19,plain,
    ( r2_hidden(X0,sK4(X1,X0))
    | ~ r2_hidden(X0,k3_tarski(X1)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1072,plain,
    ( r2_hidden(sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6))),sK4(sK5,sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6)))))
    | ~ r2_hidden(sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6))),k3_tarski(sK5)) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1372,plain,
    ( r2_hidden(sK4(sK5,sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6)))),k2_xboole_0(sK5,X0))
    | ~ r2_hidden(sK4(sK5,sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6)))),sK5) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_4492,plain,
    ( r2_hidden(sK4(sK5,sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6)))),k2_xboole_0(sK5,sK6))
    | ~ r2_hidden(sK4(sK5,sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6)))),sK5) ),
    inference(instantiation,[status(thm)],[c_1372])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,k3_tarski(X1)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1340,plain,
    ( ~ r2_hidden(sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6))),sK4(sK5,sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6)))))
    | r2_hidden(sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6))),k3_tarski(X0))
    | ~ r2_hidden(sK4(sK5,sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6)))),X0) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_4819,plain,
    ( ~ r2_hidden(sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6))),sK4(sK5,sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6)))))
    | r2_hidden(sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6))),k3_tarski(k2_xboole_0(sK5,sK6)))
    | ~ r2_hidden(sK4(sK5,sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6)))),k2_xboole_0(sK5,sK6)) ),
    inference(instantiation,[status(thm)],[c_1340])).

cnf(c_6589,plain,
    ( r2_hidden(sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6))),k3_tarski(sK6))
    | r2_hidden(sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6))),k3_tarski(k2_xboole_0(sK5,sK6))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5954,c_21,c_813,c_1073,c_1072,c_4492,c_4819])).

cnf(c_6590,plain,
    ( r2_hidden(sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6))),k3_tarski(k2_xboole_0(sK5,sK6)))
    | r2_hidden(sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6))),k3_tarski(sK6)) ),
    inference(renaming,[status(thm)],[c_6589])).

cnf(c_2361,plain,
    ( ~ r2_hidden(X0,k3_tarski(X1))
    | r2_hidden(X0,k3_tarski(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(resolution,[status(thm)],[c_2,c_20])).

cnf(c_6785,plain,
    ( r2_hidden(sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6))),k3_tarski(X0))
    | r2_hidden(sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6))),k3_tarski(sK6))
    | ~ r1_tarski(k2_xboole_0(sK5,sK6),X0) ),
    inference(resolution,[status(thm)],[c_6590,c_2361])).

cnf(c_6850,plain,
    ( r2_hidden(sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6))),k3_tarski(sK6))
    | ~ r1_tarski(k2_xboole_0(sK5,sK6),sK6) ),
    inference(factoring,[status(thm)],[c_6785])).

cnf(c_856,plain,
    ( ~ r2_hidden(sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6))),k3_tarski(k2_xboole_0(sK5,sK6)))
    | r2_hidden(sK4(k2_xboole_0(sK5,sK6),sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6)))),k2_xboole_0(sK5,sK6)) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_855,plain,
    ( r2_hidden(sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6))),sK4(k2_xboole_0(sK5,sK6),sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6)))))
    | ~ r2_hidden(sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6))),k3_tarski(k2_xboole_0(sK5,sK6))) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_4,plain,
    ( ~ r2_hidden(sK1(X0,X1,X2),X2)
    | ~ r2_hidden(sK1(X0,X1,X2),X0)
    | k2_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1069,plain,
    ( ~ r2_hidden(sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6))),k3_tarski(k2_xboole_0(sK5,sK6)))
    | ~ r2_hidden(sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6))),k3_tarski(sK5))
    | k2_xboole_0(k3_tarski(sK5),k3_tarski(sK6)) = k3_tarski(k2_xboole_0(sK5,sK6)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1547,plain,
    ( ~ r2_hidden(sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6))),sK4(k2_xboole_0(sK5,sK6),sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6)))))
    | r2_hidden(sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6))),k3_tarski(X0))
    | ~ r2_hidden(sK4(k2_xboole_0(sK5,sK6),sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6)))),X0) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_1549,plain,
    ( ~ r2_hidden(sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6))),sK4(k2_xboole_0(sK5,sK6),sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6)))))
    | r2_hidden(sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6))),k3_tarski(sK5))
    | ~ r2_hidden(sK4(k2_xboole_0(sK5,sK6),sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6)))),sK5) ),
    inference(instantiation,[status(thm)],[c_1547])).

cnf(c_8,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1597,plain,
    ( ~ r2_hidden(sK4(k2_xboole_0(sK5,sK6),sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6)))),k2_xboole_0(sK5,sK6))
    | r2_hidden(sK4(k2_xboole_0(sK5,sK6),sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6)))),sK6)
    | r2_hidden(sK4(k2_xboole_0(sK5,sK6),sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6)))),sK5) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_7894,plain,
    ( ~ r2_hidden(sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6))),sK4(k2_xboole_0(sK5,sK6),sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6)))))
    | r2_hidden(sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6))),k3_tarski(sK6))
    | ~ r2_hidden(sK4(k2_xboole_0(sK5,sK6),sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6)))),sK6) ),
    inference(instantiation,[status(thm)],[c_1547])).

cnf(c_8031,plain,
    ( r2_hidden(sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6))),k3_tarski(sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6850,c_21,c_856,c_855,c_1069,c_1549,c_1597,c_6590,c_7894])).

cnf(c_11,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_5591,plain,
    ( r1_tarski(sK6,sK6) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_3,plain,
    ( ~ r2_hidden(sK1(X0,X1,X2),X1)
    | ~ r2_hidden(sK1(X0,X1,X2),X2)
    | k2_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_852,plain,
    ( ~ r2_hidden(sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6))),k3_tarski(k2_xboole_0(sK5,sK6)))
    | ~ r2_hidden(sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6))),k3_tarski(sK6))
    | k2_xboole_0(k3_tarski(sK5),k3_tarski(sK6)) = k3_tarski(k2_xboole_0(sK5,sK6)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_21100,c_13277,c_13276,c_8031,c_5591,c_852,c_21])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 11:04:19 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running in FOF mode
% 7.66/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.66/1.49  
% 7.66/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.66/1.49  
% 7.66/1.49  ------  iProver source info
% 7.66/1.49  
% 7.66/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.66/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.66/1.49  git: non_committed_changes: false
% 7.66/1.49  git: last_make_outside_of_git: false
% 7.66/1.49  
% 7.66/1.49  ------ 
% 7.66/1.49  
% 7.66/1.49  ------ Input Options
% 7.66/1.49  
% 7.66/1.49  --out_options                           all
% 7.66/1.49  --tptp_safe_out                         true
% 7.66/1.49  --problem_path                          ""
% 7.66/1.49  --include_path                          ""
% 7.66/1.49  --clausifier                            res/vclausify_rel
% 7.66/1.49  --clausifier_options                    --mode clausify
% 7.66/1.49  --stdin                                 false
% 7.66/1.49  --stats_out                             sel
% 7.66/1.49  
% 7.66/1.49  ------ General Options
% 7.66/1.49  
% 7.66/1.49  --fof                                   false
% 7.66/1.49  --time_out_real                         604.99
% 7.66/1.49  --time_out_virtual                      -1.
% 7.66/1.49  --symbol_type_check                     false
% 7.66/1.49  --clausify_out                          false
% 7.66/1.49  --sig_cnt_out                           false
% 7.66/1.49  --trig_cnt_out                          false
% 7.66/1.49  --trig_cnt_out_tolerance                1.
% 7.66/1.49  --trig_cnt_out_sk_spl                   false
% 7.66/1.49  --abstr_cl_out                          false
% 7.66/1.49  
% 7.66/1.49  ------ Global Options
% 7.66/1.49  
% 7.66/1.49  --schedule                              none
% 7.66/1.49  --add_important_lit                     false
% 7.66/1.49  --prop_solver_per_cl                    1000
% 7.66/1.49  --min_unsat_core                        false
% 7.66/1.49  --soft_assumptions                      false
% 7.66/1.49  --soft_lemma_size                       3
% 7.66/1.49  --prop_impl_unit_size                   0
% 7.66/1.49  --prop_impl_unit                        []
% 7.66/1.49  --share_sel_clauses                     true
% 7.66/1.49  --reset_solvers                         false
% 7.66/1.49  --bc_imp_inh                            [conj_cone]
% 7.66/1.49  --conj_cone_tolerance                   3.
% 7.66/1.49  --extra_neg_conj                        none
% 7.66/1.49  --large_theory_mode                     true
% 7.66/1.49  --prolific_symb_bound                   200
% 7.66/1.49  --lt_threshold                          2000
% 7.66/1.49  --clause_weak_htbl                      true
% 7.66/1.49  --gc_record_bc_elim                     false
% 7.66/1.49  
% 7.66/1.49  ------ Preprocessing Options
% 7.66/1.49  
% 7.66/1.49  --preprocessing_flag                    true
% 7.66/1.49  --time_out_prep_mult                    0.1
% 7.66/1.49  --splitting_mode                        input
% 7.66/1.49  --splitting_grd                         true
% 7.66/1.49  --splitting_cvd                         false
% 7.66/1.49  --splitting_cvd_svl                     false
% 7.66/1.49  --splitting_nvd                         32
% 7.66/1.49  --sub_typing                            true
% 7.66/1.49  --prep_gs_sim                           false
% 7.66/1.49  --prep_unflatten                        true
% 7.66/1.49  --prep_res_sim                          true
% 7.66/1.49  --prep_upred                            true
% 7.66/1.49  --prep_sem_filter                       exhaustive
% 7.66/1.49  --prep_sem_filter_out                   false
% 7.66/1.49  --pred_elim                             false
% 7.66/1.49  --res_sim_input                         true
% 7.66/1.49  --eq_ax_congr_red                       true
% 7.66/1.49  --pure_diseq_elim                       true
% 7.66/1.49  --brand_transform                       false
% 7.66/1.49  --non_eq_to_eq                          false
% 7.66/1.49  --prep_def_merge                        true
% 7.66/1.49  --prep_def_merge_prop_impl              false
% 7.66/1.49  --prep_def_merge_mbd                    true
% 7.66/1.49  --prep_def_merge_tr_red                 false
% 7.66/1.49  --prep_def_merge_tr_cl                  false
% 7.66/1.49  --smt_preprocessing                     true
% 7.66/1.49  --smt_ac_axioms                         fast
% 7.66/1.49  --preprocessed_out                      false
% 7.66/1.49  --preprocessed_stats                    false
% 7.66/1.49  
% 7.66/1.49  ------ Abstraction refinement Options
% 7.66/1.49  
% 7.66/1.49  --abstr_ref                             []
% 7.66/1.49  --abstr_ref_prep                        false
% 7.66/1.49  --abstr_ref_until_sat                   false
% 7.66/1.49  --abstr_ref_sig_restrict                funpre
% 7.66/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.66/1.49  --abstr_ref_under                       []
% 7.66/1.49  
% 7.66/1.49  ------ SAT Options
% 7.66/1.49  
% 7.66/1.49  --sat_mode                              false
% 7.66/1.49  --sat_fm_restart_options                ""
% 7.66/1.49  --sat_gr_def                            false
% 7.66/1.49  --sat_epr_types                         true
% 7.66/1.49  --sat_non_cyclic_types                  false
% 7.66/1.49  --sat_finite_models                     false
% 7.66/1.49  --sat_fm_lemmas                         false
% 7.66/1.49  --sat_fm_prep                           false
% 7.66/1.49  --sat_fm_uc_incr                        true
% 7.66/1.49  --sat_out_model                         small
% 7.66/1.49  --sat_out_clauses                       false
% 7.66/1.49  
% 7.66/1.49  ------ QBF Options
% 7.66/1.49  
% 7.66/1.49  --qbf_mode                              false
% 7.66/1.49  --qbf_elim_univ                         false
% 7.66/1.49  --qbf_dom_inst                          none
% 7.66/1.49  --qbf_dom_pre_inst                      false
% 7.66/1.49  --qbf_sk_in                             false
% 7.66/1.49  --qbf_pred_elim                         true
% 7.66/1.49  --qbf_split                             512
% 7.66/1.49  
% 7.66/1.49  ------ BMC1 Options
% 7.66/1.49  
% 7.66/1.49  --bmc1_incremental                      false
% 7.66/1.49  --bmc1_axioms                           reachable_all
% 7.66/1.49  --bmc1_min_bound                        0
% 7.66/1.49  --bmc1_max_bound                        -1
% 7.66/1.49  --bmc1_max_bound_default                -1
% 7.66/1.49  --bmc1_symbol_reachability              true
% 7.66/1.49  --bmc1_property_lemmas                  false
% 7.66/1.49  --bmc1_k_induction                      false
% 7.66/1.49  --bmc1_non_equiv_states                 false
% 7.66/1.49  --bmc1_deadlock                         false
% 7.66/1.49  --bmc1_ucm                              false
% 7.66/1.49  --bmc1_add_unsat_core                   none
% 7.66/1.49  --bmc1_unsat_core_children              false
% 7.66/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.66/1.49  --bmc1_out_stat                         full
% 7.66/1.49  --bmc1_ground_init                      false
% 7.66/1.49  --bmc1_pre_inst_next_state              false
% 7.66/1.49  --bmc1_pre_inst_state                   false
% 7.66/1.49  --bmc1_pre_inst_reach_state             false
% 7.66/1.49  --bmc1_out_unsat_core                   false
% 7.66/1.49  --bmc1_aig_witness_out                  false
% 7.66/1.49  --bmc1_verbose                          false
% 7.66/1.49  --bmc1_dump_clauses_tptp                false
% 7.66/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.66/1.49  --bmc1_dump_file                        -
% 7.66/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.66/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.66/1.49  --bmc1_ucm_extend_mode                  1
% 7.66/1.49  --bmc1_ucm_init_mode                    2
% 7.66/1.49  --bmc1_ucm_cone_mode                    none
% 7.66/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.66/1.49  --bmc1_ucm_relax_model                  4
% 7.66/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.66/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.66/1.49  --bmc1_ucm_layered_model                none
% 7.66/1.49  --bmc1_ucm_max_lemma_size               10
% 7.66/1.49  
% 7.66/1.49  ------ AIG Options
% 7.66/1.49  
% 7.66/1.49  --aig_mode                              false
% 7.66/1.49  
% 7.66/1.49  ------ Instantiation Options
% 7.66/1.49  
% 7.66/1.49  --instantiation_flag                    true
% 7.66/1.49  --inst_sos_flag                         false
% 7.66/1.49  --inst_sos_phase                        true
% 7.66/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.66/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.66/1.49  --inst_lit_sel_side                     num_symb
% 7.66/1.49  --inst_solver_per_active                1400
% 7.66/1.49  --inst_solver_calls_frac                1.
% 7.66/1.49  --inst_passive_queue_type               priority_queues
% 7.66/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.66/1.49  --inst_passive_queues_freq              [25;2]
% 7.66/1.49  --inst_dismatching                      true
% 7.66/1.49  --inst_eager_unprocessed_to_passive     true
% 7.66/1.49  --inst_prop_sim_given                   true
% 7.66/1.49  --inst_prop_sim_new                     false
% 7.66/1.49  --inst_subs_new                         false
% 7.66/1.49  --inst_eq_res_simp                      false
% 7.66/1.49  --inst_subs_given                       false
% 7.66/1.49  --inst_orphan_elimination               true
% 7.66/1.49  --inst_learning_loop_flag               true
% 7.66/1.49  --inst_learning_start                   3000
% 7.66/1.49  --inst_learning_factor                  2
% 7.66/1.49  --inst_start_prop_sim_after_learn       3
% 7.66/1.49  --inst_sel_renew                        solver
% 7.66/1.49  --inst_lit_activity_flag                true
% 7.66/1.49  --inst_restr_to_given                   false
% 7.66/1.49  --inst_activity_threshold               500
% 7.66/1.49  --inst_out_proof                        true
% 7.66/1.49  
% 7.66/1.49  ------ Resolution Options
% 7.66/1.49  
% 7.66/1.49  --resolution_flag                       true
% 7.66/1.49  --res_lit_sel                           adaptive
% 7.66/1.49  --res_lit_sel_side                      none
% 7.66/1.49  --res_ordering                          kbo
% 7.66/1.49  --res_to_prop_solver                    active
% 7.66/1.49  --res_prop_simpl_new                    false
% 7.66/1.49  --res_prop_simpl_given                  true
% 7.66/1.49  --res_passive_queue_type                priority_queues
% 7.66/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.66/1.49  --res_passive_queues_freq               [15;5]
% 7.66/1.49  --res_forward_subs                      full
% 7.66/1.49  --res_backward_subs                     full
% 7.66/1.49  --res_forward_subs_resolution           true
% 7.66/1.49  --res_backward_subs_resolution          true
% 7.66/1.49  --res_orphan_elimination                true
% 7.66/1.49  --res_time_limit                        2.
% 7.66/1.49  --res_out_proof                         true
% 7.66/1.49  
% 7.66/1.49  ------ Superposition Options
% 7.66/1.49  
% 7.66/1.49  --superposition_flag                    true
% 7.66/1.49  --sup_passive_queue_type                priority_queues
% 7.66/1.49  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.66/1.49  --sup_passive_queues_freq               [1;4]
% 7.66/1.49  --demod_completeness_check              fast
% 7.66/1.49  --demod_use_ground                      true
% 7.66/1.49  --sup_to_prop_solver                    passive
% 7.66/1.49  --sup_prop_simpl_new                    true
% 7.66/1.49  --sup_prop_simpl_given                  true
% 7.66/1.49  --sup_fun_splitting                     false
% 7.66/1.49  --sup_smt_interval                      50000
% 7.66/1.49  
% 7.66/1.49  ------ Superposition Simplification Setup
% 7.66/1.49  
% 7.66/1.49  --sup_indices_passive                   []
% 7.66/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.66/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.66/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.66/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.66/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.66/1.49  --sup_full_bw                           [BwDemod]
% 7.66/1.49  --sup_immed_triv                        [TrivRules]
% 7.66/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.66/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.66/1.49  --sup_immed_bw_main                     []
% 7.66/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.66/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.66/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.66/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.66/1.49  
% 7.66/1.49  ------ Combination Options
% 7.66/1.49  
% 7.66/1.49  --comb_res_mult                         3
% 7.66/1.49  --comb_sup_mult                         2
% 7.66/1.49  --comb_inst_mult                        10
% 7.66/1.49  
% 7.66/1.49  ------ Debug Options
% 7.66/1.49  
% 7.66/1.49  --dbg_backtrace                         false
% 7.66/1.49  --dbg_dump_prop_clauses                 false
% 7.66/1.49  --dbg_dump_prop_clauses_file            -
% 7.66/1.49  --dbg_out_stat                          false
% 7.66/1.49  ------ Parsing...
% 7.66/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.66/1.49  
% 7.66/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 7.66/1.49  
% 7.66/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.66/1.49  
% 7.66/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.66/1.49  ------ Proving...
% 7.66/1.49  ------ Problem Properties 
% 7.66/1.49  
% 7.66/1.49  
% 7.66/1.49  clauses                                 21
% 7.66/1.49  conjectures                             1
% 7.66/1.49  EPR                                     3
% 7.66/1.49  Horn                                    16
% 7.66/1.49  unary                                   3
% 7.66/1.49  binary                                  8
% 7.66/1.49  lits                                    51
% 7.66/1.49  lits eq                                 8
% 7.66/1.49  fd_pure                                 0
% 7.66/1.49  fd_pseudo                               0
% 7.66/1.49  fd_cond                                 0
% 7.66/1.49  fd_pseudo_cond                          7
% 7.66/1.49  AC symbols                              0
% 7.66/1.49  
% 7.66/1.49  ------ Input Options Time Limit: Unbounded
% 7.66/1.49  
% 7.66/1.49  
% 7.66/1.49  ------ 
% 7.66/1.49  Current options:
% 7.66/1.49  ------ 
% 7.66/1.49  
% 7.66/1.49  ------ Input Options
% 7.66/1.49  
% 7.66/1.49  --out_options                           all
% 7.66/1.49  --tptp_safe_out                         true
% 7.66/1.49  --problem_path                          ""
% 7.66/1.49  --include_path                          ""
% 7.66/1.49  --clausifier                            res/vclausify_rel
% 7.66/1.49  --clausifier_options                    --mode clausify
% 7.66/1.49  --stdin                                 false
% 7.66/1.49  --stats_out                             sel
% 7.66/1.49  
% 7.66/1.49  ------ General Options
% 7.66/1.49  
% 7.66/1.49  --fof                                   false
% 7.66/1.49  --time_out_real                         604.99
% 7.66/1.49  --time_out_virtual                      -1.
% 7.66/1.49  --symbol_type_check                     false
% 7.66/1.49  --clausify_out                          false
% 7.66/1.49  --sig_cnt_out                           false
% 7.66/1.49  --trig_cnt_out                          false
% 7.66/1.49  --trig_cnt_out_tolerance                1.
% 7.66/1.49  --trig_cnt_out_sk_spl                   false
% 7.66/1.49  --abstr_cl_out                          false
% 7.66/1.49  
% 7.66/1.49  ------ Global Options
% 7.66/1.49  
% 7.66/1.49  --schedule                              none
% 7.66/1.49  --add_important_lit                     false
% 7.66/1.49  --prop_solver_per_cl                    1000
% 7.66/1.49  --min_unsat_core                        false
% 7.66/1.49  --soft_assumptions                      false
% 7.66/1.49  --soft_lemma_size                       3
% 7.66/1.49  --prop_impl_unit_size                   0
% 7.66/1.49  --prop_impl_unit                        []
% 7.66/1.49  --share_sel_clauses                     true
% 7.66/1.49  --reset_solvers                         false
% 7.66/1.49  --bc_imp_inh                            [conj_cone]
% 7.66/1.49  --conj_cone_tolerance                   3.
% 7.66/1.49  --extra_neg_conj                        none
% 7.66/1.49  --large_theory_mode                     true
% 7.66/1.49  --prolific_symb_bound                   200
% 7.66/1.49  --lt_threshold                          2000
% 7.66/1.49  --clause_weak_htbl                      true
% 7.66/1.49  --gc_record_bc_elim                     false
% 7.66/1.49  
% 7.66/1.49  ------ Preprocessing Options
% 7.66/1.49  
% 7.66/1.49  --preprocessing_flag                    true
% 7.66/1.49  --time_out_prep_mult                    0.1
% 7.66/1.49  --splitting_mode                        input
% 7.66/1.49  --splitting_grd                         true
% 7.66/1.49  --splitting_cvd                         false
% 7.66/1.49  --splitting_cvd_svl                     false
% 7.66/1.49  --splitting_nvd                         32
% 7.66/1.49  --sub_typing                            true
% 7.66/1.49  --prep_gs_sim                           false
% 7.66/1.49  --prep_unflatten                        true
% 7.66/1.49  --prep_res_sim                          true
% 7.66/1.49  --prep_upred                            true
% 7.66/1.49  --prep_sem_filter                       exhaustive
% 7.66/1.49  --prep_sem_filter_out                   false
% 7.66/1.49  --pred_elim                             false
% 7.66/1.49  --res_sim_input                         true
% 7.66/1.49  --eq_ax_congr_red                       true
% 7.66/1.49  --pure_diseq_elim                       true
% 7.66/1.49  --brand_transform                       false
% 7.66/1.49  --non_eq_to_eq                          false
% 7.66/1.49  --prep_def_merge                        true
% 7.66/1.49  --prep_def_merge_prop_impl              false
% 7.66/1.49  --prep_def_merge_mbd                    true
% 7.66/1.49  --prep_def_merge_tr_red                 false
% 7.66/1.49  --prep_def_merge_tr_cl                  false
% 7.66/1.49  --smt_preprocessing                     true
% 7.66/1.49  --smt_ac_axioms                         fast
% 7.66/1.49  --preprocessed_out                      false
% 7.66/1.49  --preprocessed_stats                    false
% 7.66/1.49  
% 7.66/1.49  ------ Abstraction refinement Options
% 7.66/1.49  
% 7.66/1.49  --abstr_ref                             []
% 7.66/1.49  --abstr_ref_prep                        false
% 7.66/1.49  --abstr_ref_until_sat                   false
% 7.66/1.49  --abstr_ref_sig_restrict                funpre
% 7.66/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.66/1.49  --abstr_ref_under                       []
% 7.66/1.49  
% 7.66/1.49  ------ SAT Options
% 7.66/1.49  
% 7.66/1.49  --sat_mode                              false
% 7.66/1.49  --sat_fm_restart_options                ""
% 7.66/1.49  --sat_gr_def                            false
% 7.66/1.49  --sat_epr_types                         true
% 7.66/1.49  --sat_non_cyclic_types                  false
% 7.66/1.49  --sat_finite_models                     false
% 7.66/1.49  --sat_fm_lemmas                         false
% 7.66/1.49  --sat_fm_prep                           false
% 7.66/1.49  --sat_fm_uc_incr                        true
% 7.66/1.49  --sat_out_model                         small
% 7.66/1.49  --sat_out_clauses                       false
% 7.66/1.49  
% 7.66/1.49  ------ QBF Options
% 7.66/1.49  
% 7.66/1.49  --qbf_mode                              false
% 7.66/1.49  --qbf_elim_univ                         false
% 7.66/1.49  --qbf_dom_inst                          none
% 7.66/1.49  --qbf_dom_pre_inst                      false
% 7.66/1.49  --qbf_sk_in                             false
% 7.66/1.49  --qbf_pred_elim                         true
% 7.66/1.49  --qbf_split                             512
% 7.66/1.49  
% 7.66/1.49  ------ BMC1 Options
% 7.66/1.49  
% 7.66/1.49  --bmc1_incremental                      false
% 7.66/1.49  --bmc1_axioms                           reachable_all
% 7.66/1.49  --bmc1_min_bound                        0
% 7.66/1.49  --bmc1_max_bound                        -1
% 7.66/1.49  --bmc1_max_bound_default                -1
% 7.66/1.49  --bmc1_symbol_reachability              true
% 7.66/1.49  --bmc1_property_lemmas                  false
% 7.66/1.49  --bmc1_k_induction                      false
% 7.66/1.49  --bmc1_non_equiv_states                 false
% 7.66/1.49  --bmc1_deadlock                         false
% 7.66/1.49  --bmc1_ucm                              false
% 7.66/1.49  --bmc1_add_unsat_core                   none
% 7.66/1.49  --bmc1_unsat_core_children              false
% 7.66/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.66/1.49  --bmc1_out_stat                         full
% 7.66/1.49  --bmc1_ground_init                      false
% 7.66/1.49  --bmc1_pre_inst_next_state              false
% 7.66/1.49  --bmc1_pre_inst_state                   false
% 7.66/1.49  --bmc1_pre_inst_reach_state             false
% 7.66/1.49  --bmc1_out_unsat_core                   false
% 7.66/1.49  --bmc1_aig_witness_out                  false
% 7.66/1.49  --bmc1_verbose                          false
% 7.66/1.49  --bmc1_dump_clauses_tptp                false
% 7.66/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.66/1.49  --bmc1_dump_file                        -
% 7.66/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.66/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.66/1.49  --bmc1_ucm_extend_mode                  1
% 7.66/1.49  --bmc1_ucm_init_mode                    2
% 7.66/1.49  --bmc1_ucm_cone_mode                    none
% 7.66/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.66/1.49  --bmc1_ucm_relax_model                  4
% 7.66/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.66/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.66/1.49  --bmc1_ucm_layered_model                none
% 7.66/1.49  --bmc1_ucm_max_lemma_size               10
% 7.66/1.49  
% 7.66/1.49  ------ AIG Options
% 7.66/1.49  
% 7.66/1.49  --aig_mode                              false
% 7.66/1.49  
% 7.66/1.49  ------ Instantiation Options
% 7.66/1.49  
% 7.66/1.49  --instantiation_flag                    true
% 7.66/1.49  --inst_sos_flag                         false
% 7.66/1.49  --inst_sos_phase                        true
% 7.66/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.66/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.66/1.49  --inst_lit_sel_side                     num_symb
% 7.66/1.49  --inst_solver_per_active                1400
% 7.66/1.49  --inst_solver_calls_frac                1.
% 7.66/1.49  --inst_passive_queue_type               priority_queues
% 7.66/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.66/1.49  --inst_passive_queues_freq              [25;2]
% 7.66/1.49  --inst_dismatching                      true
% 7.66/1.49  --inst_eager_unprocessed_to_passive     true
% 7.66/1.49  --inst_prop_sim_given                   true
% 7.66/1.49  --inst_prop_sim_new                     false
% 7.66/1.49  --inst_subs_new                         false
% 7.66/1.49  --inst_eq_res_simp                      false
% 7.66/1.49  --inst_subs_given                       false
% 7.66/1.49  --inst_orphan_elimination               true
% 7.66/1.49  --inst_learning_loop_flag               true
% 7.66/1.49  --inst_learning_start                   3000
% 7.66/1.49  --inst_learning_factor                  2
% 7.66/1.49  --inst_start_prop_sim_after_learn       3
% 7.66/1.49  --inst_sel_renew                        solver
% 7.66/1.49  --inst_lit_activity_flag                true
% 7.66/1.49  --inst_restr_to_given                   false
% 7.66/1.49  --inst_activity_threshold               500
% 7.66/1.49  --inst_out_proof                        true
% 7.66/1.49  
% 7.66/1.49  ------ Resolution Options
% 7.66/1.49  
% 7.66/1.49  --resolution_flag                       true
% 7.66/1.49  --res_lit_sel                           adaptive
% 7.66/1.49  --res_lit_sel_side                      none
% 7.66/1.49  --res_ordering                          kbo
% 7.66/1.49  --res_to_prop_solver                    active
% 7.66/1.49  --res_prop_simpl_new                    false
% 7.66/1.49  --res_prop_simpl_given                  true
% 7.66/1.49  --res_passive_queue_type                priority_queues
% 7.66/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.66/1.49  --res_passive_queues_freq               [15;5]
% 7.66/1.49  --res_forward_subs                      full
% 7.66/1.49  --res_backward_subs                     full
% 7.66/1.49  --res_forward_subs_resolution           true
% 7.66/1.49  --res_backward_subs_resolution          true
% 7.66/1.49  --res_orphan_elimination                true
% 7.66/1.49  --res_time_limit                        2.
% 7.66/1.49  --res_out_proof                         true
% 7.66/1.49  
% 7.66/1.49  ------ Superposition Options
% 7.66/1.49  
% 7.66/1.49  --superposition_flag                    true
% 7.66/1.49  --sup_passive_queue_type                priority_queues
% 7.66/1.49  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.66/1.49  --sup_passive_queues_freq               [1;4]
% 7.66/1.49  --demod_completeness_check              fast
% 7.66/1.49  --demod_use_ground                      true
% 7.66/1.49  --sup_to_prop_solver                    passive
% 7.66/1.49  --sup_prop_simpl_new                    true
% 7.66/1.49  --sup_prop_simpl_given                  true
% 7.66/1.49  --sup_fun_splitting                     false
% 7.66/1.49  --sup_smt_interval                      50000
% 7.66/1.49  
% 7.66/1.49  ------ Superposition Simplification Setup
% 7.66/1.49  
% 7.66/1.49  --sup_indices_passive                   []
% 7.66/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.66/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.66/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.66/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.66/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.66/1.49  --sup_full_bw                           [BwDemod]
% 7.66/1.49  --sup_immed_triv                        [TrivRules]
% 7.66/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.66/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.66/1.49  --sup_immed_bw_main                     []
% 7.66/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.66/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.66/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.66/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.66/1.49  
% 7.66/1.49  ------ Combination Options
% 7.66/1.49  
% 7.66/1.49  --comb_res_mult                         3
% 7.66/1.49  --comb_sup_mult                         2
% 7.66/1.49  --comb_inst_mult                        10
% 7.66/1.49  
% 7.66/1.49  ------ Debug Options
% 7.66/1.49  
% 7.66/1.49  --dbg_backtrace                         false
% 7.66/1.49  --dbg_dump_prop_clauses                 false
% 7.66/1.49  --dbg_dump_prop_clauses_file            -
% 7.66/1.49  --dbg_out_stat                          false
% 7.66/1.49  
% 7.66/1.49  
% 7.66/1.49  
% 7.66/1.49  
% 7.66/1.49  ------ Proving...
% 7.66/1.49  
% 7.66/1.49  
% 7.66/1.49  % SZS status Theorem for theBenchmark.p
% 7.66/1.49  
% 7.66/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.66/1.49  
% 7.66/1.49  fof(f4,axiom,(
% 7.66/1.49    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 7.66/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.66/1.49  
% 7.66/1.49  fof(f11,plain,(
% 7.66/1.49    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 7.66/1.49    inference(ennf_transformation,[],[f4])).
% 7.66/1.49  
% 7.66/1.49  fof(f45,plain,(
% 7.66/1.49    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 7.66/1.49    inference(cnf_transformation,[],[f11])).
% 7.66/1.49  
% 7.66/1.49  fof(f1,axiom,(
% 7.66/1.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 7.66/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.66/1.49  
% 7.66/1.49  fof(f10,plain,(
% 7.66/1.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 7.66/1.49    inference(ennf_transformation,[],[f1])).
% 7.66/1.49  
% 7.66/1.49  fof(f14,plain,(
% 7.66/1.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 7.66/1.49    inference(nnf_transformation,[],[f10])).
% 7.66/1.49  
% 7.66/1.49  fof(f15,plain,(
% 7.66/1.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.66/1.49    inference(rectify,[],[f14])).
% 7.66/1.49  
% 7.66/1.49  fof(f16,plain,(
% 7.66/1.49    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 7.66/1.49    introduced(choice_axiom,[])).
% 7.66/1.49  
% 7.66/1.49  fof(f17,plain,(
% 7.66/1.49    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.66/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f16])).
% 7.66/1.49  
% 7.66/1.49  fof(f33,plain,(
% 7.66/1.49    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 7.66/1.49    inference(cnf_transformation,[],[f17])).
% 7.66/1.49  
% 7.66/1.49  fof(f7,axiom,(
% 7.66/1.49    ! [X0,X1] : (r1_tarski(X0,X1) => r1_tarski(k3_tarski(X0),k3_tarski(X1)))),
% 7.66/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.66/1.49  
% 7.66/1.49  fof(f12,plain,(
% 7.66/1.49    ! [X0,X1] : (r1_tarski(k3_tarski(X0),k3_tarski(X1)) | ~r1_tarski(X0,X1))),
% 7.66/1.49    inference(ennf_transformation,[],[f7])).
% 7.66/1.49  
% 7.66/1.49  fof(f53,plain,(
% 7.66/1.49    ( ! [X0,X1] : (r1_tarski(k3_tarski(X0),k3_tarski(X1)) | ~r1_tarski(X0,X1)) )),
% 7.66/1.49    inference(cnf_transformation,[],[f12])).
% 7.66/1.49  
% 7.66/1.49  fof(f2,axiom,(
% 7.66/1.49    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 7.66/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.66/1.49  
% 7.66/1.49  fof(f18,plain,(
% 7.66/1.49    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 7.66/1.49    inference(nnf_transformation,[],[f2])).
% 7.66/1.49  
% 7.66/1.49  fof(f19,plain,(
% 7.66/1.49    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 7.66/1.49    inference(flattening,[],[f18])).
% 7.66/1.49  
% 7.66/1.49  fof(f20,plain,(
% 7.66/1.49    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 7.66/1.49    inference(rectify,[],[f19])).
% 7.66/1.49  
% 7.66/1.49  fof(f21,plain,(
% 7.66/1.49    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK1(X0,X1,X2),X1) & ~r2_hidden(sK1(X0,X1,X2),X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (r2_hidden(sK1(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 7.66/1.49    introduced(choice_axiom,[])).
% 7.66/1.49  
% 7.66/1.49  fof(f22,plain,(
% 7.66/1.49    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK1(X0,X1,X2),X1) & ~r2_hidden(sK1(X0,X1,X2),X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (r2_hidden(sK1(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 7.66/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f20,f21])).
% 7.66/1.49  
% 7.66/1.49  fof(f39,plain,(
% 7.66/1.49    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | r2_hidden(sK1(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 7.66/1.49    inference(cnf_transformation,[],[f22])).
% 7.66/1.49  
% 7.66/1.49  fof(f8,conjecture,(
% 7.66/1.49    ! [X0,X1] : k2_xboole_0(k3_tarski(X0),k3_tarski(X1)) = k3_tarski(k2_xboole_0(X0,X1))),
% 7.66/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.66/1.49  
% 7.66/1.49  fof(f9,negated_conjecture,(
% 7.66/1.49    ~! [X0,X1] : k2_xboole_0(k3_tarski(X0),k3_tarski(X1)) = k3_tarski(k2_xboole_0(X0,X1))),
% 7.66/1.49    inference(negated_conjecture,[],[f8])).
% 7.66/1.49  
% 7.66/1.49  fof(f13,plain,(
% 7.66/1.49    ? [X0,X1] : k2_xboole_0(k3_tarski(X0),k3_tarski(X1)) != k3_tarski(k2_xboole_0(X0,X1))),
% 7.66/1.49    inference(ennf_transformation,[],[f9])).
% 7.66/1.49  
% 7.66/1.49  fof(f31,plain,(
% 7.66/1.49    ? [X0,X1] : k2_xboole_0(k3_tarski(X0),k3_tarski(X1)) != k3_tarski(k2_xboole_0(X0,X1)) => k2_xboole_0(k3_tarski(sK5),k3_tarski(sK6)) != k3_tarski(k2_xboole_0(sK5,sK6))),
% 7.66/1.49    introduced(choice_axiom,[])).
% 7.66/1.49  
% 7.66/1.49  fof(f32,plain,(
% 7.66/1.49    k2_xboole_0(k3_tarski(sK5),k3_tarski(sK6)) != k3_tarski(k2_xboole_0(sK5,sK6))),
% 7.66/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f13,f31])).
% 7.66/1.49  
% 7.66/1.49  fof(f54,plain,(
% 7.66/1.49    k2_xboole_0(k3_tarski(sK5),k3_tarski(sK6)) != k3_tarski(k2_xboole_0(sK5,sK6))),
% 7.66/1.49    inference(cnf_transformation,[],[f32])).
% 7.66/1.49  
% 7.66/1.49  fof(f6,axiom,(
% 7.66/1.49    ! [X0,X1] : (k3_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3))))),
% 7.66/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.66/1.49  
% 7.66/1.49  fof(f25,plain,(
% 7.66/1.49    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3))) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | ~r2_hidden(X2,X1))) | k3_tarski(X0) != X1))),
% 7.66/1.49    inference(nnf_transformation,[],[f6])).
% 7.66/1.49  
% 7.66/1.49  fof(f26,plain,(
% 7.66/1.49    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 7.66/1.49    inference(rectify,[],[f25])).
% 7.66/1.49  
% 7.66/1.49  fof(f29,plain,(
% 7.66/1.49    ! [X5,X0] : (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) => (r2_hidden(sK4(X0,X5),X0) & r2_hidden(X5,sK4(X0,X5))))),
% 7.66/1.49    introduced(choice_axiom,[])).
% 7.66/1.49  
% 7.66/1.49  fof(f28,plain,(
% 7.66/1.49    ( ! [X2] : (! [X1,X0] : (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) => (r2_hidden(sK3(X0,X1),X0) & r2_hidden(X2,sK3(X0,X1))))) )),
% 7.66/1.49    introduced(choice_axiom,[])).
% 7.66/1.49  
% 7.66/1.49  fof(f27,plain,(
% 7.66/1.49    ! [X1,X0] : (? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1))) => ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK2(X0,X1),X3)) | ~r2_hidden(sK2(X0,X1),X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(sK2(X0,X1),X4)) | r2_hidden(sK2(X0,X1),X1))))),
% 7.66/1.49    introduced(choice_axiom,[])).
% 7.66/1.49  
% 7.66/1.49  fof(f30,plain,(
% 7.66/1.49    ! [X0,X1] : ((k3_tarski(X0) = X1 | ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK2(X0,X1),X3)) | ~r2_hidden(sK2(X0,X1),X1)) & ((r2_hidden(sK3(X0,X1),X0) & r2_hidden(sK2(X0,X1),sK3(X0,X1))) | r2_hidden(sK2(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & ((r2_hidden(sK4(X0,X5),X0) & r2_hidden(X5,sK4(X0,X5))) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 7.66/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f26,f29,f28,f27])).
% 7.66/1.49  
% 7.66/1.49  fof(f48,plain,(
% 7.66/1.49    ( ! [X0,X5,X1] : (r2_hidden(sK4(X0,X5),X0) | ~r2_hidden(X5,X1) | k3_tarski(X0) != X1) )),
% 7.66/1.49    inference(cnf_transformation,[],[f30])).
% 7.66/1.49  
% 7.66/1.49  fof(f61,plain,(
% 7.66/1.49    ( ! [X0,X5] : (r2_hidden(sK4(X0,X5),X0) | ~r2_hidden(X5,k3_tarski(X0))) )),
% 7.66/1.49    inference(equality_resolution,[],[f48])).
% 7.66/1.49  
% 7.66/1.49  fof(f47,plain,(
% 7.66/1.49    ( ! [X0,X5,X1] : (r2_hidden(X5,sK4(X0,X5)) | ~r2_hidden(X5,X1) | k3_tarski(X0) != X1) )),
% 7.66/1.49    inference(cnf_transformation,[],[f30])).
% 7.66/1.49  
% 7.66/1.49  fof(f62,plain,(
% 7.66/1.49    ( ! [X0,X5] : (r2_hidden(X5,sK4(X0,X5)) | ~r2_hidden(X5,k3_tarski(X0))) )),
% 7.66/1.49    inference(equality_resolution,[],[f47])).
% 7.66/1.49  
% 7.66/1.49  fof(f37,plain,(
% 7.66/1.49    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k2_xboole_0(X0,X1) != X2) )),
% 7.66/1.49    inference(cnf_transformation,[],[f22])).
% 7.66/1.49  
% 7.66/1.49  fof(f56,plain,(
% 7.66/1.49    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X0)) )),
% 7.66/1.49    inference(equality_resolution,[],[f37])).
% 7.66/1.49  
% 7.66/1.49  fof(f49,plain,(
% 7.66/1.49    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(X6,X0) | ~r2_hidden(X5,X6) | k3_tarski(X0) != X1) )),
% 7.66/1.49    inference(cnf_transformation,[],[f30])).
% 7.66/1.49  
% 7.66/1.49  fof(f60,plain,(
% 7.66/1.49    ( ! [X6,X0,X5] : (r2_hidden(X5,k3_tarski(X0)) | ~r2_hidden(X6,X0) | ~r2_hidden(X5,X6)) )),
% 7.66/1.49    inference(equality_resolution,[],[f49])).
% 7.66/1.49  
% 7.66/1.49  fof(f40,plain,(
% 7.66/1.49    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) )),
% 7.66/1.49    inference(cnf_transformation,[],[f22])).
% 7.66/1.49  
% 7.66/1.49  fof(f36,plain,(
% 7.66/1.49    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k2_xboole_0(X0,X1) != X2) )),
% 7.66/1.49    inference(cnf_transformation,[],[f22])).
% 7.66/1.49  
% 7.66/1.49  fof(f57,plain,(
% 7.66/1.49    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,k2_xboole_0(X0,X1))) )),
% 7.66/1.49    inference(equality_resolution,[],[f36])).
% 7.66/1.49  
% 7.66/1.49  fof(f3,axiom,(
% 7.66/1.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.66/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.66/1.49  
% 7.66/1.49  fof(f23,plain,(
% 7.66/1.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.66/1.49    inference(nnf_transformation,[],[f3])).
% 7.66/1.49  
% 7.66/1.49  fof(f24,plain,(
% 7.66/1.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.66/1.49    inference(flattening,[],[f23])).
% 7.66/1.49  
% 7.66/1.49  fof(f42,plain,(
% 7.66/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 7.66/1.49    inference(cnf_transformation,[],[f24])).
% 7.66/1.49  
% 7.66/1.49  fof(f59,plain,(
% 7.66/1.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.66/1.49    inference(equality_resolution,[],[f42])).
% 7.66/1.49  
% 7.66/1.49  fof(f41,plain,(
% 7.66/1.49    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | ~r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X2)) )),
% 7.66/1.49    inference(cnf_transformation,[],[f22])).
% 7.66/1.49  
% 7.66/1.49  cnf(c_12,plain,
% 7.66/1.49      ( ~ r1_tarski(X0,X1) | r1_tarski(X0,k2_xboole_0(X2,X1)) ),
% 7.66/1.49      inference(cnf_transformation,[],[f45]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_5658,plain,
% 7.66/1.49      ( r1_tarski(X0,k2_xboole_0(sK5,sK6)) | ~ r1_tarski(X0,sK6) ),
% 7.66/1.49      inference(instantiation,[status(thm)],[c_12]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_21100,plain,
% 7.66/1.49      ( r1_tarski(sK6,k2_xboole_0(sK5,sK6)) | ~ r1_tarski(sK6,sK6) ),
% 7.66/1.49      inference(instantiation,[status(thm)],[c_5658]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_2,plain,
% 7.66/1.49      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 7.66/1.49      inference(cnf_transformation,[],[f33]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_935,plain,
% 7.66/1.49      ( r2_hidden(sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6))),X0)
% 7.66/1.49      | ~ r2_hidden(sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6))),k3_tarski(sK6))
% 7.66/1.49      | ~ r1_tarski(k3_tarski(sK6),X0) ),
% 7.66/1.49      inference(instantiation,[status(thm)],[c_2]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_1906,plain,
% 7.66/1.49      ( r2_hidden(sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6))),k3_tarski(X0))
% 7.66/1.49      | ~ r2_hidden(sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6))),k3_tarski(sK6))
% 7.66/1.49      | ~ r1_tarski(k3_tarski(sK6),k3_tarski(X0)) ),
% 7.66/1.49      inference(instantiation,[status(thm)],[c_935]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_13277,plain,
% 7.66/1.49      ( r2_hidden(sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6))),k3_tarski(k2_xboole_0(sK5,sK6)))
% 7.66/1.49      | ~ r2_hidden(sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6))),k3_tarski(sK6))
% 7.66/1.49      | ~ r1_tarski(k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6))) ),
% 7.66/1.49      inference(instantiation,[status(thm)],[c_1906]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_20,plain,
% 7.66/1.49      ( ~ r1_tarski(X0,X1) | r1_tarski(k3_tarski(X0),k3_tarski(X1)) ),
% 7.66/1.49      inference(cnf_transformation,[],[f53]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_2051,plain,
% 7.66/1.49      ( ~ r1_tarski(X0,k2_xboole_0(sK5,sK6))
% 7.66/1.49      | r1_tarski(k3_tarski(X0),k3_tarski(k2_xboole_0(sK5,sK6))) ),
% 7.66/1.49      inference(instantiation,[status(thm)],[c_20]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_13276,plain,
% 7.66/1.49      ( r1_tarski(k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6)))
% 7.66/1.49      | ~ r1_tarski(sK6,k2_xboole_0(sK5,sK6)) ),
% 7.66/1.49      inference(instantiation,[status(thm)],[c_2051]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_5,plain,
% 7.66/1.49      ( r2_hidden(sK1(X0,X1,X2),X1)
% 7.66/1.49      | r2_hidden(sK1(X0,X1,X2),X2)
% 7.66/1.49      | r2_hidden(sK1(X0,X1,X2),X0)
% 7.66/1.49      | k2_xboole_0(X0,X1) = X2 ),
% 7.66/1.49      inference(cnf_transformation,[],[f39]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_21,negated_conjecture,
% 7.66/1.49      ( k2_xboole_0(k3_tarski(sK5),k3_tarski(sK6)) != k3_tarski(k2_xboole_0(sK5,sK6)) ),
% 7.66/1.49      inference(cnf_transformation,[],[f54]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_5954,plain,
% 7.66/1.49      ( r2_hidden(sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6))),k3_tarski(k2_xboole_0(sK5,sK6)))
% 7.66/1.49      | r2_hidden(sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6))),k3_tarski(sK6))
% 7.66/1.49      | r2_hidden(sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6))),k3_tarski(sK5)) ),
% 7.66/1.49      inference(resolution,[status(thm)],[c_5,c_21]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_813,plain,
% 7.66/1.49      ( r2_hidden(sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6))),k3_tarski(k2_xboole_0(sK5,sK6)))
% 7.66/1.49      | r2_hidden(sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6))),k3_tarski(sK6))
% 7.66/1.49      | r2_hidden(sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6))),k3_tarski(sK5))
% 7.66/1.49      | k2_xboole_0(k3_tarski(sK5),k3_tarski(sK6)) = k3_tarski(k2_xboole_0(sK5,sK6)) ),
% 7.66/1.49      inference(instantiation,[status(thm)],[c_5]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_18,plain,
% 7.66/1.49      ( ~ r2_hidden(X0,k3_tarski(X1)) | r2_hidden(sK4(X1,X0),X1) ),
% 7.66/1.49      inference(cnf_transformation,[],[f61]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_1073,plain,
% 7.66/1.49      ( ~ r2_hidden(sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6))),k3_tarski(sK5))
% 7.66/1.49      | r2_hidden(sK4(sK5,sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6)))),sK5) ),
% 7.66/1.49      inference(instantiation,[status(thm)],[c_18]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_19,plain,
% 7.66/1.49      ( r2_hidden(X0,sK4(X1,X0)) | ~ r2_hidden(X0,k3_tarski(X1)) ),
% 7.66/1.49      inference(cnf_transformation,[],[f62]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_1072,plain,
% 7.66/1.49      ( r2_hidden(sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6))),sK4(sK5,sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6)))))
% 7.66/1.49      | ~ r2_hidden(sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6))),k3_tarski(sK5)) ),
% 7.66/1.49      inference(instantiation,[status(thm)],[c_19]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_7,plain,
% 7.66/1.49      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,k2_xboole_0(X1,X2)) ),
% 7.66/1.49      inference(cnf_transformation,[],[f56]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_1372,plain,
% 7.66/1.49      ( r2_hidden(sK4(sK5,sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6)))),k2_xboole_0(sK5,X0))
% 7.66/1.49      | ~ r2_hidden(sK4(sK5,sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6)))),sK5) ),
% 7.66/1.49      inference(instantiation,[status(thm)],[c_7]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_4492,plain,
% 7.66/1.49      ( r2_hidden(sK4(sK5,sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6)))),k2_xboole_0(sK5,sK6))
% 7.66/1.49      | ~ r2_hidden(sK4(sK5,sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6)))),sK5) ),
% 7.66/1.49      inference(instantiation,[status(thm)],[c_1372]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_17,plain,
% 7.66/1.49      ( ~ r2_hidden(X0,X1)
% 7.66/1.49      | ~ r2_hidden(X2,X0)
% 7.66/1.49      | r2_hidden(X2,k3_tarski(X1)) ),
% 7.66/1.49      inference(cnf_transformation,[],[f60]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_1340,plain,
% 7.66/1.49      ( ~ r2_hidden(sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6))),sK4(sK5,sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6)))))
% 7.66/1.49      | r2_hidden(sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6))),k3_tarski(X0))
% 7.66/1.49      | ~ r2_hidden(sK4(sK5,sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6)))),X0) ),
% 7.66/1.49      inference(instantiation,[status(thm)],[c_17]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_4819,plain,
% 7.66/1.49      ( ~ r2_hidden(sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6))),sK4(sK5,sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6)))))
% 7.66/1.49      | r2_hidden(sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6))),k3_tarski(k2_xboole_0(sK5,sK6)))
% 7.66/1.49      | ~ r2_hidden(sK4(sK5,sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6)))),k2_xboole_0(sK5,sK6)) ),
% 7.66/1.49      inference(instantiation,[status(thm)],[c_1340]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_6589,plain,
% 7.66/1.49      ( r2_hidden(sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6))),k3_tarski(sK6))
% 7.66/1.49      | r2_hidden(sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6))),k3_tarski(k2_xboole_0(sK5,sK6))) ),
% 7.66/1.49      inference(global_propositional_subsumption,
% 7.66/1.49                [status(thm)],
% 7.66/1.49                [c_5954,c_21,c_813,c_1073,c_1072,c_4492,c_4819]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_6590,plain,
% 7.66/1.49      ( r2_hidden(sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6))),k3_tarski(k2_xboole_0(sK5,sK6)))
% 7.66/1.49      | r2_hidden(sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6))),k3_tarski(sK6)) ),
% 7.66/1.49      inference(renaming,[status(thm)],[c_6589]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_2361,plain,
% 7.66/1.49      ( ~ r2_hidden(X0,k3_tarski(X1))
% 7.66/1.49      | r2_hidden(X0,k3_tarski(X2))
% 7.66/1.49      | ~ r1_tarski(X1,X2) ),
% 7.66/1.49      inference(resolution,[status(thm)],[c_2,c_20]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_6785,plain,
% 7.66/1.49      ( r2_hidden(sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6))),k3_tarski(X0))
% 7.66/1.49      | r2_hidden(sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6))),k3_tarski(sK6))
% 7.66/1.49      | ~ r1_tarski(k2_xboole_0(sK5,sK6),X0) ),
% 7.66/1.49      inference(resolution,[status(thm)],[c_6590,c_2361]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_6850,plain,
% 7.66/1.49      ( r2_hidden(sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6))),k3_tarski(sK6))
% 7.66/1.49      | ~ r1_tarski(k2_xboole_0(sK5,sK6),sK6) ),
% 7.66/1.49      inference(factoring,[status(thm)],[c_6785]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_856,plain,
% 7.66/1.49      ( ~ r2_hidden(sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6))),k3_tarski(k2_xboole_0(sK5,sK6)))
% 7.66/1.49      | r2_hidden(sK4(k2_xboole_0(sK5,sK6),sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6)))),k2_xboole_0(sK5,sK6)) ),
% 7.66/1.49      inference(instantiation,[status(thm)],[c_18]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_855,plain,
% 7.66/1.49      ( r2_hidden(sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6))),sK4(k2_xboole_0(sK5,sK6),sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6)))))
% 7.66/1.49      | ~ r2_hidden(sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6))),k3_tarski(k2_xboole_0(sK5,sK6))) ),
% 7.66/1.49      inference(instantiation,[status(thm)],[c_19]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_4,plain,
% 7.66/1.49      ( ~ r2_hidden(sK1(X0,X1,X2),X2)
% 7.66/1.49      | ~ r2_hidden(sK1(X0,X1,X2),X0)
% 7.66/1.49      | k2_xboole_0(X0,X1) = X2 ),
% 7.66/1.49      inference(cnf_transformation,[],[f40]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_1069,plain,
% 7.66/1.49      ( ~ r2_hidden(sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6))),k3_tarski(k2_xboole_0(sK5,sK6)))
% 7.66/1.49      | ~ r2_hidden(sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6))),k3_tarski(sK5))
% 7.66/1.49      | k2_xboole_0(k3_tarski(sK5),k3_tarski(sK6)) = k3_tarski(k2_xboole_0(sK5,sK6)) ),
% 7.66/1.49      inference(instantiation,[status(thm)],[c_4]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_1547,plain,
% 7.66/1.49      ( ~ r2_hidden(sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6))),sK4(k2_xboole_0(sK5,sK6),sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6)))))
% 7.66/1.49      | r2_hidden(sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6))),k3_tarski(X0))
% 7.66/1.49      | ~ r2_hidden(sK4(k2_xboole_0(sK5,sK6),sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6)))),X0) ),
% 7.66/1.49      inference(instantiation,[status(thm)],[c_17]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_1549,plain,
% 7.66/1.49      ( ~ r2_hidden(sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6))),sK4(k2_xboole_0(sK5,sK6),sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6)))))
% 7.66/1.49      | r2_hidden(sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6))),k3_tarski(sK5))
% 7.66/1.49      | ~ r2_hidden(sK4(k2_xboole_0(sK5,sK6),sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6)))),sK5) ),
% 7.66/1.49      inference(instantiation,[status(thm)],[c_1547]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_8,plain,
% 7.66/1.49      ( r2_hidden(X0,X1)
% 7.66/1.49      | r2_hidden(X0,X2)
% 7.66/1.49      | ~ r2_hidden(X0,k2_xboole_0(X2,X1)) ),
% 7.66/1.49      inference(cnf_transformation,[],[f57]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_1597,plain,
% 7.66/1.49      ( ~ r2_hidden(sK4(k2_xboole_0(sK5,sK6),sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6)))),k2_xboole_0(sK5,sK6))
% 7.66/1.49      | r2_hidden(sK4(k2_xboole_0(sK5,sK6),sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6)))),sK6)
% 7.66/1.49      | r2_hidden(sK4(k2_xboole_0(sK5,sK6),sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6)))),sK5) ),
% 7.66/1.49      inference(instantiation,[status(thm)],[c_8]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_7894,plain,
% 7.66/1.49      ( ~ r2_hidden(sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6))),sK4(k2_xboole_0(sK5,sK6),sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6)))))
% 7.66/1.49      | r2_hidden(sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6))),k3_tarski(sK6))
% 7.66/1.49      | ~ r2_hidden(sK4(k2_xboole_0(sK5,sK6),sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6)))),sK6) ),
% 7.66/1.49      inference(instantiation,[status(thm)],[c_1547]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_8031,plain,
% 7.66/1.49      ( r2_hidden(sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6))),k3_tarski(sK6)) ),
% 7.66/1.49      inference(global_propositional_subsumption,
% 7.66/1.49                [status(thm)],
% 7.66/1.49                [c_6850,c_21,c_856,c_855,c_1069,c_1549,c_1597,c_6590,
% 7.66/1.49                 c_7894]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_11,plain,
% 7.66/1.49      ( r1_tarski(X0,X0) ),
% 7.66/1.49      inference(cnf_transformation,[],[f59]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_5591,plain,
% 7.66/1.49      ( r1_tarski(sK6,sK6) ),
% 7.66/1.49      inference(instantiation,[status(thm)],[c_11]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_3,plain,
% 7.66/1.49      ( ~ r2_hidden(sK1(X0,X1,X2),X1)
% 7.66/1.49      | ~ r2_hidden(sK1(X0,X1,X2),X2)
% 7.66/1.49      | k2_xboole_0(X0,X1) = X2 ),
% 7.66/1.49      inference(cnf_transformation,[],[f41]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_852,plain,
% 7.66/1.49      ( ~ r2_hidden(sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6))),k3_tarski(k2_xboole_0(sK5,sK6)))
% 7.66/1.49      | ~ r2_hidden(sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6))),k3_tarski(sK6))
% 7.66/1.49      | k2_xboole_0(k3_tarski(sK5),k3_tarski(sK6)) = k3_tarski(k2_xboole_0(sK5,sK6)) ),
% 7.66/1.49      inference(instantiation,[status(thm)],[c_3]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(contradiction,plain,
% 7.66/1.49      ( $false ),
% 7.66/1.49      inference(minisat,
% 7.66/1.49                [status(thm)],
% 7.66/1.49                [c_21100,c_13277,c_13276,c_8031,c_5591,c_852,c_21]) ).
% 7.66/1.49  
% 7.66/1.49  
% 7.66/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.66/1.49  
% 7.66/1.49  ------                               Statistics
% 7.66/1.49  
% 7.66/1.49  ------ Selected
% 7.66/1.49  
% 7.66/1.49  total_time:                             0.715
% 7.66/1.49  
%------------------------------------------------------------------------------
