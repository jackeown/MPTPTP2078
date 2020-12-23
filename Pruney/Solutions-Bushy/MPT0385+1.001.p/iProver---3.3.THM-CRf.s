%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0385+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:10 EST 2020

% Result     : Theorem 11.21s
% Output     : CNFRefutation 11.21s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 129 expanded)
%              Number of clauses        :   44 (  48 expanded)
%              Number of leaves         :   18 (  34 expanded)
%              Depth                    :   11
%              Number of atoms          :  351 ( 640 expanded)
%              Number of equality atoms :   82 ( 151 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = X0
       => ( k1_setfam_1(X0) = X1
        <=> k1_xboole_0 = X1 ) )
      & ( k1_xboole_0 != X0
       => ( k1_setfam_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ! [X3] :
                  ( r2_hidden(X3,X0)
                 => r2_hidden(X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( ( k1_setfam_1(X0) = X1
        <=> k1_xboole_0 = X1 )
        | k1_xboole_0 != X0 )
      & ( ( k1_setfam_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ! [X3] :
                  ( r2_hidden(X2,X3)
                  | ~ r2_hidden(X3,X0) ) ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( ( ( k1_setfam_1(X0) = X1
            | k1_xboole_0 != X1 )
          & ( k1_xboole_0 = X1
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 != X0 )
      & ( ( ( k1_setfam_1(X0) = X1
            | ? [X2] :
                ( ( ? [X3] :
                      ( ~ r2_hidden(X2,X3)
                      & r2_hidden(X3,X0) )
                  | ~ r2_hidden(X2,X1) )
                & ( ! [X3] :
                      ( r2_hidden(X2,X3)
                      | ~ r2_hidden(X3,X0) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X2] :
                ( ( r2_hidden(X2,X1)
                  | ? [X3] :
                      ( ~ r2_hidden(X2,X3)
                      & r2_hidden(X3,X0) ) )
                & ( ! [X3] :
                      ( r2_hidden(X2,X3)
                      | ~ r2_hidden(X3,X0) )
                  | ~ r2_hidden(X2,X1) ) )
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( ( ( k1_setfam_1(X0) = X1
            | k1_xboole_0 != X1 )
          & ( k1_xboole_0 = X1
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 != X0 )
      & ( ( ( k1_setfam_1(X0) = X1
            | ? [X2] :
                ( ( ? [X3] :
                      ( ~ r2_hidden(X2,X3)
                      & r2_hidden(X3,X0) )
                  | ~ r2_hidden(X2,X1) )
                & ( ! [X4] :
                      ( r2_hidden(X2,X4)
                      | ~ r2_hidden(X4,X0) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ? [X6] :
                      ( ~ r2_hidden(X5,X6)
                      & r2_hidden(X6,X0) ) )
                & ( ! [X7] :
                      ( r2_hidden(X5,X7)
                      | ~ r2_hidden(X7,X0) )
                  | ~ r2_hidden(X5,X1) ) )
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(rectify,[],[f12])).

fof(f16,plain,(
    ! [X5,X0] :
      ( ? [X6] :
          ( ~ r2_hidden(X5,X6)
          & r2_hidden(X6,X0) )
     => ( ~ r2_hidden(X5,sK2(X0,X5))
        & r2_hidden(sK2(X0,X5),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X2,X3)
          & r2_hidden(X3,X0) )
     => ( ~ r2_hidden(X2,sK1(X0,X1))
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ? [X3] :
                ( ~ r2_hidden(X2,X3)
                & r2_hidden(X3,X0) )
            | ~ r2_hidden(X2,X1) )
          & ( ! [X4] :
                ( r2_hidden(X2,X4)
                | ~ r2_hidden(X4,X0) )
            | r2_hidden(X2,X1) ) )
     => ( ( ? [X3] :
              ( ~ r2_hidden(sK0(X0,X1),X3)
              & r2_hidden(X3,X0) )
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( ! [X4] :
              ( r2_hidden(sK0(X0,X1),X4)
              | ~ r2_hidden(X4,X0) )
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( ( ( k1_setfam_1(X0) = X1
            | k1_xboole_0 != X1 )
          & ( k1_xboole_0 = X1
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 != X0 )
      & ( ( ( k1_setfam_1(X0) = X1
            | ( ( ( ~ r2_hidden(sK0(X0,X1),sK1(X0,X1))
                  & r2_hidden(sK1(X0,X1),X0) )
                | ~ r2_hidden(sK0(X0,X1),X1) )
              & ( ! [X4] :
                    ( r2_hidden(sK0(X0,X1),X4)
                    | ~ r2_hidden(X4,X0) )
                | r2_hidden(sK0(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ( ~ r2_hidden(X5,sK2(X0,X5))
                    & r2_hidden(sK2(X0,X5),X0) ) )
                & ( ! [X7] :
                      ( r2_hidden(X5,X7)
                      | ~ r2_hidden(X7,X0) )
                  | ~ r2_hidden(X5,X1) ) )
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f16,f15,f14])).

fof(f31,plain,(
    ! [X0,X7,X5,X1] :
      ( r2_hidden(X5,X7)
      | ~ r2_hidden(X7,X0)
      | ~ r2_hidden(X5,X1)
      | k1_setfam_1(X0) != X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f56,plain,(
    ! [X0,X7,X5] :
      ( r2_hidden(X5,X7)
      | ~ r2_hidden(X7,X0)
      | ~ r2_hidden(X5,k1_setfam_1(X0))
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f31])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
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
    inference(nnf_transformation,[],[f4])).

fof(f23,plain,(
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
    inference(rectify,[],[f22])).

fof(f26,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( r2_hidden(X7,X0)
          & r2_hidden(X5,X7) )
     => ( r2_hidden(sK6(X0,X5),X0)
        & r2_hidden(X5,sK6(X0,X5)) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X0)
          & r2_hidden(X2,X4) )
     => ( r2_hidden(sK5(X0,X1),X0)
        & r2_hidden(X2,sK5(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
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
              | ~ r2_hidden(sK4(X0,X1),X3) )
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( ? [X4] :
              ( r2_hidden(X4,X0)
              & r2_hidden(sK4(X0,X1),X4) )
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(sK4(X0,X1),X3) )
            | ~ r2_hidden(sK4(X0,X1),X1) )
          & ( ( r2_hidden(sK5(X0,X1),X0)
              & r2_hidden(sK4(X0,X1),sK5(X0,X1)) )
            | r2_hidden(sK4(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ( r2_hidden(sK6(X0,X5),X0)
                & r2_hidden(X5,sK6(X0,X5)) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f23,f26,f25,f24])).

fof(f44,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(X6,X0)
      | ~ r2_hidden(X5,X6)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f57,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k3_tarski(X0))
      | ~ r2_hidden(X6,X0)
      | ~ r2_hidden(X5,X6) ) ),
    inference(equality_resolution,[],[f44])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f32,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | r2_hidden(sK2(X0,X5),X0)
      | k1_setfam_1(X0) != X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f55,plain,(
    ! [X0,X5] :
      ( r2_hidden(X5,k1_setfam_1(X0))
      | r2_hidden(sK2(X0,X5),X0)
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f32])).

fof(f3,axiom,(
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
    inference(ennf_transformation,[],[f3])).

fof(f18,plain,(
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

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f18])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f19,f20])).

fof(f39,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(X0) = X1
      | k1_xboole_0 != X1
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f50,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_setfam_1(X0)
      | k1_xboole_0 != X0 ) ),
    inference(equality_resolution,[],[f38])).

fof(f51,plain,(
    k1_xboole_0 = k1_setfam_1(k1_xboole_0) ),
    inference(equality_resolution,[],[f50])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f6,conjecture,(
    ! [X0] : r1_tarski(k1_setfam_1(X0),k3_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0] : r1_tarski(k1_setfam_1(X0),k3_tarski(X0)) ),
    inference(negated_conjecture,[],[f6])).

fof(f11,plain,(
    ? [X0] : ~ r1_tarski(k1_setfam_1(X0),k3_tarski(X0)) ),
    inference(ennf_transformation,[],[f7])).

fof(f28,plain,
    ( ? [X0] : ~ r1_tarski(k1_setfam_1(X0),k3_tarski(X0))
   => ~ r1_tarski(k1_setfam_1(sK7),k3_tarski(sK7)) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ~ r1_tarski(k1_setfam_1(sK7),k3_tarski(sK7)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f11,f28])).

fof(f49,plain,(
    ~ r1_tarski(k1_setfam_1(sK7),k3_tarski(sK7)) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X0)
    | ~ r2_hidden(X2,k1_setfam_1(X1))
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_758,plain,
    ( ~ r2_hidden(X0,sK7)
    | r2_hidden(sK3(k1_setfam_1(sK7),k3_tarski(sK7)),X0)
    | ~ r2_hidden(sK3(k1_setfam_1(sK7),k3_tarski(sK7)),k1_setfam_1(sK7))
    | k1_xboole_0 = sK7 ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_42941,plain,
    ( r2_hidden(sK3(k1_setfam_1(sK7),k3_tarski(sK7)),sK2(sK7,k1_setfam_1(sK7)))
    | ~ r2_hidden(sK3(k1_setfam_1(sK7),k3_tarski(sK7)),k1_setfam_1(sK7))
    | ~ r2_hidden(sK2(sK7,k1_setfam_1(sK7)),sK7)
    | k1_xboole_0 = sK7 ),
    inference(instantiation,[status(thm)],[c_758])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,k3_tarski(X1)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1080,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(sK3(k1_setfam_1(sK7),k3_tarski(sK7)),X0)
    | r2_hidden(sK3(k1_setfam_1(sK7),k3_tarski(sK7)),k3_tarski(X1)) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_42888,plain,
    ( ~ r2_hidden(sK3(k1_setfam_1(sK7),k3_tarski(sK7)),sK2(sK7,k1_setfam_1(sK7)))
    | r2_hidden(sK3(k1_setfam_1(sK7),k3_tarski(sK7)),k3_tarski(sK7))
    | ~ r2_hidden(sK2(sK7,k1_setfam_1(sK7)),sK7) ),
    inference(instantiation,[status(thm)],[c_1080])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_7651,plain,
    ( ~ r2_hidden(X0,k1_setfam_1(sK7))
    | ~ r2_hidden(k1_setfam_1(sK7),X0) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_31073,plain,
    ( ~ r2_hidden(k1_setfam_1(sK7),k1_setfam_1(sK7)) ),
    inference(instantiation,[status(thm)],[c_7651])).

cnf(c_7,plain,
    ( r2_hidden(X0,k1_setfam_1(X1))
    | r2_hidden(sK2(X1,X0),X1)
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_9824,plain,
    ( r2_hidden(X0,k1_setfam_1(sK7))
    | r2_hidden(sK2(sK7,X0),sK7)
    | k1_xboole_0 = sK7 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_31071,plain,
    ( r2_hidden(sK2(sK7,k1_setfam_1(sK7)),sK7)
    | r2_hidden(k1_setfam_1(sK7),k1_setfam_1(sK7))
    | k1_xboole_0 = sK7 ),
    inference(instantiation,[status(thm)],[c_9824])).

cnf(c_11,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1081,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(sK3(k1_setfam_1(sK7),k3_tarski(sK7)),X0)
    | r2_hidden(sK3(k1_setfam_1(sK7),k3_tarski(sK7)),X1) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_8159,plain,
    ( ~ r1_tarski(k1_setfam_1(X0),X1)
    | r2_hidden(sK3(k1_setfam_1(sK7),k3_tarski(sK7)),X1)
    | ~ r2_hidden(sK3(k1_setfam_1(sK7),k3_tarski(sK7)),k1_setfam_1(X0)) ),
    inference(instantiation,[status(thm)],[c_1081])).

cnf(c_8161,plain,
    ( ~ r1_tarski(k1_setfam_1(k1_xboole_0),k1_xboole_0)
    | ~ r2_hidden(sK3(k1_setfam_1(sK7),k3_tarski(sK7)),k1_setfam_1(k1_xboole_0))
    | r2_hidden(sK3(k1_setfam_1(sK7),k3_tarski(sK7)),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_8159])).

cnf(c_2167,plain,
    ( ~ r1_tarski(X0,k3_tarski(X1))
    | ~ r2_hidden(sK3(k1_setfam_1(sK7),k3_tarski(sK7)),X0)
    | r2_hidden(sK3(k1_setfam_1(sK7),k3_tarski(sK7)),k3_tarski(X1)) ),
    inference(instantiation,[status(thm)],[c_1081])).

cnf(c_5689,plain,
    ( ~ r1_tarski(X0,k3_tarski(sK7))
    | ~ r2_hidden(sK3(k1_setfam_1(sK7),k3_tarski(sK7)),X0)
    | r2_hidden(sK3(k1_setfam_1(sK7),k3_tarski(sK7)),k3_tarski(sK7)) ),
    inference(instantiation,[status(thm)],[c_2167])).

cnf(c_5691,plain,
    ( ~ r1_tarski(k1_xboole_0,k3_tarski(sK7))
    | r2_hidden(sK3(k1_setfam_1(sK7),k3_tarski(sK7)),k3_tarski(sK7))
    | ~ r2_hidden(sK3(k1_setfam_1(sK7),k3_tarski(sK7)),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_5689])).

cnf(c_255,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_251,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2867,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_255,c_251])).

cnf(c_1,plain,
    ( k1_setfam_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_5578,plain,
    ( r1_tarski(k1_setfam_1(k1_xboole_0),X0)
    | ~ r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[status(thm)],[c_2867,c_1])).

cnf(c_5580,plain,
    ( r1_tarski(k1_setfam_1(k1_xboole_0),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_5578])).

cnf(c_18,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1030,plain,
    ( r1_tarski(k1_xboole_0,k3_tarski(X0)) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_3217,plain,
    ( r1_tarski(k1_xboole_0,k3_tarski(sK7)) ),
    inference(instantiation,[status(thm)],[c_1030])).

cnf(c_253,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_750,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK3(k1_setfam_1(sK7),k3_tarski(sK7)),k1_setfam_1(sK7))
    | X0 != sK3(k1_setfam_1(sK7),k3_tarski(sK7))
    | X1 != k1_setfam_1(sK7) ),
    inference(instantiation,[status(thm)],[c_253])).

cnf(c_901,plain,
    ( r2_hidden(sK3(k1_setfam_1(sK7),k3_tarski(sK7)),X0)
    | ~ r2_hidden(sK3(k1_setfam_1(sK7),k3_tarski(sK7)),k1_setfam_1(sK7))
    | X0 != k1_setfam_1(sK7)
    | sK3(k1_setfam_1(sK7),k3_tarski(sK7)) != sK3(k1_setfam_1(sK7),k3_tarski(sK7)) ),
    inference(instantiation,[status(thm)],[c_750])).

cnf(c_2410,plain,
    ( r2_hidden(sK3(k1_setfam_1(sK7),k3_tarski(sK7)),k1_setfam_1(X0))
    | ~ r2_hidden(sK3(k1_setfam_1(sK7),k3_tarski(sK7)),k1_setfam_1(sK7))
    | sK3(k1_setfam_1(sK7),k3_tarski(sK7)) != sK3(k1_setfam_1(sK7),k3_tarski(sK7))
    | k1_setfam_1(X0) != k1_setfam_1(sK7) ),
    inference(instantiation,[status(thm)],[c_901])).

cnf(c_2413,plain,
    ( ~ r2_hidden(sK3(k1_setfam_1(sK7),k3_tarski(sK7)),k1_setfam_1(sK7))
    | r2_hidden(sK3(k1_setfam_1(sK7),k3_tarski(sK7)),k1_setfam_1(k1_xboole_0))
    | sK3(k1_setfam_1(sK7),k3_tarski(sK7)) != sK3(k1_setfam_1(sK7),k3_tarski(sK7))
    | k1_setfam_1(k1_xboole_0) != k1_setfam_1(sK7) ),
    inference(instantiation,[status(thm)],[c_2410])).

cnf(c_254,plain,
    ( X0 != X1
    | k1_setfam_1(X0) = k1_setfam_1(X1) ),
    theory(equality)).

cnf(c_1869,plain,
    ( X0 != sK7
    | k1_setfam_1(X0) = k1_setfam_1(sK7) ),
    inference(instantiation,[status(thm)],[c_254])).

cnf(c_1874,plain,
    ( k1_setfam_1(k1_xboole_0) = k1_setfam_1(sK7)
    | k1_xboole_0 != sK7 ),
    inference(instantiation,[status(thm)],[c_1869])).

cnf(c_9,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(sK3(X0,X1),X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1218,plain,
    ( r1_tarski(k1_setfam_1(sK7),k3_tarski(sK7))
    | ~ r2_hidden(sK3(k1_setfam_1(sK7),k3_tarski(sK7)),k3_tarski(sK7)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_902,plain,
    ( sK3(k1_setfam_1(sK7),k3_tarski(sK7)) = sK3(k1_setfam_1(sK7),k3_tarski(sK7)) ),
    inference(instantiation,[status(thm)],[c_251])).

cnf(c_10,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK3(X0,X1),X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_701,plain,
    ( r1_tarski(k1_setfam_1(sK7),k3_tarski(sK7))
    | r2_hidden(sK3(k1_setfam_1(sK7),k3_tarski(sK7)),k1_setfam_1(sK7)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_22,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_19,negated_conjecture,
    ( ~ r1_tarski(k1_setfam_1(sK7),k3_tarski(sK7)) ),
    inference(cnf_transformation,[],[f49])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_42941,c_42888,c_31073,c_31071,c_8161,c_5691,c_5580,c_3217,c_2413,c_1874,c_1218,c_902,c_701,c_22,c_19])).


%------------------------------------------------------------------------------
