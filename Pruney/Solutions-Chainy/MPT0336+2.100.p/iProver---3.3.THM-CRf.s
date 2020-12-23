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
% DateTime   : Thu Dec  3 11:38:49 EST 2020

% Result     : Theorem 2.85s
% Output     : CNFRefutation 2.85s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 197 expanded)
%              Number of clauses        :   38 (  54 expanded)
%              Number of leaves         :   16 (  43 expanded)
%              Depth                    :   16
%              Number of atoms          :  373 ( 748 expanded)
%              Number of equality atoms :   48 (  51 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
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

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f5])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f18,f39])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f25])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).

fof(f47,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f12,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
     => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X2,X1)
          & r2_hidden(X3,X2)
          & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
       => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f23,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f24,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(flattening,[],[f23])).

fof(f45,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
        & r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
   => ( ~ r1_xboole_0(k2_xboole_0(sK5,sK7),sK6)
      & r1_xboole_0(sK7,sK6)
      & r2_hidden(sK8,sK7)
      & r1_tarski(k3_xboole_0(sK5,sK6),k1_tarski(sK8)) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ~ r1_xboole_0(k2_xboole_0(sK5,sK7),sK6)
    & r1_xboole_0(sK7,sK6)
    & r2_hidden(sK8,sK7)
    & r1_tarski(k3_xboole_0(sK5,sK6),k1_tarski(sK8)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f24,f45])).

fof(f77,plain,(
    r1_tarski(k3_xboole_0(sK5,sK6),k1_tarski(sK8)) ),
    inference(cnf_transformation,[],[f46])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f6])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f41])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)
    <=> ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)
        | r2_hidden(X0,X1) )
      & ( ~ r2_hidden(X0,X1)
        | k4_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f78,plain,(
    r2_hidden(sK8,sK7) ),
    inference(cnf_transformation,[],[f46])).

fof(f79,plain,(
    r1_xboole_0(sK7,sK6) ),
    inference(cnf_transformation,[],[f46])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f34])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f35])).

fof(f37,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK2(X0,X1,X2),X1)
          | ~ r2_hidden(sK2(X0,X1,X2),X0)
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
            & r2_hidden(sK2(X0,X1,X2),X0) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK2(X0,X1,X2),X1)
            | ~ r2_hidden(sK2(X0,X1,X2),X0)
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
              & r2_hidden(sK2(X0,X1,X2),X0) )
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f36,f37])).

fof(f57,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f85,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f57])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f31,plain,(
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
    inference(rectify,[],[f30])).

fof(f32,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
          | ~ r2_hidden(sK1(X0,X1,X2),X0)
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK1(X0,X1,X2),X1)
            & r2_hidden(sK1(X0,X1,X2),X0) )
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
            | ~ r2_hidden(sK1(X0,X1,X2),X0)
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK1(X0,X1,X2),X1)
              & r2_hidden(sK1(X0,X1,X2),X0) )
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f31,f32])).

fof(f51,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f82,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f51])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f80,plain,(
    ~ r1_xboole_0(k2_xboole_0(sK5,sK7),sK6) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_16,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X2,X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_33,negated_conjecture,
    ( r1_tarski(k3_xboole_0(sK5,sK6),k1_tarski(sK8)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_2847,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(sK5,sK6))
    | r2_hidden(X0,k1_tarski(sK8)) ),
    inference(resolution,[status(thm)],[c_2,c_33])).

cnf(c_20,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_2870,plain,
    ( r1_xboole_0(sK5,sK6)
    | r2_hidden(sK4(sK5,sK6),k1_tarski(sK8)) ),
    inference(resolution,[status(thm)],[c_2847,c_20])).

cnf(c_3380,plain,
    ( ~ r1_xboole_0(k1_tarski(sK8),X0)
    | r1_xboole_0(sK5,sK6)
    | ~ r2_hidden(sK4(sK5,sK6),X0) ),
    inference(resolution,[status(thm)],[c_16,c_2870])).

cnf(c_4291,plain,
    ( ~ r1_xboole_0(k1_tarski(sK8),k1_tarski(sK8))
    | r1_xboole_0(sK5,sK6) ),
    inference(resolution,[status(thm)],[c_3380,c_2870])).

cnf(c_28,plain,
    ( r2_hidden(X0,X1)
    | k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1291,plain,
    ( k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)
    | r2_hidden(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_32,negated_conjecture,
    ( r2_hidden(sK8,sK7) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1287,plain,
    ( r2_hidden(sK8,sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_31,negated_conjecture,
    ( r1_xboole_0(sK7,sK6) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1288,plain,
    ( r1_xboole_0(sK7,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_27,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1292,plain,
    ( k4_xboole_0(X0,X1) = X0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_1652,plain,
    ( k4_xboole_0(sK7,sK6) = sK7 ),
    inference(superposition,[status(thm)],[c_1288,c_1292])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1306,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3503,plain,
    ( r2_hidden(X0,sK6) != iProver_top
    | r2_hidden(X0,sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_1652,c_1306])).

cnf(c_3722,plain,
    ( r2_hidden(sK8,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1287,c_3503])).

cnf(c_3752,plain,
    ( k4_xboole_0(k1_tarski(sK8),sK6) = k1_tarski(sK8) ),
    inference(superposition,[status(thm)],[c_1291,c_3722])).

cnf(c_26,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) != X0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1293,plain,
    ( k4_xboole_0(X0,X1) != X0
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_4063,plain,
    ( r1_xboole_0(k1_tarski(sK8),sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_3752,c_1293])).

cnf(c_4073,plain,
    ( r1_xboole_0(k1_tarski(sK8),sK6) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4063])).

cnf(c_7,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_2343,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK4(X0,X1),X1) ),
    inference(resolution,[status(thm)],[c_20,c_7])).

cnf(c_4287,plain,
    ( ~ r1_xboole_0(k1_tarski(sK8),sK6)
    | r1_xboole_0(sK5,sK6) ),
    inference(resolution,[status(thm)],[c_3380,c_2343])).

cnf(c_4294,plain,
    ( r1_xboole_0(sK5,sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4291,c_4073,c_4287])).

cnf(c_15,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_4306,plain,
    ( r1_xboole_0(sK6,sK5) ),
    inference(resolution,[status(thm)],[c_4294,c_15])).

cnf(c_24,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(X0,X2)
    | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1767,plain,
    ( r1_xboole_0(sK6,k2_xboole_0(sK5,sK7))
    | ~ r1_xboole_0(sK6,sK7)
    | ~ r1_xboole_0(sK6,sK5) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_1574,plain,
    ( r1_xboole_0(sK6,sK7) ),
    inference(resolution,[status(thm)],[c_15,c_31])).

cnf(c_1557,plain,
    ( r1_xboole_0(k2_xboole_0(sK5,sK7),sK6)
    | ~ r1_xboole_0(sK6,k2_xboole_0(sK5,sK7)) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_30,negated_conjecture,
    ( ~ r1_xboole_0(k2_xboole_0(sK5,sK7),sK6) ),
    inference(cnf_transformation,[],[f80])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4306,c_1767,c_1574,c_1557,c_30])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n017.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:30:16 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 2.85/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.85/0.99  
% 2.85/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.85/0.99  
% 2.85/0.99  ------  iProver source info
% 2.85/0.99  
% 2.85/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.85/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.85/0.99  git: non_committed_changes: false
% 2.85/0.99  git: last_make_outside_of_git: false
% 2.85/0.99  
% 2.85/0.99  ------ 
% 2.85/0.99  ------ Parsing...
% 2.85/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.85/0.99  
% 2.85/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.85/0.99  
% 2.85/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.85/0.99  
% 2.85/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.85/0.99  ------ Proving...
% 2.85/0.99  ------ Problem Properties 
% 2.85/0.99  
% 2.85/0.99  
% 2.85/0.99  clauses                                 34
% 2.85/0.99  conjectures                             4
% 2.85/0.99  EPR                                     5
% 2.85/0.99  Horn                                    23
% 2.85/0.99  unary                                   4
% 2.85/0.99  binary                                  19
% 2.85/0.99  lits                                    77
% 2.85/0.99  lits eq                                 11
% 2.85/0.99  fd_pure                                 0
% 2.85/0.99  fd_pseudo                               0
% 2.85/0.99  fd_cond                                 0
% 2.85/0.99  fd_pseudo_cond                          6
% 2.85/0.99  AC symbols                              0
% 2.85/0.99  
% 2.85/0.99  ------ Input Options Time Limit: Unbounded
% 2.85/0.99  
% 2.85/0.99  
% 2.85/0.99  ------ 
% 2.85/0.99  Current options:
% 2.85/0.99  ------ 
% 2.85/0.99  
% 2.85/0.99  
% 2.85/0.99  
% 2.85/0.99  
% 2.85/0.99  ------ Proving...
% 2.85/0.99  
% 2.85/0.99  
% 2.85/0.99  % SZS status Theorem for theBenchmark.p
% 2.85/0.99  
% 2.85/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.85/0.99  
% 2.85/0.99  fof(f5,axiom,(
% 2.85/0.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 2.85/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.85/0.99  
% 2.85/0.99  fof(f14,plain,(
% 2.85/0.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 2.85/0.99    inference(rectify,[],[f5])).
% 2.85/0.99  
% 2.85/0.99  fof(f18,plain,(
% 2.85/0.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 2.85/0.99    inference(ennf_transformation,[],[f14])).
% 2.85/0.99  
% 2.85/0.99  fof(f39,plain,(
% 2.85/0.99    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 2.85/0.99    introduced(choice_axiom,[])).
% 2.85/0.99  
% 2.85/0.99  fof(f40,plain,(
% 2.85/0.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 2.85/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f18,f39])).
% 2.85/0.99  
% 2.85/0.99  fof(f65,plain,(
% 2.85/0.99    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 2.85/0.99    inference(cnf_transformation,[],[f40])).
% 2.85/0.99  
% 2.85/0.99  fof(f1,axiom,(
% 2.85/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.85/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.85/0.99  
% 2.85/0.99  fof(f16,plain,(
% 2.85/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.85/0.99    inference(ennf_transformation,[],[f1])).
% 2.85/0.99  
% 2.85/0.99  fof(f25,plain,(
% 2.85/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.85/0.99    inference(nnf_transformation,[],[f16])).
% 2.85/0.99  
% 2.85/0.99  fof(f26,plain,(
% 2.85/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.85/0.99    inference(rectify,[],[f25])).
% 2.85/0.99  
% 2.85/0.99  fof(f27,plain,(
% 2.85/0.99    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 2.85/0.99    introduced(choice_axiom,[])).
% 2.85/0.99  
% 2.85/0.99  fof(f28,plain,(
% 2.85/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.85/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).
% 2.85/0.99  
% 2.85/0.99  fof(f47,plain,(
% 2.85/0.99    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 2.85/0.99    inference(cnf_transformation,[],[f28])).
% 2.85/0.99  
% 2.85/0.99  fof(f12,conjecture,(
% 2.85/0.99    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 2.85/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.85/0.99  
% 2.85/0.99  fof(f13,negated_conjecture,(
% 2.85/0.99    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 2.85/0.99    inference(negated_conjecture,[],[f12])).
% 2.85/0.99  
% 2.85/0.99  fof(f23,plain,(
% 2.85/0.99    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & (r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))))),
% 2.85/0.99    inference(ennf_transformation,[],[f13])).
% 2.85/0.99  
% 2.85/0.99  fof(f24,plain,(
% 2.85/0.99    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)))),
% 2.85/0.99    inference(flattening,[],[f23])).
% 2.85/0.99  
% 2.85/0.99  fof(f45,plain,(
% 2.85/0.99    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => (~r1_xboole_0(k2_xboole_0(sK5,sK7),sK6) & r1_xboole_0(sK7,sK6) & r2_hidden(sK8,sK7) & r1_tarski(k3_xboole_0(sK5,sK6),k1_tarski(sK8)))),
% 2.85/0.99    introduced(choice_axiom,[])).
% 2.85/0.99  
% 2.85/0.99  fof(f46,plain,(
% 2.85/0.99    ~r1_xboole_0(k2_xboole_0(sK5,sK7),sK6) & r1_xboole_0(sK7,sK6) & r2_hidden(sK8,sK7) & r1_tarski(k3_xboole_0(sK5,sK6),k1_tarski(sK8))),
% 2.85/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f24,f45])).
% 2.85/0.99  
% 2.85/0.99  fof(f77,plain,(
% 2.85/0.99    r1_tarski(k3_xboole_0(sK5,sK6),k1_tarski(sK8))),
% 2.85/0.99    inference(cnf_transformation,[],[f46])).
% 2.85/0.99  
% 2.85/0.99  fof(f6,axiom,(
% 2.85/0.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.85/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.85/0.99  
% 2.85/0.99  fof(f15,plain,(
% 2.85/0.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.85/0.99    inference(rectify,[],[f6])).
% 2.85/0.99  
% 2.85/0.99  fof(f19,plain,(
% 2.85/0.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.85/0.99    inference(ennf_transformation,[],[f15])).
% 2.85/0.99  
% 2.85/0.99  fof(f41,plain,(
% 2.85/0.99    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)))),
% 2.85/0.99    introduced(choice_axiom,[])).
% 2.85/0.99  
% 2.85/0.99  fof(f42,plain,(
% 2.85/0.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.85/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f41])).
% 2.85/0.99  
% 2.85/0.99  fof(f66,plain,(
% 2.85/0.99    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 2.85/0.99    inference(cnf_transformation,[],[f42])).
% 2.85/0.99  
% 2.85/0.99  fof(f11,axiom,(
% 2.85/0.99    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0) <=> ~r2_hidden(X0,X1))),
% 2.85/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.85/0.99  
% 2.85/0.99  fof(f44,plain,(
% 2.85/0.99    ! [X0,X1] : ((k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0) | r2_hidden(X0,X1)) & (~r2_hidden(X0,X1) | k4_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0)))),
% 2.85/0.99    inference(nnf_transformation,[],[f11])).
% 2.85/0.99  
% 2.85/0.99  fof(f76,plain,(
% 2.85/0.99    ( ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0) | r2_hidden(X0,X1)) )),
% 2.85/0.99    inference(cnf_transformation,[],[f44])).
% 2.85/0.99  
% 2.85/0.99  fof(f78,plain,(
% 2.85/0.99    r2_hidden(sK8,sK7)),
% 2.85/0.99    inference(cnf_transformation,[],[f46])).
% 2.85/0.99  
% 2.85/0.99  fof(f79,plain,(
% 2.85/0.99    r1_xboole_0(sK7,sK6)),
% 2.85/0.99    inference(cnf_transformation,[],[f46])).
% 2.85/0.99  
% 2.85/0.99  fof(f10,axiom,(
% 2.85/0.99    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 2.85/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.85/0.99  
% 2.85/0.99  fof(f43,plain,(
% 2.85/0.99    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 2.85/0.99    inference(nnf_transformation,[],[f10])).
% 2.85/0.99  
% 2.85/0.99  fof(f73,plain,(
% 2.85/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 2.85/0.99    inference(cnf_transformation,[],[f43])).
% 2.85/0.99  
% 2.85/0.99  fof(f3,axiom,(
% 2.85/0.99    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.85/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.85/0.99  
% 2.85/0.99  fof(f34,plain,(
% 2.85/0.99    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.85/0.99    inference(nnf_transformation,[],[f3])).
% 2.85/0.99  
% 2.85/0.99  fof(f35,plain,(
% 2.85/0.99    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.85/0.99    inference(flattening,[],[f34])).
% 2.85/0.99  
% 2.85/0.99  fof(f36,plain,(
% 2.85/0.99    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.85/0.99    inference(rectify,[],[f35])).
% 2.85/0.99  
% 2.85/0.99  fof(f37,plain,(
% 2.85/0.99    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 2.85/0.99    introduced(choice_axiom,[])).
% 2.85/0.99  
% 2.85/0.99  fof(f38,plain,(
% 2.85/0.99    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.85/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f36,f37])).
% 2.85/0.99  
% 2.85/0.99  fof(f57,plain,(
% 2.85/0.99    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.85/0.99    inference(cnf_transformation,[],[f38])).
% 2.85/0.99  
% 2.85/0.99  fof(f85,plain,(
% 2.85/0.99    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 2.85/0.99    inference(equality_resolution,[],[f57])).
% 2.85/0.99  
% 2.85/0.99  fof(f74,plain,(
% 2.85/0.99    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 2.85/0.99    inference(cnf_transformation,[],[f43])).
% 2.85/0.99  
% 2.85/0.99  fof(f2,axiom,(
% 2.85/0.99    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.85/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.85/0.99  
% 2.85/0.99  fof(f29,plain,(
% 2.85/0.99    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 2.85/0.99    inference(nnf_transformation,[],[f2])).
% 2.85/0.99  
% 2.85/0.99  fof(f30,plain,(
% 2.85/0.99    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 2.85/0.99    inference(flattening,[],[f29])).
% 2.85/0.99  
% 2.85/0.99  fof(f31,plain,(
% 2.85/0.99    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 2.85/0.99    inference(rectify,[],[f30])).
% 2.85/0.99  
% 2.85/0.99  fof(f32,plain,(
% 2.85/0.99    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 2.85/0.99    introduced(choice_axiom,[])).
% 2.85/0.99  
% 2.85/0.99  fof(f33,plain,(
% 2.85/0.99    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 2.85/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f31,f32])).
% 2.85/0.99  
% 2.85/0.99  fof(f51,plain,(
% 2.85/0.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 2.85/0.99    inference(cnf_transformation,[],[f33])).
% 2.85/0.99  
% 2.85/0.99  fof(f82,plain,(
% 2.85/0.99    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,k3_xboole_0(X0,X1))) )),
% 2.85/0.99    inference(equality_resolution,[],[f51])).
% 2.85/0.99  
% 2.85/0.99  fof(f4,axiom,(
% 2.85/0.99    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 2.85/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.85/0.99  
% 2.85/0.99  fof(f17,plain,(
% 2.85/0.99    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 2.85/0.99    inference(ennf_transformation,[],[f4])).
% 2.85/0.99  
% 2.85/0.99  fof(f62,plain,(
% 2.85/0.99    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 2.85/0.99    inference(cnf_transformation,[],[f17])).
% 2.85/0.99  
% 2.85/0.99  fof(f8,axiom,(
% 2.85/0.99    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 2.85/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.85/0.99  
% 2.85/0.99  fof(f21,plain,(
% 2.85/0.99    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 2.85/0.99    inference(ennf_transformation,[],[f8])).
% 2.85/0.99  
% 2.85/0.99  fof(f69,plain,(
% 2.85/0.99    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 2.85/0.99    inference(cnf_transformation,[],[f21])).
% 2.85/0.99  
% 2.85/0.99  fof(f80,plain,(
% 2.85/0.99    ~r1_xboole_0(k2_xboole_0(sK5,sK7),sK6)),
% 2.85/0.99    inference(cnf_transformation,[],[f46])).
% 2.85/0.99  
% 2.85/0.99  cnf(c_16,plain,
% 2.85/0.99      ( ~ r1_xboole_0(X0,X1) | ~ r2_hidden(X2,X1) | ~ r2_hidden(X2,X0) ),
% 2.85/0.99      inference(cnf_transformation,[],[f65]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_2,plain,
% 2.85/0.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 2.85/0.99      inference(cnf_transformation,[],[f47]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_33,negated_conjecture,
% 2.85/0.99      ( r1_tarski(k3_xboole_0(sK5,sK6),k1_tarski(sK8)) ),
% 2.85/0.99      inference(cnf_transformation,[],[f77]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_2847,plain,
% 2.85/0.99      ( ~ r2_hidden(X0,k3_xboole_0(sK5,sK6))
% 2.85/0.99      | r2_hidden(X0,k1_tarski(sK8)) ),
% 2.85/0.99      inference(resolution,[status(thm)],[c_2,c_33]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_20,plain,
% 2.85/0.99      ( r1_xboole_0(X0,X1) | r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) ),
% 2.85/0.99      inference(cnf_transformation,[],[f66]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_2870,plain,
% 2.85/0.99      ( r1_xboole_0(sK5,sK6) | r2_hidden(sK4(sK5,sK6),k1_tarski(sK8)) ),
% 2.85/0.99      inference(resolution,[status(thm)],[c_2847,c_20]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_3380,plain,
% 2.85/0.99      ( ~ r1_xboole_0(k1_tarski(sK8),X0)
% 2.85/0.99      | r1_xboole_0(sK5,sK6)
% 2.85/0.99      | ~ r2_hidden(sK4(sK5,sK6),X0) ),
% 2.85/0.99      inference(resolution,[status(thm)],[c_16,c_2870]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_4291,plain,
% 2.85/0.99      ( ~ r1_xboole_0(k1_tarski(sK8),k1_tarski(sK8))
% 2.85/0.99      | r1_xboole_0(sK5,sK6) ),
% 2.85/0.99      inference(resolution,[status(thm)],[c_3380,c_2870]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_28,plain,
% 2.85/0.99      ( r2_hidden(X0,X1)
% 2.85/0.99      | k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0) ),
% 2.85/0.99      inference(cnf_transformation,[],[f76]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_1291,plain,
% 2.85/0.99      ( k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)
% 2.85/0.99      | r2_hidden(X0,X1) = iProver_top ),
% 2.85/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_32,negated_conjecture,
% 2.85/0.99      ( r2_hidden(sK8,sK7) ),
% 2.85/0.99      inference(cnf_transformation,[],[f78]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_1287,plain,
% 2.85/0.99      ( r2_hidden(sK8,sK7) = iProver_top ),
% 2.85/0.99      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_31,negated_conjecture,
% 2.85/0.99      ( r1_xboole_0(sK7,sK6) ),
% 2.85/0.99      inference(cnf_transformation,[],[f79]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_1288,plain,
% 2.85/0.99      ( r1_xboole_0(sK7,sK6) = iProver_top ),
% 2.85/0.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_27,plain,
% 2.85/0.99      ( ~ r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0 ),
% 2.85/0.99      inference(cnf_transformation,[],[f73]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_1292,plain,
% 2.85/0.99      ( k4_xboole_0(X0,X1) = X0 | r1_xboole_0(X0,X1) != iProver_top ),
% 2.85/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_1652,plain,
% 2.85/0.99      ( k4_xboole_0(sK7,sK6) = sK7 ),
% 2.85/0.99      inference(superposition,[status(thm)],[c_1288,c_1292]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_13,plain,
% 2.85/0.99      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
% 2.85/0.99      inference(cnf_transformation,[],[f85]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_1306,plain,
% 2.85/0.99      ( r2_hidden(X0,X1) != iProver_top
% 2.85/0.99      | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
% 2.85/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_3503,plain,
% 2.85/0.99      ( r2_hidden(X0,sK6) != iProver_top
% 2.85/0.99      | r2_hidden(X0,sK7) != iProver_top ),
% 2.85/0.99      inference(superposition,[status(thm)],[c_1652,c_1306]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_3722,plain,
% 2.85/0.99      ( r2_hidden(sK8,sK6) != iProver_top ),
% 2.85/0.99      inference(superposition,[status(thm)],[c_1287,c_3503]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_3752,plain,
% 2.85/0.99      ( k4_xboole_0(k1_tarski(sK8),sK6) = k1_tarski(sK8) ),
% 2.85/0.99      inference(superposition,[status(thm)],[c_1291,c_3722]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_26,plain,
% 2.85/0.99      ( r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0 ),
% 2.85/0.99      inference(cnf_transformation,[],[f74]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_1293,plain,
% 2.85/0.99      ( k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1) = iProver_top ),
% 2.85/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_4063,plain,
% 2.85/0.99      ( r1_xboole_0(k1_tarski(sK8),sK6) = iProver_top ),
% 2.85/0.99      inference(superposition,[status(thm)],[c_3752,c_1293]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_4073,plain,
% 2.85/0.99      ( r1_xboole_0(k1_tarski(sK8),sK6) ),
% 2.85/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_4063]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_7,plain,
% 2.85/0.99      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k3_xboole_0(X2,X1)) ),
% 2.85/0.99      inference(cnf_transformation,[],[f82]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_2343,plain,
% 2.85/0.99      ( r1_xboole_0(X0,X1) | r2_hidden(sK4(X0,X1),X1) ),
% 2.85/0.99      inference(resolution,[status(thm)],[c_20,c_7]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_4287,plain,
% 2.85/0.99      ( ~ r1_xboole_0(k1_tarski(sK8),sK6) | r1_xboole_0(sK5,sK6) ),
% 2.85/0.99      inference(resolution,[status(thm)],[c_3380,c_2343]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_4294,plain,
% 2.85/0.99      ( r1_xboole_0(sK5,sK6) ),
% 2.85/0.99      inference(global_propositional_subsumption,
% 2.85/0.99                [status(thm)],
% 2.85/0.99                [c_4291,c_4073,c_4287]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_15,plain,
% 2.85/0.99      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 2.85/0.99      inference(cnf_transformation,[],[f62]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_4306,plain,
% 2.85/0.99      ( r1_xboole_0(sK6,sK5) ),
% 2.85/0.99      inference(resolution,[status(thm)],[c_4294,c_15]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_24,plain,
% 2.85/0.99      ( ~ r1_xboole_0(X0,X1)
% 2.85/0.99      | ~ r1_xboole_0(X0,X2)
% 2.85/0.99      | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 2.85/0.99      inference(cnf_transformation,[],[f69]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_1767,plain,
% 2.85/0.99      ( r1_xboole_0(sK6,k2_xboole_0(sK5,sK7))
% 2.85/0.99      | ~ r1_xboole_0(sK6,sK7)
% 2.85/0.99      | ~ r1_xboole_0(sK6,sK5) ),
% 2.85/0.99      inference(instantiation,[status(thm)],[c_24]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_1574,plain,
% 2.85/0.99      ( r1_xboole_0(sK6,sK7) ),
% 2.85/0.99      inference(resolution,[status(thm)],[c_15,c_31]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_1557,plain,
% 2.85/0.99      ( r1_xboole_0(k2_xboole_0(sK5,sK7),sK6)
% 2.85/0.99      | ~ r1_xboole_0(sK6,k2_xboole_0(sK5,sK7)) ),
% 2.85/0.99      inference(instantiation,[status(thm)],[c_15]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_30,negated_conjecture,
% 2.85/0.99      ( ~ r1_xboole_0(k2_xboole_0(sK5,sK7),sK6) ),
% 2.85/0.99      inference(cnf_transformation,[],[f80]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(contradiction,plain,
% 2.85/0.99      ( $false ),
% 2.85/0.99      inference(minisat,[status(thm)],[c_4306,c_1767,c_1574,c_1557,c_30]) ).
% 2.85/0.99  
% 2.85/0.99  
% 2.85/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.85/0.99  
% 2.85/0.99  ------                               Statistics
% 2.85/0.99  
% 2.85/0.99  ------ Selected
% 2.85/0.99  
% 2.85/0.99  total_time:                             0.146
% 2.85/0.99  
%------------------------------------------------------------------------------
