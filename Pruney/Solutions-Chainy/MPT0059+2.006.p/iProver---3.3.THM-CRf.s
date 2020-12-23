%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:22:58 EST 2020

% Result     : Theorem 3.88s
% Output     : CNFRefutation 3.88s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 884 expanded)
%              Number of clauses        :   50 ( 203 expanded)
%              Number of leaves         :   12 ( 186 expanded)
%              Depth                    :   18
%              Number of atoms          :  433 (5997 expanded)
%              Number of equality atoms :   54 ( 827 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f11,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f10])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f13])).

fof(f15,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f15])).

fof(f34,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
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
    inference(flattening,[],[f17])).

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
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f18])).

fof(f20,plain,(
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

fof(f21,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f20])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | r2_hidden(sK1(X0,X1,X2),X1)
      | r2_hidden(sK1(X0,X1,X2),X0)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f7,conjecture,(
    ! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(negated_conjecture,[],[f7])).

fof(f12,plain,(
    ? [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) != k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(ennf_transformation,[],[f8])).

fof(f32,plain,
    ( ? [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) != k4_xboole_0(X0,k4_xboole_0(X1,X2))
   => k2_xboole_0(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6)) != k4_xboole_0(sK4,k4_xboole_0(sK5,sK6)) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    k2_xboole_0(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6)) != k4_xboole_0(sK4,k4_xboole_0(sK5,sK6)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f12,f32])).

fof(f57,plain,(
    k2_xboole_0(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6)) != k4_xboole_0(sK4,k4_xboole_0(sK5,sK6)) ),
    inference(cnf_transformation,[],[f33])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
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
    inference(nnf_transformation,[],[f4])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f29,plain,(
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
    inference(rectify,[],[f28])).

fof(f30,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK3(X0,X1,X2),X1)
          | ~ r2_hidden(sK3(X0,X1,X2),X0)
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
            & r2_hidden(sK3(X0,X1,X2),X0) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK3(X0,X1,X2),X1)
            | ~ r2_hidden(sK3(X0,X1,X2),X0)
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
              & r2_hidden(sK3(X0,X1,X2),X0) )
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f29,f30])).

fof(f51,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f64,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f51])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
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

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f24,plain,(
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
    inference(rectify,[],[f23])).

fof(f25,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
          | ~ r2_hidden(sK2(X0,X1,X2),X0)
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK2(X0,X1,X2),X1)
            & r2_hidden(sK2(X0,X1,X2),X0) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
            | ~ r2_hidden(sK2(X0,X1,X2),X0)
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK2(X0,X1,X2),X1)
              & r2_hidden(sK2(X0,X1,X2),X0) )
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f24,f25])).

fof(f45,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f61,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f45])).

fof(f49,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f66,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f49])).

fof(f43,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f63,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f43])).

fof(f50,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f65,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f50])).

fof(f44,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f62,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f44])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK1(X0,X1,X2),X0)
      | ~ r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK1(X0,X1,X2),X1)
      | ~ r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

cnf(c_21,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X3)
    | r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_2597,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(X1,X2))
    | r2_hidden(X0,k4_xboole_0(X3,X4))
    | ~ r1_tarski(X1,X3)
    | ~ r1_tarski(X4,X2) ),
    inference(resolution,[status(thm)],[c_21,c_2])).

cnf(c_5,plain,
    ( r2_hidden(sK1(X0,X1,X2),X1)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | r2_hidden(sK1(X0,X1,X2),X0)
    | k2_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_23,negated_conjecture,
    ( k2_xboole_0(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6)) != k4_xboole_0(sK4,k4_xboole_0(sK5,sK6)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_7551,plain,
    ( r2_hidden(sK1(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6))),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6)))
    | r2_hidden(sK1(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6))),k4_xboole_0(sK4,sK5))
    | r2_hidden(sK1(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6))),k3_xboole_0(sK4,sK6)) ),
    inference(resolution,[status(thm)],[c_5,c_23])).

cnf(c_12381,plain,
    ( r2_hidden(sK1(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6))),k4_xboole_0(X0,X1))
    | r2_hidden(sK1(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6))),k4_xboole_0(sK4,sK5))
    | r2_hidden(sK1(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6))),k3_xboole_0(sK4,sK6))
    | ~ r1_tarski(X1,k4_xboole_0(sK5,sK6))
    | ~ r1_tarski(sK4,X0) ),
    inference(resolution,[status(thm)],[c_2597,c_7551])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1431,plain,
    ( r2_hidden(sK1(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6))),X0)
    | r2_hidden(sK1(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6))),k4_xboole_0(sK4,X0))
    | ~ r2_hidden(sK1(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6))),sK4) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_2698,plain,
    ( r2_hidden(sK1(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6))),k4_xboole_0(sK4,sK5))
    | r2_hidden(sK1(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6))),sK5)
    | ~ r2_hidden(sK1(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6))),sK4) ),
    inference(instantiation,[status(thm)],[c_1431])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1448,plain,
    ( ~ r2_hidden(sK1(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6))),X0)
    | r2_hidden(sK1(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6))),k3_xboole_0(sK4,X0))
    | ~ r2_hidden(sK1(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6))),sK4) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_2709,plain,
    ( r2_hidden(sK1(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6))),k3_xboole_0(sK4,sK6))
    | ~ r2_hidden(sK1(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6))),sK6)
    | ~ r2_hidden(sK1(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6))),sK4) ),
    inference(instantiation,[status(thm)],[c_1448])).

cnf(c_20,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_7696,plain,
    ( r2_hidden(sK1(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6))),k4_xboole_0(sK4,sK5))
    | r2_hidden(sK1(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6))),k3_xboole_0(sK4,sK6))
    | r2_hidden(sK1(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6))),sK4) ),
    inference(resolution,[status(thm)],[c_7551,c_20])).

cnf(c_14,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_874,plain,
    ( ~ r2_hidden(sK1(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6))),k3_xboole_0(sK4,sK6))
    | r2_hidden(sK1(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6))),sK4) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1051,plain,
    ( ~ r2_hidden(sK1(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6))),k4_xboole_0(sK4,sK5))
    | r2_hidden(sK1(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6))),sK4) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_7861,plain,
    ( r2_hidden(sK1(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6))),sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7696,c_874,c_1051])).

cnf(c_19,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_7694,plain,
    ( ~ r2_hidden(sK1(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6))),k4_xboole_0(sK5,sK6))
    | r2_hidden(sK1(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6))),k4_xboole_0(sK4,sK5))
    | r2_hidden(sK1(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6))),k3_xboole_0(sK4,sK6)) ),
    inference(resolution,[status(thm)],[c_7551,c_19])).

cnf(c_8369,plain,
    ( r2_hidden(sK1(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6))),k4_xboole_0(sK4,sK5))
    | r2_hidden(sK1(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6))),k3_xboole_0(sK4,sK6))
    | r2_hidden(sK1(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6))),sK6)
    | ~ r2_hidden(sK1(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6))),sK5) ),
    inference(resolution,[status(thm)],[c_7694,c_18])).

cnf(c_13,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_871,plain,
    ( ~ r2_hidden(sK1(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6))),k3_xboole_0(sK4,sK6))
    | r2_hidden(sK1(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6))),sK6) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1048,plain,
    ( ~ r2_hidden(sK1(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6))),k4_xboole_0(sK4,sK5))
    | ~ r2_hidden(sK1(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6))),sK5) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_8372,plain,
    ( r2_hidden(sK1(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6))),sK6)
    | ~ r2_hidden(sK1(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6))),sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8369,c_871,c_1048])).

cnf(c_12768,plain,
    ( r2_hidden(sK1(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6))),k4_xboole_0(sK4,sK5))
    | r2_hidden(sK1(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6))),k3_xboole_0(sK4,sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12381,c_874,c_1051,c_2698,c_2709,c_7696,c_8372])).

cnf(c_4,plain,
    ( ~ r2_hidden(sK1(X0,X1,X2),X2)
    | ~ r2_hidden(sK1(X0,X1,X2),X0)
    | k2_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_13268,plain,
    ( ~ r2_hidden(sK1(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6))),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6)))
    | r2_hidden(sK1(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6))),k3_xboole_0(sK4,sK6))
    | k2_xboole_0(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6)) = k4_xboole_0(sK4,k4_xboole_0(sK5,sK6)) ),
    inference(resolution,[status(thm)],[c_12768,c_4])).

cnf(c_3,plain,
    ( ~ r2_hidden(sK1(X0,X1,X2),X1)
    | ~ r2_hidden(sK1(X0,X1,X2),X2)
    | k2_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_914,plain,
    ( ~ r2_hidden(sK1(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6))),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6)))
    | ~ r2_hidden(sK1(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6))),k3_xboole_0(sK4,sK6))
    | k2_xboole_0(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6)) = k4_xboole_0(sK4,k4_xboole_0(sK5,sK6)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_13668,plain,
    ( ~ r2_hidden(sK1(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6))),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_13268,c_23,c_914])).

cnf(c_13681,plain,
    ( r2_hidden(sK1(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6))),k4_xboole_0(sK5,sK6))
    | ~ r2_hidden(sK1(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6))),sK4) ),
    inference(resolution,[status(thm)],[c_13668,c_18])).

cnf(c_2695,plain,
    ( r2_hidden(sK1(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6))),k4_xboole_0(sK5,sK6))
    | r2_hidden(sK1(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6))),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6)))
    | ~ r2_hidden(sK1(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6))),sK4) ),
    inference(instantiation,[status(thm)],[c_1431])).

cnf(c_14509,plain,
    ( r2_hidden(sK1(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6))),k4_xboole_0(sK5,sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_13681,c_23,c_874,c_914,c_1051,c_2695,c_7696,c_13268])).

cnf(c_14521,plain,
    ( ~ r2_hidden(sK1(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6))),sK6) ),
    inference(resolution,[status(thm)],[c_14509,c_19])).

cnf(c_13275,plain,
    ( r2_hidden(sK1(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6))),k4_xboole_0(X0,X1))
    | r2_hidden(sK1(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6))),k3_xboole_0(sK4,sK6))
    | ~ r1_tarski(X1,sK5)
    | ~ r1_tarski(sK4,X0) ),
    inference(resolution,[status(thm)],[c_12768,c_2597])).

cnf(c_13683,plain,
    ( r2_hidden(sK1(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6))),k3_xboole_0(sK4,sK6))
    | ~ r1_tarski(k4_xboole_0(sK5,sK6),sK5)
    | ~ r1_tarski(sK4,sK4) ),
    inference(resolution,[status(thm)],[c_13668,c_13275])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_583,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_584,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1061,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_583,c_584])).

cnf(c_1079,plain,
    ( r1_tarski(X0,X0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1061])).

cnf(c_1081,plain,
    ( r1_tarski(sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_1079])).

cnf(c_13686,plain,
    ( ~ r1_tarski(k4_xboole_0(sK5,sK6),sK5)
    | r2_hidden(sK1(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6))),k3_xboole_0(sK4,sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_13683,c_1081])).

cnf(c_13687,plain,
    ( r2_hidden(sK1(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6))),k3_xboole_0(sK4,sK6))
    | ~ r1_tarski(k4_xboole_0(sK5,sK6),sK5) ),
    inference(renaming,[status(thm)],[c_13686])).

cnf(c_22,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_13692,plain,
    ( r2_hidden(sK1(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6))),k3_xboole_0(sK4,sK6)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_13687,c_22])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_14521,c_13692,c_871])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.32  % Computer   : n005.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 14:30:47 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.32  % Running in FOF mode
% 3.88/0.97  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.88/0.97  
% 3.88/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.88/0.97  
% 3.88/0.97  ------  iProver source info
% 3.88/0.97  
% 3.88/0.97  git: date: 2020-06-30 10:37:57 +0100
% 3.88/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.88/0.97  git: non_committed_changes: false
% 3.88/0.97  git: last_make_outside_of_git: false
% 3.88/0.97  
% 3.88/0.97  ------ 
% 3.88/0.97  ------ Parsing...
% 3.88/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.88/0.97  
% 3.88/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.88/0.97  
% 3.88/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.88/0.97  
% 3.88/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.88/0.97  ------ Proving...
% 3.88/0.97  ------ Problem Properties 
% 3.88/0.97  
% 3.88/0.97  
% 3.88/0.97  clauses                                 24
% 3.88/0.97  conjectures                             1
% 3.88/0.97  EPR                                     1
% 3.88/0.97  Horn                                    15
% 3.88/0.97  unary                                   2
% 3.88/0.97  binary                                  8
% 3.88/0.97  lits                                    63
% 3.88/0.97  lits eq                                 10
% 3.88/0.97  fd_pure                                 0
% 3.88/0.97  fd_pseudo                               0
% 3.88/0.97  fd_cond                                 0
% 3.88/0.97  fd_pseudo_cond                          9
% 3.88/0.97  AC symbols                              0
% 3.88/0.97  
% 3.88/0.97  ------ Input Options Time Limit: Unbounded
% 3.88/0.97  
% 3.88/0.97  
% 3.88/0.97  ------ 
% 3.88/0.97  Current options:
% 3.88/0.97  ------ 
% 3.88/0.97  
% 3.88/0.97  
% 3.88/0.97  
% 3.88/0.97  
% 3.88/0.97  ------ Proving...
% 3.88/0.97  
% 3.88/0.97  
% 3.88/0.97  % SZS status Theorem for theBenchmark.p
% 3.88/0.97  
% 3.88/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 3.88/0.97  
% 3.88/0.97  fof(f5,axiom,(
% 3.88/0.97    ! [X0,X1,X2,X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2)))),
% 3.88/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.88/0.97  
% 3.88/0.97  fof(f10,plain,(
% 3.88/0.97    ! [X0,X1,X2,X3] : (r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2)) | (~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)))),
% 3.88/0.97    inference(ennf_transformation,[],[f5])).
% 3.88/0.97  
% 3.88/0.97  fof(f11,plain,(
% 3.88/0.97    ! [X0,X1,X2,X3] : (r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1))),
% 3.88/0.97    inference(flattening,[],[f10])).
% 3.88/0.97  
% 3.88/0.97  fof(f55,plain,(
% 3.88/0.97    ( ! [X2,X0,X3,X1] : (r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)) )),
% 3.88/0.97    inference(cnf_transformation,[],[f11])).
% 3.88/0.97  
% 3.88/0.97  fof(f1,axiom,(
% 3.88/0.97    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.88/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.88/0.97  
% 3.88/0.97  fof(f9,plain,(
% 3.88/0.97    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.88/0.97    inference(ennf_transformation,[],[f1])).
% 3.88/0.97  
% 3.88/0.97  fof(f13,plain,(
% 3.88/0.97    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.88/0.97    inference(nnf_transformation,[],[f9])).
% 3.88/0.97  
% 3.88/0.97  fof(f14,plain,(
% 3.88/0.97    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.88/0.97    inference(rectify,[],[f13])).
% 3.88/0.97  
% 3.88/0.97  fof(f15,plain,(
% 3.88/0.97    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.88/0.97    introduced(choice_axiom,[])).
% 3.88/0.97  
% 3.88/0.97  fof(f16,plain,(
% 3.88/0.97    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.88/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f15])).
% 3.88/0.97  
% 3.88/0.97  fof(f34,plain,(
% 3.88/0.97    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 3.88/0.97    inference(cnf_transformation,[],[f16])).
% 3.88/0.97  
% 3.88/0.97  fof(f2,axiom,(
% 3.88/0.97    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 3.88/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.88/0.97  
% 3.88/0.97  fof(f17,plain,(
% 3.88/0.97    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.88/0.97    inference(nnf_transformation,[],[f2])).
% 3.88/0.97  
% 3.88/0.97  fof(f18,plain,(
% 3.88/0.97    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.88/0.97    inference(flattening,[],[f17])).
% 3.88/0.97  
% 3.88/0.97  fof(f19,plain,(
% 3.88/0.97    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.88/0.97    inference(rectify,[],[f18])).
% 3.88/0.97  
% 3.88/0.97  fof(f20,plain,(
% 3.88/0.97    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK1(X0,X1,X2),X1) & ~r2_hidden(sK1(X0,X1,X2),X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (r2_hidden(sK1(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 3.88/0.97    introduced(choice_axiom,[])).
% 3.88/0.97  
% 3.88/0.97  fof(f21,plain,(
% 3.88/0.97    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK1(X0,X1,X2),X1) & ~r2_hidden(sK1(X0,X1,X2),X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (r2_hidden(sK1(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.88/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f20])).
% 3.88/0.97  
% 3.88/0.97  fof(f40,plain,(
% 3.88/0.97    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | r2_hidden(sK1(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 3.88/0.97    inference(cnf_transformation,[],[f21])).
% 3.88/0.97  
% 3.88/0.97  fof(f7,conjecture,(
% 3.88/0.97    ! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,X2))),
% 3.88/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.88/0.97  
% 3.88/0.97  fof(f8,negated_conjecture,(
% 3.88/0.97    ~! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,X2))),
% 3.88/0.97    inference(negated_conjecture,[],[f7])).
% 3.88/0.97  
% 3.88/0.97  fof(f12,plain,(
% 3.88/0.97    ? [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) != k4_xboole_0(X0,k4_xboole_0(X1,X2))),
% 3.88/0.97    inference(ennf_transformation,[],[f8])).
% 3.88/0.97  
% 3.88/0.97  fof(f32,plain,(
% 3.88/0.97    ? [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) != k4_xboole_0(X0,k4_xboole_0(X1,X2)) => k2_xboole_0(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6)) != k4_xboole_0(sK4,k4_xboole_0(sK5,sK6))),
% 3.88/0.97    introduced(choice_axiom,[])).
% 3.88/0.97  
% 3.88/0.97  fof(f33,plain,(
% 3.88/0.97    k2_xboole_0(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6)) != k4_xboole_0(sK4,k4_xboole_0(sK5,sK6))),
% 3.88/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f12,f32])).
% 3.88/0.97  
% 3.88/0.97  fof(f57,plain,(
% 3.88/0.97    k2_xboole_0(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6)) != k4_xboole_0(sK4,k4_xboole_0(sK5,sK6))),
% 3.88/0.97    inference(cnf_transformation,[],[f33])).
% 3.88/0.97  
% 3.88/0.97  fof(f4,axiom,(
% 3.88/0.97    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 3.88/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.88/0.97  
% 3.88/0.97  fof(f27,plain,(
% 3.88/0.97    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.88/0.97    inference(nnf_transformation,[],[f4])).
% 3.88/0.97  
% 3.88/0.97  fof(f28,plain,(
% 3.88/0.97    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.88/0.97    inference(flattening,[],[f27])).
% 3.88/0.97  
% 3.88/0.97  fof(f29,plain,(
% 3.88/0.97    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.88/0.97    inference(rectify,[],[f28])).
% 3.88/0.97  
% 3.88/0.97  fof(f30,plain,(
% 3.88/0.97    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 3.88/0.97    introduced(choice_axiom,[])).
% 3.88/0.97  
% 3.88/0.97  fof(f31,plain,(
% 3.88/0.97    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.88/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f29,f30])).
% 3.88/0.97  
% 3.88/0.97  fof(f51,plain,(
% 3.88/0.97    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 3.88/0.97    inference(cnf_transformation,[],[f31])).
% 3.88/0.97  
% 3.88/0.97  fof(f64,plain,(
% 3.88/0.97    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 3.88/0.97    inference(equality_resolution,[],[f51])).
% 3.88/0.97  
% 3.88/0.97  fof(f3,axiom,(
% 3.88/0.97    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 3.88/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.88/0.97  
% 3.88/0.97  fof(f22,plain,(
% 3.88/0.97    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.88/0.97    inference(nnf_transformation,[],[f3])).
% 3.88/0.97  
% 3.88/0.97  fof(f23,plain,(
% 3.88/0.97    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.88/0.97    inference(flattening,[],[f22])).
% 3.88/0.97  
% 3.88/0.97  fof(f24,plain,(
% 3.88/0.97    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.88/0.97    inference(rectify,[],[f23])).
% 3.88/0.97  
% 3.88/0.97  fof(f25,plain,(
% 3.88/0.97    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 3.88/0.97    introduced(choice_axiom,[])).
% 3.88/0.97  
% 3.88/0.97  fof(f26,plain,(
% 3.88/0.97    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.88/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f24,f25])).
% 3.88/0.97  
% 3.88/0.97  fof(f45,plain,(
% 3.88/0.97    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k3_xboole_0(X0,X1) != X2) )),
% 3.88/0.97    inference(cnf_transformation,[],[f26])).
% 3.88/0.97  
% 3.88/0.97  fof(f61,plain,(
% 3.88/0.97    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_xboole_0(X0,X1)) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 3.88/0.97    inference(equality_resolution,[],[f45])).
% 3.88/0.97  
% 3.88/0.97  fof(f49,plain,(
% 3.88/0.97    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 3.88/0.97    inference(cnf_transformation,[],[f31])).
% 3.88/0.97  
% 3.88/0.97  fof(f66,plain,(
% 3.88/0.97    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 3.88/0.97    inference(equality_resolution,[],[f49])).
% 3.88/0.97  
% 3.88/0.97  fof(f43,plain,(
% 3.88/0.97    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 3.88/0.97    inference(cnf_transformation,[],[f26])).
% 3.88/0.97  
% 3.88/0.97  fof(f63,plain,(
% 3.88/0.97    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k3_xboole_0(X0,X1))) )),
% 3.88/0.97    inference(equality_resolution,[],[f43])).
% 3.88/0.97  
% 3.88/0.97  fof(f50,plain,(
% 3.88/0.97    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 3.88/0.97    inference(cnf_transformation,[],[f31])).
% 3.88/0.97  
% 3.88/0.97  fof(f65,plain,(
% 3.88/0.97    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 3.88/0.97    inference(equality_resolution,[],[f50])).
% 3.88/0.97  
% 3.88/0.97  fof(f44,plain,(
% 3.88/0.97    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 3.88/0.97    inference(cnf_transformation,[],[f26])).
% 3.88/0.97  
% 3.88/0.97  fof(f62,plain,(
% 3.88/0.97    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,k3_xboole_0(X0,X1))) )),
% 3.88/0.97    inference(equality_resolution,[],[f44])).
% 3.88/0.97  
% 3.88/0.97  fof(f41,plain,(
% 3.88/0.97    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) )),
% 3.88/0.97    inference(cnf_transformation,[],[f21])).
% 3.88/0.97  
% 3.88/0.97  fof(f42,plain,(
% 3.88/0.97    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | ~r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X2)) )),
% 3.88/0.97    inference(cnf_transformation,[],[f21])).
% 3.88/0.97  
% 3.88/0.97  fof(f35,plain,(
% 3.88/0.97    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 3.88/0.97    inference(cnf_transformation,[],[f16])).
% 3.88/0.97  
% 3.88/0.97  fof(f36,plain,(
% 3.88/0.97    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 3.88/0.97    inference(cnf_transformation,[],[f16])).
% 3.88/0.97  
% 3.88/0.97  fof(f6,axiom,(
% 3.88/0.97    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 3.88/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.88/0.97  
% 3.88/0.97  fof(f56,plain,(
% 3.88/0.97    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 3.88/0.97    inference(cnf_transformation,[],[f6])).
% 3.88/0.97  
% 3.88/0.97  cnf(c_21,plain,
% 3.88/0.97      ( ~ r1_tarski(X0,X1)
% 3.88/0.97      | ~ r1_tarski(X2,X3)
% 3.88/0.97      | r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2)) ),
% 3.88/0.97      inference(cnf_transformation,[],[f55]) ).
% 3.88/0.97  
% 3.88/0.97  cnf(c_2,plain,
% 3.88/0.97      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 3.88/0.97      inference(cnf_transformation,[],[f34]) ).
% 3.88/0.97  
% 3.88/0.97  cnf(c_2597,plain,
% 3.88/0.97      ( ~ r2_hidden(X0,k4_xboole_0(X1,X2))
% 3.88/0.97      | r2_hidden(X0,k4_xboole_0(X3,X4))
% 3.88/0.97      | ~ r1_tarski(X1,X3)
% 3.88/0.97      | ~ r1_tarski(X4,X2) ),
% 3.88/0.97      inference(resolution,[status(thm)],[c_21,c_2]) ).
% 3.88/0.97  
% 3.88/0.97  cnf(c_5,plain,
% 3.88/0.97      ( r2_hidden(sK1(X0,X1,X2),X1)
% 3.88/0.97      | r2_hidden(sK1(X0,X1,X2),X2)
% 3.88/0.97      | r2_hidden(sK1(X0,X1,X2),X0)
% 3.88/0.97      | k2_xboole_0(X0,X1) = X2 ),
% 3.88/0.97      inference(cnf_transformation,[],[f40]) ).
% 3.88/0.97  
% 3.88/0.97  cnf(c_23,negated_conjecture,
% 3.88/0.97      ( k2_xboole_0(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6)) != k4_xboole_0(sK4,k4_xboole_0(sK5,sK6)) ),
% 3.88/0.97      inference(cnf_transformation,[],[f57]) ).
% 3.88/0.97  
% 3.88/0.97  cnf(c_7551,plain,
% 3.88/0.97      ( r2_hidden(sK1(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6))),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6)))
% 3.88/0.97      | r2_hidden(sK1(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6))),k4_xboole_0(sK4,sK5))
% 3.88/0.97      | r2_hidden(sK1(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6))),k3_xboole_0(sK4,sK6)) ),
% 3.88/0.97      inference(resolution,[status(thm)],[c_5,c_23]) ).
% 3.88/0.97  
% 3.88/0.97  cnf(c_12381,plain,
% 3.88/0.97      ( r2_hidden(sK1(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6))),k4_xboole_0(X0,X1))
% 3.88/0.97      | r2_hidden(sK1(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6))),k4_xboole_0(sK4,sK5))
% 3.88/0.97      | r2_hidden(sK1(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6))),k3_xboole_0(sK4,sK6))
% 3.88/0.97      | ~ r1_tarski(X1,k4_xboole_0(sK5,sK6))
% 3.88/0.97      | ~ r1_tarski(sK4,X0) ),
% 3.88/0.97      inference(resolution,[status(thm)],[c_2597,c_7551]) ).
% 3.88/0.97  
% 3.88/0.97  cnf(c_18,plain,
% 3.88/0.97      ( ~ r2_hidden(X0,X1)
% 3.88/0.97      | r2_hidden(X0,X2)
% 3.88/0.97      | r2_hidden(X0,k4_xboole_0(X1,X2)) ),
% 3.88/0.97      inference(cnf_transformation,[],[f64]) ).
% 3.88/0.97  
% 3.88/0.97  cnf(c_1431,plain,
% 3.88/0.97      ( r2_hidden(sK1(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6))),X0)
% 3.88/0.97      | r2_hidden(sK1(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6))),k4_xboole_0(sK4,X0))
% 3.88/0.97      | ~ r2_hidden(sK1(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6))),sK4) ),
% 3.88/0.97      inference(instantiation,[status(thm)],[c_18]) ).
% 3.88/0.97  
% 3.88/0.97  cnf(c_2698,plain,
% 3.88/0.97      ( r2_hidden(sK1(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6))),k4_xboole_0(sK4,sK5))
% 3.88/0.97      | r2_hidden(sK1(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6))),sK5)
% 3.88/0.97      | ~ r2_hidden(sK1(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6))),sK4) ),
% 3.88/0.97      inference(instantiation,[status(thm)],[c_1431]) ).
% 3.88/0.97  
% 3.88/0.97  cnf(c_12,plain,
% 3.88/0.97      ( ~ r2_hidden(X0,X1)
% 3.88/0.97      | ~ r2_hidden(X0,X2)
% 3.88/0.97      | r2_hidden(X0,k3_xboole_0(X2,X1)) ),
% 3.88/0.97      inference(cnf_transformation,[],[f61]) ).
% 3.88/0.97  
% 3.88/0.97  cnf(c_1448,plain,
% 3.88/0.97      ( ~ r2_hidden(sK1(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6))),X0)
% 3.88/0.97      | r2_hidden(sK1(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6))),k3_xboole_0(sK4,X0))
% 3.88/0.97      | ~ r2_hidden(sK1(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6))),sK4) ),
% 3.88/0.97      inference(instantiation,[status(thm)],[c_12]) ).
% 3.88/0.97  
% 3.88/0.97  cnf(c_2709,plain,
% 3.88/0.97      ( r2_hidden(sK1(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6))),k3_xboole_0(sK4,sK6))
% 3.88/0.97      | ~ r2_hidden(sK1(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6))),sK6)
% 3.88/0.97      | ~ r2_hidden(sK1(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6))),sK4) ),
% 3.88/0.97      inference(instantiation,[status(thm)],[c_1448]) ).
% 3.88/0.97  
% 3.88/0.97  cnf(c_20,plain,
% 3.88/0.97      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
% 3.88/0.97      inference(cnf_transformation,[],[f66]) ).
% 3.88/0.97  
% 3.88/0.97  cnf(c_7696,plain,
% 3.88/0.97      ( r2_hidden(sK1(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6))),k4_xboole_0(sK4,sK5))
% 3.88/0.97      | r2_hidden(sK1(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6))),k3_xboole_0(sK4,sK6))
% 3.88/0.97      | r2_hidden(sK1(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6))),sK4) ),
% 3.88/0.97      inference(resolution,[status(thm)],[c_7551,c_20]) ).
% 3.88/0.97  
% 3.88/0.97  cnf(c_14,plain,
% 3.88/0.97      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k3_xboole_0(X1,X2)) ),
% 3.88/0.97      inference(cnf_transformation,[],[f63]) ).
% 3.88/0.97  
% 3.88/0.97  cnf(c_874,plain,
% 3.88/0.97      ( ~ r2_hidden(sK1(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6))),k3_xboole_0(sK4,sK6))
% 3.88/0.97      | r2_hidden(sK1(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6))),sK4) ),
% 3.88/0.97      inference(instantiation,[status(thm)],[c_14]) ).
% 3.88/0.97  
% 3.88/0.97  cnf(c_1051,plain,
% 3.88/0.97      ( ~ r2_hidden(sK1(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6))),k4_xboole_0(sK4,sK5))
% 3.88/0.97      | r2_hidden(sK1(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6))),sK4) ),
% 3.88/0.97      inference(instantiation,[status(thm)],[c_20]) ).
% 3.88/0.97  
% 3.88/0.97  cnf(c_7861,plain,
% 3.88/0.97      ( r2_hidden(sK1(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6))),sK4) ),
% 3.88/0.97      inference(global_propositional_subsumption,
% 3.88/0.97                [status(thm)],
% 3.88/0.97                [c_7696,c_874,c_1051]) ).
% 3.88/0.97  
% 3.88/0.97  cnf(c_19,plain,
% 3.88/0.97      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
% 3.88/0.97      inference(cnf_transformation,[],[f65]) ).
% 3.88/0.97  
% 3.88/0.97  cnf(c_7694,plain,
% 3.88/0.97      ( ~ r2_hidden(sK1(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6))),k4_xboole_0(sK5,sK6))
% 3.88/0.97      | r2_hidden(sK1(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6))),k4_xboole_0(sK4,sK5))
% 3.88/0.97      | r2_hidden(sK1(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6))),k3_xboole_0(sK4,sK6)) ),
% 3.88/0.97      inference(resolution,[status(thm)],[c_7551,c_19]) ).
% 3.88/0.97  
% 3.88/0.97  cnf(c_8369,plain,
% 3.88/0.97      ( r2_hidden(sK1(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6))),k4_xboole_0(sK4,sK5))
% 3.88/0.97      | r2_hidden(sK1(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6))),k3_xboole_0(sK4,sK6))
% 3.88/0.97      | r2_hidden(sK1(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6))),sK6)
% 3.88/0.97      | ~ r2_hidden(sK1(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6))),sK5) ),
% 3.88/0.97      inference(resolution,[status(thm)],[c_7694,c_18]) ).
% 3.88/0.97  
% 3.88/0.97  cnf(c_13,plain,
% 3.88/0.97      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k3_xboole_0(X2,X1)) ),
% 3.88/0.97      inference(cnf_transformation,[],[f62]) ).
% 3.88/0.97  
% 3.88/0.97  cnf(c_871,plain,
% 3.88/0.97      ( ~ r2_hidden(sK1(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6))),k3_xboole_0(sK4,sK6))
% 3.88/0.97      | r2_hidden(sK1(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6))),sK6) ),
% 3.88/0.97      inference(instantiation,[status(thm)],[c_13]) ).
% 3.88/0.97  
% 3.88/0.97  cnf(c_1048,plain,
% 3.88/0.97      ( ~ r2_hidden(sK1(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6))),k4_xboole_0(sK4,sK5))
% 3.88/0.97      | ~ r2_hidden(sK1(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6))),sK5) ),
% 3.88/0.97      inference(instantiation,[status(thm)],[c_19]) ).
% 3.88/0.97  
% 3.88/0.97  cnf(c_8372,plain,
% 3.88/0.97      ( r2_hidden(sK1(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6))),sK6)
% 3.88/0.97      | ~ r2_hidden(sK1(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6))),sK5) ),
% 3.88/0.97      inference(global_propositional_subsumption,
% 3.88/0.97                [status(thm)],
% 3.88/0.97                [c_8369,c_871,c_1048]) ).
% 3.88/0.97  
% 3.88/0.97  cnf(c_12768,plain,
% 3.88/0.97      ( r2_hidden(sK1(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6))),k4_xboole_0(sK4,sK5))
% 3.88/0.97      | r2_hidden(sK1(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6))),k3_xboole_0(sK4,sK6)) ),
% 3.88/0.97      inference(global_propositional_subsumption,
% 3.88/0.97                [status(thm)],
% 3.88/0.97                [c_12381,c_874,c_1051,c_2698,c_2709,c_7696,c_8372]) ).
% 3.88/0.97  
% 3.88/0.97  cnf(c_4,plain,
% 3.88/0.97      ( ~ r2_hidden(sK1(X0,X1,X2),X2)
% 3.88/0.97      | ~ r2_hidden(sK1(X0,X1,X2),X0)
% 3.88/0.97      | k2_xboole_0(X0,X1) = X2 ),
% 3.88/0.97      inference(cnf_transformation,[],[f41]) ).
% 3.88/0.97  
% 3.88/0.97  cnf(c_13268,plain,
% 3.88/0.97      ( ~ r2_hidden(sK1(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6))),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6)))
% 3.88/0.97      | r2_hidden(sK1(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6))),k3_xboole_0(sK4,sK6))
% 3.88/0.97      | k2_xboole_0(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6)) = k4_xboole_0(sK4,k4_xboole_0(sK5,sK6)) ),
% 3.88/0.97      inference(resolution,[status(thm)],[c_12768,c_4]) ).
% 3.88/0.97  
% 3.88/0.97  cnf(c_3,plain,
% 3.88/0.97      ( ~ r2_hidden(sK1(X0,X1,X2),X1)
% 3.88/0.97      | ~ r2_hidden(sK1(X0,X1,X2),X2)
% 3.88/0.97      | k2_xboole_0(X0,X1) = X2 ),
% 3.88/0.97      inference(cnf_transformation,[],[f42]) ).
% 3.88/0.97  
% 3.88/0.97  cnf(c_914,plain,
% 3.88/0.97      ( ~ r2_hidden(sK1(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6))),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6)))
% 3.88/0.97      | ~ r2_hidden(sK1(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6))),k3_xboole_0(sK4,sK6))
% 3.88/0.97      | k2_xboole_0(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6)) = k4_xboole_0(sK4,k4_xboole_0(sK5,sK6)) ),
% 3.88/0.97      inference(instantiation,[status(thm)],[c_3]) ).
% 3.88/0.97  
% 3.88/0.97  cnf(c_13668,plain,
% 3.88/0.97      ( ~ r2_hidden(sK1(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6))),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6))) ),
% 3.88/0.97      inference(global_propositional_subsumption,
% 3.88/0.97                [status(thm)],
% 3.88/0.97                [c_13268,c_23,c_914]) ).
% 3.88/0.97  
% 3.88/0.97  cnf(c_13681,plain,
% 3.88/0.97      ( r2_hidden(sK1(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6))),k4_xboole_0(sK5,sK6))
% 3.88/0.97      | ~ r2_hidden(sK1(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6))),sK4) ),
% 3.88/0.97      inference(resolution,[status(thm)],[c_13668,c_18]) ).
% 3.88/0.97  
% 3.88/0.97  cnf(c_2695,plain,
% 3.88/0.97      ( r2_hidden(sK1(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6))),k4_xboole_0(sK5,sK6))
% 3.88/0.97      | r2_hidden(sK1(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6))),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6)))
% 3.88/0.97      | ~ r2_hidden(sK1(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6))),sK4) ),
% 3.88/0.97      inference(instantiation,[status(thm)],[c_1431]) ).
% 3.88/0.97  
% 3.88/0.97  cnf(c_14509,plain,
% 3.88/0.97      ( r2_hidden(sK1(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6))),k4_xboole_0(sK5,sK6)) ),
% 3.88/0.97      inference(global_propositional_subsumption,
% 3.88/0.97                [status(thm)],
% 3.88/0.97                [c_13681,c_23,c_874,c_914,c_1051,c_2695,c_7696,c_13268]) ).
% 3.88/0.97  
% 3.88/0.97  cnf(c_14521,plain,
% 3.88/0.97      ( ~ r2_hidden(sK1(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6))),sK6) ),
% 3.88/0.97      inference(resolution,[status(thm)],[c_14509,c_19]) ).
% 3.88/0.97  
% 3.88/0.97  cnf(c_13275,plain,
% 3.88/0.97      ( r2_hidden(sK1(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6))),k4_xboole_0(X0,X1))
% 3.88/0.97      | r2_hidden(sK1(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6))),k3_xboole_0(sK4,sK6))
% 3.88/0.97      | ~ r1_tarski(X1,sK5)
% 3.88/0.97      | ~ r1_tarski(sK4,X0) ),
% 3.88/0.97      inference(resolution,[status(thm)],[c_12768,c_2597]) ).
% 3.88/0.97  
% 3.88/0.97  cnf(c_13683,plain,
% 3.88/0.97      ( r2_hidden(sK1(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6))),k3_xboole_0(sK4,sK6))
% 3.88/0.97      | ~ r1_tarski(k4_xboole_0(sK5,sK6),sK5)
% 3.88/0.97      | ~ r1_tarski(sK4,sK4) ),
% 3.88/0.97      inference(resolution,[status(thm)],[c_13668,c_13275]) ).
% 3.88/0.97  
% 3.88/0.97  cnf(c_1,plain,
% 3.88/0.97      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 3.88/0.97      inference(cnf_transformation,[],[f35]) ).
% 3.88/0.97  
% 3.88/0.97  cnf(c_583,plain,
% 3.88/0.97      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 3.88/0.97      | r1_tarski(X0,X1) = iProver_top ),
% 3.88/0.97      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.88/0.97  
% 3.88/0.97  cnf(c_0,plain,
% 3.88/0.97      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 3.88/0.97      inference(cnf_transformation,[],[f36]) ).
% 3.88/0.97  
% 3.88/0.97  cnf(c_584,plain,
% 3.88/0.97      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 3.88/0.97      | r1_tarski(X0,X1) = iProver_top ),
% 3.88/0.97      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.88/0.97  
% 3.88/0.97  cnf(c_1061,plain,
% 3.88/0.97      ( r1_tarski(X0,X0) = iProver_top ),
% 3.88/0.97      inference(superposition,[status(thm)],[c_583,c_584]) ).
% 3.88/0.97  
% 3.88/0.97  cnf(c_1079,plain,
% 3.88/0.97      ( r1_tarski(X0,X0) ),
% 3.88/0.97      inference(predicate_to_equality_rev,[status(thm)],[c_1061]) ).
% 3.88/0.97  
% 3.88/0.97  cnf(c_1081,plain,
% 3.88/0.97      ( r1_tarski(sK4,sK4) ),
% 3.88/0.97      inference(instantiation,[status(thm)],[c_1079]) ).
% 3.88/0.97  
% 3.88/0.97  cnf(c_13686,plain,
% 3.88/0.97      ( ~ r1_tarski(k4_xboole_0(sK5,sK6),sK5)
% 3.88/0.97      | r2_hidden(sK1(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6))),k3_xboole_0(sK4,sK6)) ),
% 3.88/0.97      inference(global_propositional_subsumption,
% 3.88/0.97                [status(thm)],
% 3.88/0.97                [c_13683,c_1081]) ).
% 3.88/0.97  
% 3.88/0.97  cnf(c_13687,plain,
% 3.88/0.97      ( r2_hidden(sK1(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6))),k3_xboole_0(sK4,sK6))
% 3.88/0.97      | ~ r1_tarski(k4_xboole_0(sK5,sK6),sK5) ),
% 3.88/0.97      inference(renaming,[status(thm)],[c_13686]) ).
% 3.88/0.97  
% 3.88/0.97  cnf(c_22,plain,
% 3.88/0.97      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 3.88/0.97      inference(cnf_transformation,[],[f56]) ).
% 3.88/0.97  
% 3.88/0.97  cnf(c_13692,plain,
% 3.88/0.97      ( r2_hidden(sK1(k4_xboole_0(sK4,sK5),k3_xboole_0(sK4,sK6),k4_xboole_0(sK4,k4_xboole_0(sK5,sK6))),k3_xboole_0(sK4,sK6)) ),
% 3.88/0.97      inference(forward_subsumption_resolution,
% 3.88/0.97                [status(thm)],
% 3.88/0.97                [c_13687,c_22]) ).
% 3.88/0.97  
% 3.88/0.97  cnf(contradiction,plain,
% 3.88/0.97      ( $false ),
% 3.88/0.97      inference(minisat,[status(thm)],[c_14521,c_13692,c_871]) ).
% 3.88/0.97  
% 3.88/0.97  
% 3.88/0.97  % SZS output end CNFRefutation for theBenchmark.p
% 3.88/0.97  
% 3.88/0.97  ------                               Statistics
% 3.88/0.97  
% 3.88/0.97  ------ Selected
% 3.88/0.97  
% 3.88/0.97  total_time:                             0.427
% 3.88/0.97  
%------------------------------------------------------------------------------
