%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0062+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:22 EST 2020

% Result     : Theorem 3.55s
% Output     : CNFRefutation 3.55s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 500 expanded)
%              Number of clauses        :   40 ( 108 expanded)
%              Number of leaves         :    8 ( 104 expanded)
%              Depth                    :   15
%              Number of atoms          :  379 (3696 expanded)
%              Number of equality atoms :   52 ( 514 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f8,plain,(
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
    inference(flattening,[],[f7])).

fof(f9,plain,(
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
    inference(rectify,[],[f8])).

fof(f10,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            & ~ r2_hidden(sK0(X0,X1,X2),X0) )
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( r2_hidden(sK0(X0,X1,X2),X1)
          | r2_hidden(sK0(X0,X1,X2),X0)
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
              & ~ r2_hidden(sK0(X0,X1,X2),X0) )
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( r2_hidden(sK0(X0,X1,X2),X1)
            | r2_hidden(sK0(X0,X1,X2),X0)
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f10])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f4,conjecture,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f4])).

fof(f6,plain,(
    ? [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f5])).

fof(f22,plain,
    ( ? [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))
   => k2_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3)) != k4_xboole_0(k2_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK4)) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    k2_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3)) != k4_xboole_0(k2_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f6,f22])).

fof(f42,plain,(
    k2_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3)) != k4_xboole_0(k2_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK4)) ),
    inference(cnf_transformation,[],[f23])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
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

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f19,plain,(
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
    inference(rectify,[],[f18])).

fof(f20,plain,(
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

fof(f21,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f19,f20])).

fof(f37,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f50,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f37])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
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

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

fof(f14,plain,(
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
    inference(rectify,[],[f13])).

fof(f15,plain,(
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

fof(f16,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f14,f15])).

fof(f30,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f48,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f30])).

fof(f31,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f47,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f31])).

fof(f32,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f46,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f32])).

fof(f38,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f49,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f38])).

fof(f36,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f51,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f36])).

fof(f26,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f43,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f26])).

fof(f25,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f44,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f25])).

fof(f24,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f45,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f24])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f11])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1,X2),X1)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | r2_hidden(sK0(X0,X1,X2),X0)
    | k2_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f27])).

cnf(c_18,negated_conjecture,
    ( k2_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3)) != k4_xboole_0(k2_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK4)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_5180,plain,
    ( r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),k4_xboole_0(k2_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK4))),k4_xboole_0(k2_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK4)))
    | r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),k4_xboole_0(k2_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK4))),k4_xboole_0(sK4,sK3))
    | r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),k4_xboole_0(k2_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK4))),k4_xboole_0(sK3,sK4)) ),
    inference(resolution,[status(thm)],[c_2,c_18])).

cnf(c_16,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_5473,plain,
    ( r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),k4_xboole_0(k2_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK4))),k4_xboole_0(sK4,sK3))
    | r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),k4_xboole_0(k2_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK4))),k4_xboole_0(sK3,sK4))
    | ~ r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),k4_xboole_0(k2_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK4))),k3_xboole_0(sK3,sK4)) ),
    inference(resolution,[status(thm)],[c_5180,c_16])).

cnf(c_5657,plain,
    ( r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),k4_xboole_0(k2_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK4))),k4_xboole_0(sK3,sK4))
    | ~ r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),k4_xboole_0(k2_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK4))),k3_xboole_0(sK3,sK4))
    | ~ r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),k4_xboole_0(k2_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK4))),sK3) ),
    inference(resolution,[status(thm)],[c_5473,c_16])).

cnf(c_11,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_5912,plain,
    ( r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),k4_xboole_0(k2_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK4))),k4_xboole_0(sK3,sK4))
    | ~ r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),k4_xboole_0(k2_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK4))),k3_xboole_0(sK3,sK4)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5657,c_11])).

cnf(c_6506,plain,
    ( ~ r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),k4_xboole_0(k2_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK4))),k3_xboole_0(sK3,sK4))
    | ~ r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),k4_xboole_0(k2_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK4))),sK4) ),
    inference(resolution,[status(thm)],[c_5912,c_16])).

cnf(c_10,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_9694,plain,
    ( ~ r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),k4_xboole_0(k2_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK4))),k3_xboole_0(sK3,sK4)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6506,c_10])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_11906,plain,
    ( ~ r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),k4_xboole_0(k2_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK4))),sK4)
    | ~ r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),k4_xboole_0(k2_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK4))),sK3) ),
    inference(resolution,[status(thm)],[c_9694,c_9])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_2972,plain,
    ( r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),k4_xboole_0(k2_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK4))),X0)
    | r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),k4_xboole_0(k2_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK4))),k4_xboole_0(sK3,X0))
    | ~ r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),k4_xboole_0(k2_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK4))),sK3) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_11304,plain,
    ( r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),k4_xboole_0(k2_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK4))),k4_xboole_0(sK3,sK4))
    | r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),k4_xboole_0(k2_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK4))),sK4)
    | ~ r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),k4_xboole_0(k2_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK4))),sK3) ),
    inference(instantiation,[status(thm)],[c_2972])).

cnf(c_17,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_5475,plain,
    ( r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),k4_xboole_0(k2_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK4))),k4_xboole_0(sK4,sK3))
    | r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),k4_xboole_0(k2_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK4))),k4_xboole_0(sK3,sK4))
    | r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),k4_xboole_0(k2_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK4))),k2_xboole_0(sK3,sK4)) ),
    inference(resolution,[status(thm)],[c_5180,c_17])).

cnf(c_863,plain,
    ( ~ r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),k4_xboole_0(k2_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK4))),k4_xboole_0(sK4,sK3))
    | r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),k4_xboole_0(k2_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK4))),sK4) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1861,plain,
    ( r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),k4_xboole_0(k2_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK4))),k2_xboole_0(X0,sK4))
    | ~ r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),k4_xboole_0(k2_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK4))),sK4) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1863,plain,
    ( r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),k4_xboole_0(k2_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK4))),k2_xboole_0(sK3,sK4))
    | ~ r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),k4_xboole_0(k2_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK4))),sK4) ),
    inference(instantiation,[status(thm)],[c_1861])).

cnf(c_5482,plain,
    ( r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),k4_xboole_0(k2_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK4))),k4_xboole_0(sK3,sK4))
    | r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),k4_xboole_0(k2_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK4))),k2_xboole_0(sK3,sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5475,c_863,c_1863])).

cnf(c_5502,plain,
    ( r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),k4_xboole_0(k2_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK4))),k2_xboole_0(sK3,sK4))
    | r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),k4_xboole_0(k2_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK4))),sK3) ),
    inference(resolution,[status(thm)],[c_5482,c_17])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_5678,plain,
    ( r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),k4_xboole_0(k2_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK4))),k2_xboole_0(sK3,sK4)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5502,c_4])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_6248,plain,
    ( r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),k4_xboole_0(k2_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK4))),sK4)
    | r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),k4_xboole_0(k2_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK4))),sK3) ),
    inference(resolution,[status(thm)],[c_5678,c_5])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X1)
    | ~ r2_hidden(sK0(X0,X1,X2),X2)
    | k2_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_734,plain,
    ( ~ r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),k4_xboole_0(k2_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK4))),k4_xboole_0(k2_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK4)))
    | ~ r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),k4_xboole_0(k2_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK4))),k4_xboole_0(sK4,sK3))
    | k2_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3)) = k4_xboole_0(k2_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_825,plain,
    ( ~ r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),k4_xboole_0(k2_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK4))),k2_xboole_0(sK3,sK4))
    | r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),k4_xboole_0(k2_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK4))),sK4)
    | r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),k4_xboole_0(k2_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK4))),sK3) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1858,plain,
    ( r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),k4_xboole_0(k2_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK4))),X0)
    | r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),k4_xboole_0(k2_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK4))),k4_xboole_0(sK4,X0))
    | ~ r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),k4_xboole_0(k2_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK4))),sK4) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1875,plain,
    ( r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),k4_xboole_0(k2_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK4))),k4_xboole_0(sK4,sK3))
    | ~ r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),k4_xboole_0(k2_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK4))),sK4)
    | r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),k4_xboole_0(k2_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK4))),sK3) ),
    inference(instantiation,[status(thm)],[c_1858])).

cnf(c_801,plain,
    ( r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),k4_xboole_0(k2_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK4))),X0)
    | r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),k4_xboole_0(k2_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK4))),k4_xboole_0(k2_xboole_0(sK3,sK4),X0))
    | ~ r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),k4_xboole_0(k2_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK4))),k2_xboole_0(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_2608,plain,
    ( r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),k4_xboole_0(k2_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK4))),k4_xboole_0(k2_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK4)))
    | r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),k4_xboole_0(k2_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK4))),k3_xboole_0(sK3,sK4))
    | ~ r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),k4_xboole_0(k2_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK4))),k2_xboole_0(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_801])).

cnf(c_6508,plain,
    ( ~ r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),k4_xboole_0(k2_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK4))),k3_xboole_0(sK3,sK4))
    | r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),k4_xboole_0(k2_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK4))),sK3) ),
    inference(resolution,[status(thm)],[c_5912,c_17])).

cnf(c_6515,plain,
    ( r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),k4_xboole_0(k2_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK4))),sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6248,c_18,c_734,c_825,c_1875,c_2608,c_5678,c_6508])).

cnf(c_1,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X2)
    | ~ r2_hidden(sK0(X0,X1,X2),X0)
    | k2_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_880,plain,
    ( ~ r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),k4_xboole_0(k2_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK4))),k4_xboole_0(k2_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK4)))
    | ~ r2_hidden(sK0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3),k4_xboole_0(k2_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK4))),k4_xboole_0(sK3,sK4))
    | k2_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,sK3)) = k4_xboole_0(k2_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_11906,c_11304,c_9694,c_6515,c_5678,c_2608,c_880,c_18])).


%------------------------------------------------------------------------------
