%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:26:15 EST 2020

% Result     : Theorem 4.07s
% Output     : CNFRefutation 4.07s
% Verified   : 
% Statistics : Number of formulae       :  126 (1280 expanded)
%              Number of clauses        :   78 ( 376 expanded)
%              Number of leaves         :   15 ( 328 expanded)
%              Depth                    :   18
%              Number of atoms          :  444 (6261 expanded)
%              Number of equality atoms :  242 (3395 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    5 (   1 average)

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
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f10,plain,(
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
    inference(flattening,[],[f9])).

fof(f11,plain,(
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
    inference(rectify,[],[f10])).

fof(f12,plain,(
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

fof(f13,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f12])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f44,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f32,f31])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f28,f44])).

fof(f6,conjecture,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    inference(negated_conjecture,[],[f6])).

fof(f8,plain,(
    ? [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k2_tarski(X0,X1) ),
    inference(ennf_transformation,[],[f7])).

fof(f23,plain,
    ( ? [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k2_tarski(X0,X1)
   => k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)) != k2_tarski(sK3,sK4) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)) != k2_tarski(sK3,sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f8,f23])).

fof(f43,plain,(
    k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)) != k2_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f24])).

fof(f51,plain,(
    k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))) != k2_tarski(sK3,sK4) ),
    inference(definition_unfolding,[],[f43,f44])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f18])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f19])).

fof(f21,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK2(X0,X1,X2) != X1
            & sK2(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( sK2(X0,X1,X2) = X1
          | sK2(X0,X1,X2) = X0
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK2(X0,X1,X2) != X1
              & sK2(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( sK2(X0,X1,X2) = X1
            | sK2(X0,X1,X2) = X0
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f21])).

fof(f37,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f62,plain,(
    ! [X4,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,k2_tarski(X0,X1)) ) ),
    inference(equality_resolution,[],[f37])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
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
    inference(nnf_transformation,[],[f4])).

fof(f15,plain,(
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
    inference(rectify,[],[f14])).

fof(f16,plain,(
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

fof(f17,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f15,f16])).

fof(f33,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f57,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f33])).

fof(f38,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f60,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f38])).

fof(f61,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_tarski(X4,X1)) ),
    inference(equality_resolution,[],[f60])).

fof(f34,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f55,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f34])).

fof(f56,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f55])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f29,f44])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f30,f44])).

fof(f39,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f58,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f39])).

fof(f59,plain,(
    ! [X4,X0] : r2_hidden(X4,k2_tarski(X0,X4)) ),
    inference(equality_resolution,[],[f58])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1,X2),X1)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | r2_hidden(sK0(X0,X1,X2),X0)
    | k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X2 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_16,negated_conjecture,
    ( k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))) != k2_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_6234,plain,
    ( r2_hidden(sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)),k2_tarski(sK3,sK4))
    | r2_hidden(sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)),k1_tarski(sK4))
    | r2_hidden(sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)),k1_tarski(sK3)) ),
    inference(resolution,[status(thm)],[c_2,c_16])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,k2_tarski(X1,X2))
    | X0 = X1
    | X0 = X2 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_6638,plain,
    ( r2_hidden(sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)),k1_tarski(sK4))
    | r2_hidden(sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)),k1_tarski(sK3))
    | sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)) = sK4
    | sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)) = sK3 ),
    inference(resolution,[status(thm)],[c_6234,c_15])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k1_tarski(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2375,plain,
    ( ~ r2_hidden(sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)),k1_tarski(sK4))
    | sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)) = sK4 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_2523,plain,
    ( ~ r2_hidden(sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)),k1_tarski(X0))
    | sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)) = X0 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_2525,plain,
    ( ~ r2_hidden(sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)),k1_tarski(sK3))
    | sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)) = sK3 ),
    inference(instantiation,[status(thm)],[c_2523])).

cnf(c_6641,plain,
    ( sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)) = sK4
    | sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6638,c_2375,c_2525])).

cnf(c_182,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_6656,plain,
    ( X0 != sK4
    | sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)) = X0
    | sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)) = sK3 ),
    inference(resolution,[status(thm)],[c_6641,c_182])).

cnf(c_181,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_865,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_182,c_181])).

cnf(c_7288,plain,
    ( X0 != sK4
    | sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)) = X0
    | sK3 = sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)) ),
    inference(resolution,[status(thm)],[c_6656,c_865])).

cnf(c_18,plain,
    ( ~ r2_hidden(sK3,k2_tarski(sK3,sK3))
    | sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_14,plain,
    ( r2_hidden(X0,k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_21,plain,
    ( r2_hidden(sK3,k2_tarski(sK3,sK3)) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_8,plain,
    ( r2_hidden(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_185,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_645,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X2,k1_tarski(X2))
    | X0 != X2
    | X1 != k1_tarski(X2) ),
    inference(instantiation,[status(thm)],[c_185])).

cnf(c_945,plain,
    ( ~ r2_hidden(X0,k1_tarski(X0))
    | r2_hidden(X1,k1_tarski(X2))
    | X1 != X0
    | k1_tarski(X2) != k1_tarski(X0) ),
    inference(instantiation,[status(thm)],[c_645])).

cnf(c_1591,plain,
    ( ~ r2_hidden(X0,k1_tarski(X0))
    | r2_hidden(sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)),k1_tarski(sK4))
    | sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)) != X0
    | k1_tarski(sK4) != k1_tarski(X0) ),
    inference(instantiation,[status(thm)],[c_945])).

cnf(c_2871,plain,
    ( X0 != X1
    | X0 = sK4
    | sK4 != X1 ),
    inference(instantiation,[status(thm)],[c_182])).

cnf(c_2872,plain,
    ( sK4 != sK3
    | sK3 = sK4
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_2871])).

cnf(c_4863,plain,
    ( X0 != X1
    | X0 = sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4))
    | sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)) != X1 ),
    inference(instantiation,[status(thm)],[c_182])).

cnf(c_4864,plain,
    ( sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)) != sK3
    | sK3 = sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4))
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_4863])).

cnf(c_7327,plain,
    ( sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)) = sK3
    | sK3 != sK4 ),
    inference(factoring,[status(thm)],[c_6656])).

cnf(c_35,plain,
    ( r2_hidden(sK3,k1_tarski(sK3)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_186,plain,
    ( X0 != X1
    | k1_tarski(X0) = k1_tarski(X1) ),
    theory(equality)).

cnf(c_191,plain,
    ( k1_tarski(sK3) = k1_tarski(sK3)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_186])).

cnf(c_731,plain,
    ( ~ r2_hidden(k2_tarski(sK3,sK4),k1_tarski(X0))
    | k2_tarski(sK3,sK4) = X0 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_809,plain,
    ( ~ r2_hidden(k2_tarski(sK3,sK4),k1_tarski(k2_tarski(sK3,sK4)))
    | k2_tarski(sK3,sK4) = k2_tarski(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_731])).

cnf(c_810,plain,
    ( r2_hidden(k2_tarski(sK3,sK4),k1_tarski(k2_tarski(sK3,sK4))) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X2)
    | ~ r2_hidden(sK0(X0,X1,X2),X0)
    | k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X2 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1183,plain,
    ( ~ r2_hidden(sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)),k2_tarski(sK3,sK4))
    | ~ r2_hidden(sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)),k1_tarski(sK3))
    | k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))) = k2_tarski(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_742,plain,
    ( X0 != X1
    | k2_tarski(sK3,sK4) != X1
    | k2_tarski(sK3,sK4) = X0 ),
    inference(instantiation,[status(thm)],[c_182])).

cnf(c_837,plain,
    ( X0 != k2_tarski(sK3,sK4)
    | k2_tarski(sK3,sK4) = X0
    | k2_tarski(sK3,sK4) != k2_tarski(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_742])).

cnf(c_1308,plain,
    ( k2_tarski(X0,X1) != k2_tarski(sK3,sK4)
    | k2_tarski(sK3,sK4) = k2_tarski(X0,X1)
    | k2_tarski(sK3,sK4) != k2_tarski(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_837])).

cnf(c_1310,plain,
    ( k2_tarski(sK3,sK4) != k2_tarski(sK3,sK4)
    | k2_tarski(sK3,sK4) = k2_tarski(sK3,sK3)
    | k2_tarski(sK3,sK3) != k2_tarski(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_1308])).

cnf(c_187,plain,
    ( X0 != X1
    | X2 != X3
    | k2_tarski(X0,X2) = k2_tarski(X1,X3) ),
    theory(equality)).

cnf(c_1309,plain,
    ( X0 != sK4
    | X1 != sK3
    | k2_tarski(X1,X0) = k2_tarski(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_187])).

cnf(c_1311,plain,
    ( k2_tarski(sK3,sK3) = k2_tarski(sK3,sK4)
    | sK3 != sK4
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1309])).

cnf(c_650,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X2,k2_tarski(X3,X2))
    | X0 != X2
    | X1 != k2_tarski(X3,X2) ),
    inference(instantiation,[status(thm)],[c_185])).

cnf(c_1053,plain,
    ( ~ r2_hidden(X0,k2_tarski(X1,X0))
    | r2_hidden(X2,k2_tarski(X3,X4))
    | X2 != X0
    | k2_tarski(X3,X4) != k2_tarski(X1,X0) ),
    inference(instantiation,[status(thm)],[c_650])).

cnf(c_4095,plain,
    ( ~ r2_hidden(X0,k2_tarski(X1,X0))
    | r2_hidden(sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)),k2_tarski(sK3,sK4))
    | sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)) != X0
    | k2_tarski(sK3,sK4) != k2_tarski(X1,X0) ),
    inference(instantiation,[status(thm)],[c_1053])).

cnf(c_4097,plain,
    ( r2_hidden(sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)),k2_tarski(sK3,sK4))
    | ~ r2_hidden(sK3,k2_tarski(sK3,sK3))
    | sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)) != sK3
    | k2_tarski(sK3,sK4) != k2_tarski(sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_4095])).

cnf(c_4796,plain,
    ( ~ r2_hidden(X0,k1_tarski(X0))
    | r2_hidden(sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)),k1_tarski(sK3))
    | sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)) != X0
    | k1_tarski(sK3) != k1_tarski(X0) ),
    inference(instantiation,[status(thm)],[c_945])).

cnf(c_4798,plain,
    ( r2_hidden(sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)),k1_tarski(sK3))
    | ~ r2_hidden(sK3,k1_tarski(sK3))
    | sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)) != sK3
    | k1_tarski(sK3) != k1_tarski(sK3) ),
    inference(instantiation,[status(thm)],[c_4796])).

cnf(c_6661,plain,
    ( sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)) = sK3
    | sK3 != sK4 ),
    inference(instantiation,[status(thm)],[c_6656])).

cnf(c_8433,plain,
    ( sK3 != sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7327,c_16,c_18,c_21,c_35,c_191,c_809,c_810,c_1183,c_1310,c_1311,c_4097,c_4798,c_6661])).

cnf(c_1177,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_185,c_181])).

cnf(c_875,plain,
    ( X0 != X1
    | k1_tarski(X1) = k1_tarski(X0) ),
    inference(resolution,[status(thm)],[c_865,c_186])).

cnf(c_1403,plain,
    ( ~ r2_hidden(k1_tarski(X0),X1)
    | r2_hidden(k1_tarski(X2),X1)
    | X0 != X2 ),
    inference(resolution,[status(thm)],[c_1177,c_875])).

cnf(c_6652,plain,
    ( ~ r2_hidden(k1_tarski(sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4))),X0)
    | r2_hidden(k1_tarski(sK4),X0)
    | sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)) = sK3 ),
    inference(resolution,[status(thm)],[c_6641,c_1403])).

cnf(c_7038,plain,
    ( r2_hidden(k1_tarski(sK4),k1_tarski(k1_tarski(sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)))))
    | sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)) = sK3 ),
    inference(resolution,[status(thm)],[c_6652,c_8])).

cnf(c_863,plain,
    ( ~ r2_hidden(X0,k1_tarski(X1))
    | X2 != X1
    | X0 = X2 ),
    inference(resolution,[status(thm)],[c_182,c_9])).

cnf(c_1771,plain,
    ( ~ r2_hidden(X0,k1_tarski(k1_tarski(X1)))
    | X1 != X2
    | X0 = k1_tarski(X2) ),
    inference(resolution,[status(thm)],[c_863,c_875])).

cnf(c_9436,plain,
    ( sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)) != X0
    | sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)) = sK3
    | k1_tarski(sK4) = k1_tarski(X0) ),
    inference(resolution,[status(thm)],[c_7038,c_1771])).

cnf(c_6662,plain,
    ( r2_hidden(sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)),X0)
    | ~ r2_hidden(sK4,X0)
    | sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)) = sK3 ),
    inference(resolution,[status(thm)],[c_6641,c_1177])).

cnf(c_6962,plain,
    ( r2_hidden(sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)),X0)
    | ~ r2_hidden(sK4,X0)
    | sK3 = sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)) ),
    inference(resolution,[status(thm)],[c_6662,c_865])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X1)
    | ~ r2_hidden(sK0(X0,X1,X2),X2)
    | k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X2 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_9774,plain,
    ( ~ r2_hidden(sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)),k1_tarski(sK4))
    | ~ r2_hidden(sK4,k2_tarski(sK3,sK4))
    | k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))) = k2_tarski(sK3,sK4)
    | sK3 = sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)) ),
    inference(resolution,[status(thm)],[c_6962,c_0])).

cnf(c_13,plain,
    ( r2_hidden(X0,k2_tarski(X1,X0)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_9978,plain,
    ( r2_hidden(sK4,k2_tarski(X0,sK4)) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_9980,plain,
    ( r2_hidden(sK4,k2_tarski(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_9978])).

cnf(c_6651,plain,
    ( sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)) = sK3
    | sK4 = sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)) ),
    inference(resolution,[status(thm)],[c_6641,c_865])).

cnf(c_6929,plain,
    ( ~ r2_hidden(k1_tarski(sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4))),X0)
    | r2_hidden(k1_tarski(sK3),X0)
    | sK4 = sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)) ),
    inference(resolution,[status(thm)],[c_6651,c_1403])).

cnf(c_6936,plain,
    ( r2_hidden(sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)),X0)
    | ~ r2_hidden(sK3,X0)
    | sK4 = sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)) ),
    inference(resolution,[status(thm)],[c_6651,c_1177])).

cnf(c_9713,plain,
    ( ~ r2_hidden(sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)),k1_tarski(sK3))
    | ~ r2_hidden(sK3,k2_tarski(sK3,sK4))
    | k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))) = k2_tarski(sK3,sK4)
    | sK4 = sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)) ),
    inference(resolution,[status(thm)],[c_6936,c_1])).

cnf(c_9872,plain,
    ( r2_hidden(X0,k2_tarski(X0,sK4)) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_9874,plain,
    ( r2_hidden(sK3,k2_tarski(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_9872])).

cnf(c_10236,plain,
    ( sK4 = sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6929,c_16,c_18,c_21,c_35,c_191,c_4798,c_6651,c_9713,c_9874])).

cnf(c_10563,plain,
    ( X0 != sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4))
    | sK4 = X0 ),
    inference(resolution,[status(thm)],[c_10236,c_182])).

cnf(c_10568,plain,
    ( sK4 = sK3
    | sK3 != sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_10563])).

cnf(c_11354,plain,
    ( X0 != sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7288,c_16,c_18,c_21,c_8,c_35,c_191,c_809,c_810,c_1183,c_1310,c_1311,c_1591,c_2872,c_4097,c_4798,c_4864,c_6656,c_6661,c_9436,c_9774,c_9980,c_10568])).

cnf(c_10554,plain,
    ( sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)) = sK4 ),
    inference(resolution,[status(thm)],[c_10236,c_865])).

cnf(c_11365,plain,
    ( $false ),
    inference(backward_subsumption_resolution,[status(thm)],[c_11354,c_10554])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.14/0.33  % Computer   : n016.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % WCLimit    : 600
% 0.14/0.33  % DateTime   : Tue Dec  1 09:47:19 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 4.07/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.07/1.00  
% 4.07/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 4.07/1.00  
% 4.07/1.00  ------  iProver source info
% 4.07/1.00  
% 4.07/1.00  git: date: 2020-06-30 10:37:57 +0100
% 4.07/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 4.07/1.00  git: non_committed_changes: false
% 4.07/1.00  git: last_make_outside_of_git: false
% 4.07/1.00  
% 4.07/1.00  ------ 
% 4.07/1.00  ------ Parsing...
% 4.07/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 4.07/1.00  
% 4.07/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 4.07/1.00  
% 4.07/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 4.07/1.00  
% 4.07/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.07/1.00  ------ Proving...
% 4.07/1.00  ------ Problem Properties 
% 4.07/1.00  
% 4.07/1.00  
% 4.07/1.00  clauses                                 17
% 4.07/1.00  conjectures                             1
% 4.07/1.00  EPR                                     0
% 4.07/1.00  Horn                                    12
% 4.07/1.00  unary                                   4
% 4.07/1.00  binary                                  3
% 4.07/1.00  lits                                    42
% 4.07/1.00  lits eq                                 18
% 4.07/1.00  fd_pure                                 0
% 4.07/1.00  fd_pseudo                               0
% 4.07/1.00  fd_cond                                 0
% 4.07/1.00  fd_pseudo_cond                          8
% 4.07/1.00  AC symbols                              0
% 4.07/1.00  
% 4.07/1.00  ------ Input Options Time Limit: Unbounded
% 4.07/1.00  
% 4.07/1.00  
% 4.07/1.00  ------ 
% 4.07/1.00  Current options:
% 4.07/1.00  ------ 
% 4.07/1.00  
% 4.07/1.00  
% 4.07/1.00  
% 4.07/1.00  
% 4.07/1.00  ------ Proving...
% 4.07/1.00  
% 4.07/1.00  
% 4.07/1.00  % SZS status Theorem for theBenchmark.p
% 4.07/1.00  
% 4.07/1.00   Resolution empty clause
% 4.07/1.00  
% 4.07/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 4.07/1.00  
% 4.07/1.00  fof(f1,axiom,(
% 4.07/1.00    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 4.07/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.07/1.00  
% 4.07/1.00  fof(f9,plain,(
% 4.07/1.00    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 4.07/1.00    inference(nnf_transformation,[],[f1])).
% 4.07/1.00  
% 4.07/1.00  fof(f10,plain,(
% 4.07/1.00    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 4.07/1.00    inference(flattening,[],[f9])).
% 4.07/1.00  
% 4.07/1.00  fof(f11,plain,(
% 4.07/1.00    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 4.07/1.00    inference(rectify,[],[f10])).
% 4.07/1.00  
% 4.07/1.00  fof(f12,plain,(
% 4.07/1.00    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 4.07/1.00    introduced(choice_axiom,[])).
% 4.07/1.00  
% 4.07/1.00  fof(f13,plain,(
% 4.07/1.00    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 4.07/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f12])).
% 4.07/1.00  
% 4.07/1.00  fof(f28,plain,(
% 4.07/1.00    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 4.07/1.00    inference(cnf_transformation,[],[f13])).
% 4.07/1.00  
% 4.07/1.00  fof(f3,axiom,(
% 4.07/1.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 4.07/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.07/1.00  
% 4.07/1.00  fof(f32,plain,(
% 4.07/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 4.07/1.00    inference(cnf_transformation,[],[f3])).
% 4.07/1.00  
% 4.07/1.00  fof(f2,axiom,(
% 4.07/1.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 4.07/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.07/1.00  
% 4.07/1.00  fof(f31,plain,(
% 4.07/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 4.07/1.00    inference(cnf_transformation,[],[f2])).
% 4.07/1.00  
% 4.07/1.00  fof(f44,plain,(
% 4.07/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 4.07/1.00    inference(definition_unfolding,[],[f32,f31])).
% 4.07/1.00  
% 4.07/1.00  fof(f47,plain,(
% 4.07/1.00    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 4.07/1.00    inference(definition_unfolding,[],[f28,f44])).
% 4.07/1.00  
% 4.07/1.00  fof(f6,conjecture,(
% 4.07/1.00    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1)),
% 4.07/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.07/1.00  
% 4.07/1.00  fof(f7,negated_conjecture,(
% 4.07/1.00    ~! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1)),
% 4.07/1.00    inference(negated_conjecture,[],[f6])).
% 4.07/1.00  
% 4.07/1.00  fof(f8,plain,(
% 4.07/1.00    ? [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k2_tarski(X0,X1)),
% 4.07/1.00    inference(ennf_transformation,[],[f7])).
% 4.07/1.00  
% 4.07/1.00  fof(f23,plain,(
% 4.07/1.00    ? [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k2_tarski(X0,X1) => k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)) != k2_tarski(sK3,sK4)),
% 4.07/1.00    introduced(choice_axiom,[])).
% 4.07/1.00  
% 4.07/1.00  fof(f24,plain,(
% 4.07/1.00    k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)) != k2_tarski(sK3,sK4)),
% 4.07/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f8,f23])).
% 4.07/1.00  
% 4.07/1.00  fof(f43,plain,(
% 4.07/1.00    k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)) != k2_tarski(sK3,sK4)),
% 4.07/1.00    inference(cnf_transformation,[],[f24])).
% 4.07/1.00  
% 4.07/1.00  fof(f51,plain,(
% 4.07/1.00    k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))) != k2_tarski(sK3,sK4)),
% 4.07/1.00    inference(definition_unfolding,[],[f43,f44])).
% 4.07/1.00  
% 4.07/1.00  fof(f5,axiom,(
% 4.07/1.00    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 4.07/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.07/1.00  
% 4.07/1.00  fof(f18,plain,(
% 4.07/1.00    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 4.07/1.00    inference(nnf_transformation,[],[f5])).
% 4.07/1.00  
% 4.07/1.00  fof(f19,plain,(
% 4.07/1.00    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 4.07/1.00    inference(flattening,[],[f18])).
% 4.07/1.00  
% 4.07/1.00  fof(f20,plain,(
% 4.07/1.00    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 4.07/1.00    inference(rectify,[],[f19])).
% 4.07/1.00  
% 4.07/1.00  fof(f21,plain,(
% 4.07/1.00    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK2(X0,X1,X2) != X1 & sK2(X0,X1,X2) != X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (sK2(X0,X1,X2) = X1 | sK2(X0,X1,X2) = X0 | r2_hidden(sK2(X0,X1,X2),X2))))),
% 4.07/1.00    introduced(choice_axiom,[])).
% 4.07/1.00  
% 4.07/1.00  fof(f22,plain,(
% 4.07/1.00    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK2(X0,X1,X2) != X1 & sK2(X0,X1,X2) != X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (sK2(X0,X1,X2) = X1 | sK2(X0,X1,X2) = X0 | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 4.07/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f21])).
% 4.07/1.00  
% 4.07/1.00  fof(f37,plain,(
% 4.07/1.00    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 4.07/1.00    inference(cnf_transformation,[],[f22])).
% 4.07/1.00  
% 4.07/1.00  fof(f62,plain,(
% 4.07/1.00    ( ! [X4,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,k2_tarski(X0,X1))) )),
% 4.07/1.00    inference(equality_resolution,[],[f37])).
% 4.07/1.00  
% 4.07/1.00  fof(f4,axiom,(
% 4.07/1.00    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 4.07/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.07/1.00  
% 4.07/1.00  fof(f14,plain,(
% 4.07/1.00    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 4.07/1.00    inference(nnf_transformation,[],[f4])).
% 4.07/1.00  
% 4.07/1.00  fof(f15,plain,(
% 4.07/1.00    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 4.07/1.00    inference(rectify,[],[f14])).
% 4.07/1.00  
% 4.07/1.00  fof(f16,plain,(
% 4.07/1.00    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1))))),
% 4.07/1.00    introduced(choice_axiom,[])).
% 4.07/1.00  
% 4.07/1.00  fof(f17,plain,(
% 4.07/1.00    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 4.07/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f15,f16])).
% 4.07/1.00  
% 4.07/1.00  fof(f33,plain,(
% 4.07/1.00    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 4.07/1.00    inference(cnf_transformation,[],[f17])).
% 4.07/1.00  
% 4.07/1.00  fof(f57,plain,(
% 4.07/1.00    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k1_tarski(X0))) )),
% 4.07/1.00    inference(equality_resolution,[],[f33])).
% 4.07/1.00  
% 4.07/1.00  fof(f38,plain,(
% 4.07/1.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 4.07/1.00    inference(cnf_transformation,[],[f22])).
% 4.07/1.00  
% 4.07/1.00  fof(f60,plain,(
% 4.07/1.00    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k2_tarski(X4,X1) != X2) )),
% 4.07/1.00    inference(equality_resolution,[],[f38])).
% 4.07/1.00  
% 4.07/1.00  fof(f61,plain,(
% 4.07/1.00    ( ! [X4,X1] : (r2_hidden(X4,k2_tarski(X4,X1))) )),
% 4.07/1.00    inference(equality_resolution,[],[f60])).
% 4.07/1.00  
% 4.07/1.00  fof(f34,plain,(
% 4.07/1.00    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 4.07/1.00    inference(cnf_transformation,[],[f17])).
% 4.07/1.00  
% 4.07/1.00  fof(f55,plain,(
% 4.07/1.00    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_tarski(X3) != X1) )),
% 4.07/1.00    inference(equality_resolution,[],[f34])).
% 4.07/1.00  
% 4.07/1.00  fof(f56,plain,(
% 4.07/1.00    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) )),
% 4.07/1.00    inference(equality_resolution,[],[f55])).
% 4.07/1.00  
% 4.07/1.00  fof(f29,plain,(
% 4.07/1.00    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 4.07/1.00    inference(cnf_transformation,[],[f13])).
% 4.07/1.00  
% 4.07/1.00  fof(f46,plain,(
% 4.07/1.00    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X2 | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 4.07/1.00    inference(definition_unfolding,[],[f29,f44])).
% 4.07/1.00  
% 4.07/1.00  fof(f30,plain,(
% 4.07/1.00    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 4.07/1.00    inference(cnf_transformation,[],[f13])).
% 4.07/1.00  
% 4.07/1.00  fof(f45,plain,(
% 4.07/1.00    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 4.07/1.00    inference(definition_unfolding,[],[f30,f44])).
% 4.07/1.00  
% 4.07/1.00  fof(f39,plain,(
% 4.07/1.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_tarski(X0,X1) != X2) )),
% 4.07/1.00    inference(cnf_transformation,[],[f22])).
% 4.07/1.00  
% 4.07/1.00  fof(f58,plain,(
% 4.07/1.00    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | k2_tarski(X0,X4) != X2) )),
% 4.07/1.00    inference(equality_resolution,[],[f39])).
% 4.07/1.00  
% 4.07/1.00  fof(f59,plain,(
% 4.07/1.00    ( ! [X4,X0] : (r2_hidden(X4,k2_tarski(X0,X4))) )),
% 4.07/1.00    inference(equality_resolution,[],[f58])).
% 4.07/1.00  
% 4.07/1.00  cnf(c_2,plain,
% 4.07/1.00      ( r2_hidden(sK0(X0,X1,X2),X1)
% 4.07/1.00      | r2_hidden(sK0(X0,X1,X2),X2)
% 4.07/1.00      | r2_hidden(sK0(X0,X1,X2),X0)
% 4.07/1.00      | k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X2 ),
% 4.07/1.00      inference(cnf_transformation,[],[f47]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_16,negated_conjecture,
% 4.07/1.00      ( k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))) != k2_tarski(sK3,sK4) ),
% 4.07/1.00      inference(cnf_transformation,[],[f51]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_6234,plain,
% 4.07/1.00      ( r2_hidden(sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)),k2_tarski(sK3,sK4))
% 4.07/1.00      | r2_hidden(sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)),k1_tarski(sK4))
% 4.07/1.00      | r2_hidden(sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)),k1_tarski(sK3)) ),
% 4.07/1.00      inference(resolution,[status(thm)],[c_2,c_16]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_15,plain,
% 4.07/1.00      ( ~ r2_hidden(X0,k2_tarski(X1,X2)) | X0 = X1 | X0 = X2 ),
% 4.07/1.00      inference(cnf_transformation,[],[f62]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_6638,plain,
% 4.07/1.00      ( r2_hidden(sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)),k1_tarski(sK4))
% 4.07/1.00      | r2_hidden(sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)),k1_tarski(sK3))
% 4.07/1.00      | sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)) = sK4
% 4.07/1.00      | sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)) = sK3 ),
% 4.07/1.00      inference(resolution,[status(thm)],[c_6234,c_15]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_9,plain,
% 4.07/1.00      ( ~ r2_hidden(X0,k1_tarski(X1)) | X0 = X1 ),
% 4.07/1.00      inference(cnf_transformation,[],[f57]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_2375,plain,
% 4.07/1.00      ( ~ r2_hidden(sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)),k1_tarski(sK4))
% 4.07/1.00      | sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)) = sK4 ),
% 4.07/1.00      inference(instantiation,[status(thm)],[c_9]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_2523,plain,
% 4.07/1.00      ( ~ r2_hidden(sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)),k1_tarski(X0))
% 4.07/1.00      | sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)) = X0 ),
% 4.07/1.00      inference(instantiation,[status(thm)],[c_9]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_2525,plain,
% 4.07/1.00      ( ~ r2_hidden(sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)),k1_tarski(sK3))
% 4.07/1.00      | sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)) = sK3 ),
% 4.07/1.00      inference(instantiation,[status(thm)],[c_2523]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_6641,plain,
% 4.07/1.00      ( sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)) = sK4
% 4.07/1.00      | sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)) = sK3 ),
% 4.07/1.00      inference(global_propositional_subsumption,
% 4.07/1.00                [status(thm)],
% 4.07/1.00                [c_6638,c_2375,c_2525]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_182,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_6656,plain,
% 4.07/1.00      ( X0 != sK4
% 4.07/1.00      | sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)) = X0
% 4.07/1.00      | sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)) = sK3 ),
% 4.07/1.00      inference(resolution,[status(thm)],[c_6641,c_182]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_181,plain,( X0 = X0 ),theory(equality) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_865,plain,
% 4.07/1.00      ( X0 != X1 | X1 = X0 ),
% 4.07/1.00      inference(resolution,[status(thm)],[c_182,c_181]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_7288,plain,
% 4.07/1.00      ( X0 != sK4
% 4.07/1.00      | sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)) = X0
% 4.07/1.00      | sK3 = sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)) ),
% 4.07/1.00      inference(resolution,[status(thm)],[c_6656,c_865]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_18,plain,
% 4.07/1.00      ( ~ r2_hidden(sK3,k2_tarski(sK3,sK3)) | sK3 = sK3 ),
% 4.07/1.00      inference(instantiation,[status(thm)],[c_15]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_14,plain,
% 4.07/1.00      ( r2_hidden(X0,k2_tarski(X0,X1)) ),
% 4.07/1.00      inference(cnf_transformation,[],[f61]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_21,plain,
% 4.07/1.00      ( r2_hidden(sK3,k2_tarski(sK3,sK3)) ),
% 4.07/1.00      inference(instantiation,[status(thm)],[c_14]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_8,plain,
% 4.07/1.00      ( r2_hidden(X0,k1_tarski(X0)) ),
% 4.07/1.00      inference(cnf_transformation,[],[f56]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_185,plain,
% 4.07/1.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 4.07/1.00      theory(equality) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_645,plain,
% 4.07/1.00      ( r2_hidden(X0,X1)
% 4.07/1.00      | ~ r2_hidden(X2,k1_tarski(X2))
% 4.07/1.00      | X0 != X2
% 4.07/1.00      | X1 != k1_tarski(X2) ),
% 4.07/1.00      inference(instantiation,[status(thm)],[c_185]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_945,plain,
% 4.07/1.00      ( ~ r2_hidden(X0,k1_tarski(X0))
% 4.07/1.00      | r2_hidden(X1,k1_tarski(X2))
% 4.07/1.00      | X1 != X0
% 4.07/1.00      | k1_tarski(X2) != k1_tarski(X0) ),
% 4.07/1.00      inference(instantiation,[status(thm)],[c_645]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_1591,plain,
% 4.07/1.00      ( ~ r2_hidden(X0,k1_tarski(X0))
% 4.07/1.00      | r2_hidden(sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)),k1_tarski(sK4))
% 4.07/1.00      | sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)) != X0
% 4.07/1.00      | k1_tarski(sK4) != k1_tarski(X0) ),
% 4.07/1.00      inference(instantiation,[status(thm)],[c_945]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_2871,plain,
% 4.07/1.00      ( X0 != X1 | X0 = sK4 | sK4 != X1 ),
% 4.07/1.00      inference(instantiation,[status(thm)],[c_182]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_2872,plain,
% 4.07/1.00      ( sK4 != sK3 | sK3 = sK4 | sK3 != sK3 ),
% 4.07/1.00      inference(instantiation,[status(thm)],[c_2871]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_4863,plain,
% 4.07/1.00      ( X0 != X1
% 4.07/1.00      | X0 = sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4))
% 4.07/1.00      | sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)) != X1 ),
% 4.07/1.00      inference(instantiation,[status(thm)],[c_182]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_4864,plain,
% 4.07/1.00      ( sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)) != sK3
% 4.07/1.00      | sK3 = sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4))
% 4.07/1.00      | sK3 != sK3 ),
% 4.07/1.00      inference(instantiation,[status(thm)],[c_4863]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_7327,plain,
% 4.07/1.00      ( sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)) = sK3
% 4.07/1.00      | sK3 != sK4 ),
% 4.07/1.00      inference(factoring,[status(thm)],[c_6656]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_35,plain,
% 4.07/1.00      ( r2_hidden(sK3,k1_tarski(sK3)) ),
% 4.07/1.00      inference(instantiation,[status(thm)],[c_8]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_186,plain,
% 4.07/1.00      ( X0 != X1 | k1_tarski(X0) = k1_tarski(X1) ),
% 4.07/1.00      theory(equality) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_191,plain,
% 4.07/1.00      ( k1_tarski(sK3) = k1_tarski(sK3) | sK3 != sK3 ),
% 4.07/1.00      inference(instantiation,[status(thm)],[c_186]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_731,plain,
% 4.07/1.00      ( ~ r2_hidden(k2_tarski(sK3,sK4),k1_tarski(X0))
% 4.07/1.00      | k2_tarski(sK3,sK4) = X0 ),
% 4.07/1.00      inference(instantiation,[status(thm)],[c_9]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_809,plain,
% 4.07/1.00      ( ~ r2_hidden(k2_tarski(sK3,sK4),k1_tarski(k2_tarski(sK3,sK4)))
% 4.07/1.00      | k2_tarski(sK3,sK4) = k2_tarski(sK3,sK4) ),
% 4.07/1.00      inference(instantiation,[status(thm)],[c_731]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_810,plain,
% 4.07/1.00      ( r2_hidden(k2_tarski(sK3,sK4),k1_tarski(k2_tarski(sK3,sK4))) ),
% 4.07/1.00      inference(instantiation,[status(thm)],[c_8]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_1,plain,
% 4.07/1.00      ( ~ r2_hidden(sK0(X0,X1,X2),X2)
% 4.07/1.00      | ~ r2_hidden(sK0(X0,X1,X2),X0)
% 4.07/1.00      | k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X2 ),
% 4.07/1.00      inference(cnf_transformation,[],[f46]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_1183,plain,
% 4.07/1.00      ( ~ r2_hidden(sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)),k2_tarski(sK3,sK4))
% 4.07/1.00      | ~ r2_hidden(sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)),k1_tarski(sK3))
% 4.07/1.00      | k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))) = k2_tarski(sK3,sK4) ),
% 4.07/1.00      inference(instantiation,[status(thm)],[c_1]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_742,plain,
% 4.07/1.00      ( X0 != X1 | k2_tarski(sK3,sK4) != X1 | k2_tarski(sK3,sK4) = X0 ),
% 4.07/1.00      inference(instantiation,[status(thm)],[c_182]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_837,plain,
% 4.07/1.00      ( X0 != k2_tarski(sK3,sK4)
% 4.07/1.00      | k2_tarski(sK3,sK4) = X0
% 4.07/1.00      | k2_tarski(sK3,sK4) != k2_tarski(sK3,sK4) ),
% 4.07/1.00      inference(instantiation,[status(thm)],[c_742]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_1308,plain,
% 4.07/1.00      ( k2_tarski(X0,X1) != k2_tarski(sK3,sK4)
% 4.07/1.00      | k2_tarski(sK3,sK4) = k2_tarski(X0,X1)
% 4.07/1.00      | k2_tarski(sK3,sK4) != k2_tarski(sK3,sK4) ),
% 4.07/1.00      inference(instantiation,[status(thm)],[c_837]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_1310,plain,
% 4.07/1.00      ( k2_tarski(sK3,sK4) != k2_tarski(sK3,sK4)
% 4.07/1.00      | k2_tarski(sK3,sK4) = k2_tarski(sK3,sK3)
% 4.07/1.00      | k2_tarski(sK3,sK3) != k2_tarski(sK3,sK4) ),
% 4.07/1.00      inference(instantiation,[status(thm)],[c_1308]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_187,plain,
% 4.07/1.00      ( X0 != X1 | X2 != X3 | k2_tarski(X0,X2) = k2_tarski(X1,X3) ),
% 4.07/1.00      theory(equality) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_1309,plain,
% 4.07/1.00      ( X0 != sK4 | X1 != sK3 | k2_tarski(X1,X0) = k2_tarski(sK3,sK4) ),
% 4.07/1.00      inference(instantiation,[status(thm)],[c_187]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_1311,plain,
% 4.07/1.00      ( k2_tarski(sK3,sK3) = k2_tarski(sK3,sK4) | sK3 != sK4 | sK3 != sK3 ),
% 4.07/1.00      inference(instantiation,[status(thm)],[c_1309]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_650,plain,
% 4.07/1.00      ( r2_hidden(X0,X1)
% 4.07/1.00      | ~ r2_hidden(X2,k2_tarski(X3,X2))
% 4.07/1.00      | X0 != X2
% 4.07/1.00      | X1 != k2_tarski(X3,X2) ),
% 4.07/1.00      inference(instantiation,[status(thm)],[c_185]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_1053,plain,
% 4.07/1.00      ( ~ r2_hidden(X0,k2_tarski(X1,X0))
% 4.07/1.00      | r2_hidden(X2,k2_tarski(X3,X4))
% 4.07/1.00      | X2 != X0
% 4.07/1.00      | k2_tarski(X3,X4) != k2_tarski(X1,X0) ),
% 4.07/1.00      inference(instantiation,[status(thm)],[c_650]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_4095,plain,
% 4.07/1.00      ( ~ r2_hidden(X0,k2_tarski(X1,X0))
% 4.07/1.00      | r2_hidden(sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)),k2_tarski(sK3,sK4))
% 4.07/1.00      | sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)) != X0
% 4.07/1.00      | k2_tarski(sK3,sK4) != k2_tarski(X1,X0) ),
% 4.07/1.00      inference(instantiation,[status(thm)],[c_1053]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_4097,plain,
% 4.07/1.00      ( r2_hidden(sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)),k2_tarski(sK3,sK4))
% 4.07/1.00      | ~ r2_hidden(sK3,k2_tarski(sK3,sK3))
% 4.07/1.00      | sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)) != sK3
% 4.07/1.00      | k2_tarski(sK3,sK4) != k2_tarski(sK3,sK3) ),
% 4.07/1.00      inference(instantiation,[status(thm)],[c_4095]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_4796,plain,
% 4.07/1.00      ( ~ r2_hidden(X0,k1_tarski(X0))
% 4.07/1.00      | r2_hidden(sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)),k1_tarski(sK3))
% 4.07/1.00      | sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)) != X0
% 4.07/1.00      | k1_tarski(sK3) != k1_tarski(X0) ),
% 4.07/1.00      inference(instantiation,[status(thm)],[c_945]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_4798,plain,
% 4.07/1.00      ( r2_hidden(sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)),k1_tarski(sK3))
% 4.07/1.00      | ~ r2_hidden(sK3,k1_tarski(sK3))
% 4.07/1.00      | sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)) != sK3
% 4.07/1.00      | k1_tarski(sK3) != k1_tarski(sK3) ),
% 4.07/1.00      inference(instantiation,[status(thm)],[c_4796]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_6661,plain,
% 4.07/1.00      ( sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)) = sK3
% 4.07/1.00      | sK3 != sK4 ),
% 4.07/1.00      inference(instantiation,[status(thm)],[c_6656]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_8433,plain,
% 4.07/1.00      ( sK3 != sK4 ),
% 4.07/1.00      inference(global_propositional_subsumption,
% 4.07/1.00                [status(thm)],
% 4.07/1.00                [c_7327,c_16,c_18,c_21,c_35,c_191,c_809,c_810,c_1183,c_1310,
% 4.07/1.00                 c_1311,c_4097,c_4798,c_6661]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_1177,plain,
% 4.07/1.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X1) | X2 != X0 ),
% 4.07/1.00      inference(resolution,[status(thm)],[c_185,c_181]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_875,plain,
% 4.07/1.00      ( X0 != X1 | k1_tarski(X1) = k1_tarski(X0) ),
% 4.07/1.00      inference(resolution,[status(thm)],[c_865,c_186]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_1403,plain,
% 4.07/1.00      ( ~ r2_hidden(k1_tarski(X0),X1)
% 4.07/1.00      | r2_hidden(k1_tarski(X2),X1)
% 4.07/1.00      | X0 != X2 ),
% 4.07/1.00      inference(resolution,[status(thm)],[c_1177,c_875]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_6652,plain,
% 4.07/1.00      ( ~ r2_hidden(k1_tarski(sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4))),X0)
% 4.07/1.00      | r2_hidden(k1_tarski(sK4),X0)
% 4.07/1.00      | sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)) = sK3 ),
% 4.07/1.00      inference(resolution,[status(thm)],[c_6641,c_1403]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_7038,plain,
% 4.07/1.00      ( r2_hidden(k1_tarski(sK4),k1_tarski(k1_tarski(sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)))))
% 4.07/1.00      | sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)) = sK3 ),
% 4.07/1.00      inference(resolution,[status(thm)],[c_6652,c_8]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_863,plain,
% 4.07/1.00      ( ~ r2_hidden(X0,k1_tarski(X1)) | X2 != X1 | X0 = X2 ),
% 4.07/1.00      inference(resolution,[status(thm)],[c_182,c_9]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_1771,plain,
% 4.07/1.00      ( ~ r2_hidden(X0,k1_tarski(k1_tarski(X1)))
% 4.07/1.00      | X1 != X2
% 4.07/1.00      | X0 = k1_tarski(X2) ),
% 4.07/1.00      inference(resolution,[status(thm)],[c_863,c_875]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_9436,plain,
% 4.07/1.00      ( sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)) != X0
% 4.07/1.00      | sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)) = sK3
% 4.07/1.00      | k1_tarski(sK4) = k1_tarski(X0) ),
% 4.07/1.00      inference(resolution,[status(thm)],[c_7038,c_1771]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_6662,plain,
% 4.07/1.00      ( r2_hidden(sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)),X0)
% 4.07/1.00      | ~ r2_hidden(sK4,X0)
% 4.07/1.00      | sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)) = sK3 ),
% 4.07/1.00      inference(resolution,[status(thm)],[c_6641,c_1177]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_6962,plain,
% 4.07/1.00      ( r2_hidden(sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)),X0)
% 4.07/1.00      | ~ r2_hidden(sK4,X0)
% 4.07/1.00      | sK3 = sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)) ),
% 4.07/1.00      inference(resolution,[status(thm)],[c_6662,c_865]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_0,plain,
% 4.07/1.00      ( ~ r2_hidden(sK0(X0,X1,X2),X1)
% 4.07/1.00      | ~ r2_hidden(sK0(X0,X1,X2),X2)
% 4.07/1.00      | k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X2 ),
% 4.07/1.00      inference(cnf_transformation,[],[f45]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_9774,plain,
% 4.07/1.00      ( ~ r2_hidden(sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)),k1_tarski(sK4))
% 4.07/1.00      | ~ r2_hidden(sK4,k2_tarski(sK3,sK4))
% 4.07/1.00      | k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))) = k2_tarski(sK3,sK4)
% 4.07/1.00      | sK3 = sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)) ),
% 4.07/1.00      inference(resolution,[status(thm)],[c_6962,c_0]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_13,plain,
% 4.07/1.00      ( r2_hidden(X0,k2_tarski(X1,X0)) ),
% 4.07/1.00      inference(cnf_transformation,[],[f59]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_9978,plain,
% 4.07/1.00      ( r2_hidden(sK4,k2_tarski(X0,sK4)) ),
% 4.07/1.00      inference(instantiation,[status(thm)],[c_13]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_9980,plain,
% 4.07/1.00      ( r2_hidden(sK4,k2_tarski(sK3,sK4)) ),
% 4.07/1.00      inference(instantiation,[status(thm)],[c_9978]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_6651,plain,
% 4.07/1.00      ( sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)) = sK3
% 4.07/1.00      | sK4 = sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)) ),
% 4.07/1.00      inference(resolution,[status(thm)],[c_6641,c_865]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_6929,plain,
% 4.07/1.00      ( ~ r2_hidden(k1_tarski(sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4))),X0)
% 4.07/1.00      | r2_hidden(k1_tarski(sK3),X0)
% 4.07/1.00      | sK4 = sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)) ),
% 4.07/1.00      inference(resolution,[status(thm)],[c_6651,c_1403]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_6936,plain,
% 4.07/1.00      ( r2_hidden(sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)),X0)
% 4.07/1.00      | ~ r2_hidden(sK3,X0)
% 4.07/1.00      | sK4 = sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)) ),
% 4.07/1.00      inference(resolution,[status(thm)],[c_6651,c_1177]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_9713,plain,
% 4.07/1.00      ( ~ r2_hidden(sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)),k1_tarski(sK3))
% 4.07/1.00      | ~ r2_hidden(sK3,k2_tarski(sK3,sK4))
% 4.07/1.00      | k5_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK4),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))) = k2_tarski(sK3,sK4)
% 4.07/1.00      | sK4 = sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)) ),
% 4.07/1.00      inference(resolution,[status(thm)],[c_6936,c_1]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_9872,plain,
% 4.07/1.00      ( r2_hidden(X0,k2_tarski(X0,sK4)) ),
% 4.07/1.00      inference(instantiation,[status(thm)],[c_14]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_9874,plain,
% 4.07/1.00      ( r2_hidden(sK3,k2_tarski(sK3,sK4)) ),
% 4.07/1.00      inference(instantiation,[status(thm)],[c_9872]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_10236,plain,
% 4.07/1.00      ( sK4 = sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)) ),
% 4.07/1.00      inference(global_propositional_subsumption,
% 4.07/1.00                [status(thm)],
% 4.07/1.00                [c_6929,c_16,c_18,c_21,c_35,c_191,c_4798,c_6651,c_9713,c_9874]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_10563,plain,
% 4.07/1.00      ( X0 != sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4))
% 4.07/1.00      | sK4 = X0 ),
% 4.07/1.00      inference(resolution,[status(thm)],[c_10236,c_182]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_10568,plain,
% 4.07/1.00      ( sK4 = sK3
% 4.07/1.00      | sK3 != sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)) ),
% 4.07/1.00      inference(instantiation,[status(thm)],[c_10563]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_11354,plain,
% 4.07/1.00      ( X0 != sK4 ),
% 4.07/1.00      inference(global_propositional_subsumption,
% 4.07/1.00                [status(thm)],
% 4.07/1.00                [c_7288,c_16,c_18,c_21,c_8,c_35,c_191,c_809,c_810,c_1183,
% 4.07/1.00                 c_1310,c_1311,c_1591,c_2872,c_4097,c_4798,c_4864,c_6656,
% 4.07/1.00                 c_6661,c_9436,c_9774,c_9980,c_10568]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_10554,plain,
% 4.07/1.00      ( sK0(k1_tarski(sK3),k1_tarski(sK4),k2_tarski(sK3,sK4)) = sK4 ),
% 4.07/1.00      inference(resolution,[status(thm)],[c_10236,c_865]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_11365,plain,
% 4.07/1.00      ( $false ),
% 4.07/1.00      inference(backward_subsumption_resolution,
% 4.07/1.00                [status(thm)],
% 4.07/1.00                [c_11354,c_10554]) ).
% 4.07/1.00  
% 4.07/1.00  
% 4.07/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 4.07/1.00  
% 4.07/1.00  ------                               Statistics
% 4.07/1.00  
% 4.07/1.00  ------ Selected
% 4.07/1.00  
% 4.07/1.00  total_time:                             0.466
% 4.07/1.00  
%------------------------------------------------------------------------------
