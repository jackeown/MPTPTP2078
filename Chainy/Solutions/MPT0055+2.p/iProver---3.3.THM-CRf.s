%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0055+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:15 EST 2020

% Result     : Theorem 15.80s
% Output     : CNFRefutation 15.80s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 100 expanded)
%              Number of clauses        :   24 (  26 expanded)
%              Number of leaves         :   10 (  20 expanded)
%              Depth                    :   10
%              Number of atoms          :  341 ( 714 expanded)
%              Number of equality atoms :   50 (  96 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f175,plain,(
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
    inference(nnf_transformation,[],[f11])).

fof(f176,plain,(
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
    inference(flattening,[],[f175])).

fof(f177,plain,(
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
    inference(rectify,[],[f176])).

fof(f178,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK4(X0,X1,X2),X1)
          | ~ r2_hidden(sK4(X0,X1,X2),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
            & r2_hidden(sK4(X0,X1,X2),X0) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f179,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK4(X0,X1,X2),X1)
            | ~ r2_hidden(sK4(X0,X1,X2),X0)
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
              & r2_hidden(sK4(X0,X1,X2),X0) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f177,f178])).

fof(f234,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f179])).

fof(f376,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f234])).

fof(f235,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f179])).

fof(f375,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f235])).

fof(f29,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f110,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f185,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k5_xboole_0(X1,X2))
        | ( ( r2_hidden(X0,X1)
            | ~ r2_hidden(X0,X2) )
          & ( r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) ) ) )
      & ( ( ( ~ r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) )
          & ( r2_hidden(X0,X2)
            | r2_hidden(X0,X1) ) )
        | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f110])).

fof(f253,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f185])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f239,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f348,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))) ) ),
    inference(definition_unfolding,[],[f253,f239])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f165,plain,(
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
    inference(nnf_transformation,[],[f9])).

fof(f166,plain,(
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
    inference(flattening,[],[f165])).

fof(f167,plain,(
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
    inference(rectify,[],[f166])).

fof(f168,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
            & ~ r2_hidden(sK2(X0,X1,X2),X0) )
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( r2_hidden(sK2(X0,X1,X2),X1)
          | r2_hidden(sK2(X0,X1,X2),X0)
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f169,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
              & ~ r2_hidden(sK2(X0,X1,X2),X0) )
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( r2_hidden(sK2(X0,X1,X2),X1)
            | r2_hidden(sK2(X0,X1,X2),X0)
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f167,f168])).

fof(f222,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f169])).

fof(f370,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f222])).

fof(f233,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f179])).

fof(f377,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f233])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f170,plain,(
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
    inference(nnf_transformation,[],[f10])).

fof(f171,plain,(
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
    inference(flattening,[],[f170])).

fof(f172,plain,(
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
    inference(rectify,[],[f171])).

fof(f173,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
          | ~ r2_hidden(sK3(X0,X1,X2),X0)
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK3(X0,X1,X2),X1)
            & r2_hidden(sK3(X0,X1,X2),X0) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f174,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
            | ~ r2_hidden(sK3(X0,X1,X2),X0)
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK3(X0,X1,X2),X1)
              & r2_hidden(sK3(X0,X1,X2),X0) )
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f172,f173])).

fof(f232,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X0)
      | ~ r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f174])).

fof(f230,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X0)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f174])).

fof(f231,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f174])).

fof(f85,conjecture,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f86,negated_conjecture,(
    ~ ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f85])).

fof(f150,plain,(
    ? [X0,X1] : k3_xboole_0(X0,X1) != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f86])).

fof(f208,plain,
    ( ? [X0,X1] : k3_xboole_0(X0,X1) != k4_xboole_0(X0,k4_xboole_0(X0,X1))
   => k3_xboole_0(sK15,sK16) != k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)) ),
    introduced(choice_axiom,[])).

fof(f209,plain,(
    k3_xboole_0(sK15,sK16) != k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15,sK16])],[f150,f208])).

fof(f330,plain,(
    k3_xboole_0(sK15,sK16) != k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)) ),
    inference(cnf_transformation,[],[f209])).

cnf(c_26,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f376])).

cnf(c_6090,plain,
    ( ~ r2_hidden(sK3(sK15,sK16,k4_xboole_0(sK15,k4_xboole_0(sK15,sK16))),k4_xboole_0(X0,sK16))
    | ~ r2_hidden(sK3(sK15,sK16,k4_xboole_0(sK15,k4_xboole_0(sK15,sK16))),sK16) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_94962,plain,
    ( ~ r2_hidden(sK3(sK15,sK16,k4_xboole_0(sK15,k4_xboole_0(sK15,sK16))),k4_xboole_0(sK15,sK16))
    | ~ r2_hidden(sK3(sK15,sK16,k4_xboole_0(sK15,k4_xboole_0(sK15,sK16))),sK16) ),
    inference(instantiation,[status(thm)],[c_6090])).

cnf(c_25,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f375])).

cnf(c_6145,plain,
    ( r2_hidden(sK3(sK15,sK16,k4_xboole_0(sK15,k4_xboole_0(sK15,sK16))),X0)
    | r2_hidden(sK3(sK15,sK16,k4_xboole_0(sK15,k4_xboole_0(sK15,sK16))),k4_xboole_0(sK15,X0))
    | ~ r2_hidden(sK3(sK15,sK16,k4_xboole_0(sK15,k4_xboole_0(sK15,sK16))),sK15) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_94215,plain,
    ( r2_hidden(sK3(sK15,sK16,k4_xboole_0(sK15,k4_xboole_0(sK15,sK16))),k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)))
    | r2_hidden(sK3(sK15,sK16,k4_xboole_0(sK15,k4_xboole_0(sK15,sK16))),k4_xboole_0(sK15,sK16))
    | ~ r2_hidden(sK3(sK15,sK16,k4_xboole_0(sK15,k4_xboole_0(sK15,sK16))),sK15) ),
    inference(instantiation,[status(thm)],[c_6145])).

cnf(c_42,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f348])).

cnf(c_6141,plain,
    ( ~ r2_hidden(sK3(sK15,sK16,k4_xboole_0(sK15,k4_xboole_0(sK15,sK16))),X0)
    | ~ r2_hidden(sK3(sK15,sK16,k4_xboole_0(sK15,k4_xboole_0(sK15,sK16))),k2_xboole_0(k4_xboole_0(sK15,X0),k4_xboole_0(X0,sK15)))
    | ~ r2_hidden(sK3(sK15,sK16,k4_xboole_0(sK15,k4_xboole_0(sK15,sK16))),sK15) ),
    inference(instantiation,[status(thm)],[c_42])).

cnf(c_15855,plain,
    ( ~ r2_hidden(sK3(sK15,sK16,k4_xboole_0(sK15,k4_xboole_0(sK15,sK16))),k4_xboole_0(sK15,X0))
    | ~ r2_hidden(sK3(sK15,sK16,k4_xboole_0(sK15,k4_xboole_0(sK15,sK16))),k2_xboole_0(k4_xboole_0(sK15,k4_xboole_0(sK15,X0)),k4_xboole_0(k4_xboole_0(sK15,X0),sK15)))
    | ~ r2_hidden(sK3(sK15,sK16,k4_xboole_0(sK15,k4_xboole_0(sK15,sK16))),sK15) ),
    inference(instantiation,[status(thm)],[c_6141])).

cnf(c_82588,plain,
    ( ~ r2_hidden(sK3(sK15,sK16,k4_xboole_0(sK15,k4_xboole_0(sK15,sK16))),k4_xboole_0(sK15,sK16))
    | ~ r2_hidden(sK3(sK15,sK16,k4_xboole_0(sK15,k4_xboole_0(sK15,sK16))),k2_xboole_0(k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)),k4_xboole_0(k4_xboole_0(sK15,sK16),sK15)))
    | ~ r2_hidden(sK3(sK15,sK16,k4_xboole_0(sK15,k4_xboole_0(sK15,sK16))),sK15) ),
    inference(instantiation,[status(thm)],[c_15855])).

cnf(c_10459,plain,
    ( r2_hidden(sK3(sK15,sK16,k4_xboole_0(sK15,k4_xboole_0(sK15,sK16))),k4_xboole_0(sK15,sK16))
    | r2_hidden(sK3(sK15,sK16,k4_xboole_0(sK15,k4_xboole_0(sK15,sK16))),sK16)
    | ~ r2_hidden(sK3(sK15,sK16,k4_xboole_0(sK15,k4_xboole_0(sK15,sK16))),sK15) ),
    inference(instantiation,[status(thm)],[c_6145])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f370])).

cnf(c_5115,plain,
    ( ~ r2_hidden(sK3(sK15,sK16,k4_xboole_0(sK15,k4_xboole_0(sK15,sK16))),k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)))
    | r2_hidden(sK3(sK15,sK16,k4_xboole_0(sK15,k4_xboole_0(sK15,sK16))),k2_xboole_0(k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)),X0)) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_8842,plain,
    ( ~ r2_hidden(sK3(sK15,sK16,k4_xboole_0(sK15,k4_xboole_0(sK15,sK16))),k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)))
    | r2_hidden(sK3(sK15,sK16,k4_xboole_0(sK15,k4_xboole_0(sK15,sK16))),k2_xboole_0(k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)),k4_xboole_0(k4_xboole_0(sK15,sK16),sK15))) ),
    inference(instantiation,[status(thm)],[c_5115])).

cnf(c_27,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f377])).

cnf(c_5171,plain,
    ( ~ r2_hidden(sK3(sK15,sK16,k4_xboole_0(sK15,k4_xboole_0(sK15,sK16))),k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)))
    | r2_hidden(sK3(sK15,sK16,k4_xboole_0(sK15,k4_xboole_0(sK15,sK16))),sK15) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_16,plain,
    ( ~ r2_hidden(sK3(X0,X1,X2),X1)
    | ~ r2_hidden(sK3(X0,X1,X2),X0)
    | ~ r2_hidden(sK3(X0,X1,X2),X2)
    | k3_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f232])).

cnf(c_4751,plain,
    ( ~ r2_hidden(sK3(sK15,sK16,k4_xboole_0(sK15,k4_xboole_0(sK15,sK16))),k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)))
    | ~ r2_hidden(sK3(sK15,sK16,k4_xboole_0(sK15,k4_xboole_0(sK15,sK16))),sK16)
    | ~ r2_hidden(sK3(sK15,sK16,k4_xboole_0(sK15,k4_xboole_0(sK15,sK16))),sK15)
    | k3_xboole_0(sK15,sK16) = k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_18,plain,
    ( r2_hidden(sK3(X0,X1,X2),X0)
    | r2_hidden(sK3(X0,X1,X2),X2)
    | k3_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f230])).

cnf(c_4714,plain,
    ( r2_hidden(sK3(sK15,sK16,k4_xboole_0(sK15,k4_xboole_0(sK15,sK16))),k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)))
    | r2_hidden(sK3(sK15,sK16,k4_xboole_0(sK15,k4_xboole_0(sK15,sK16))),sK15)
    | k3_xboole_0(sK15,sK16) = k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_17,plain,
    ( r2_hidden(sK3(X0,X1,X2),X1)
    | r2_hidden(sK3(X0,X1,X2),X2)
    | k3_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f231])).

cnf(c_4711,plain,
    ( r2_hidden(sK3(sK15,sK16,k4_xboole_0(sK15,k4_xboole_0(sK15,sK16))),k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)))
    | r2_hidden(sK3(sK15,sK16,k4_xboole_0(sK15,k4_xboole_0(sK15,sK16))),sK16)
    | k3_xboole_0(sK15,sK16) = k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_118,negated_conjecture,
    ( k3_xboole_0(sK15,sK16) != k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)) ),
    inference(cnf_transformation,[],[f330])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_94962,c_94215,c_82588,c_10459,c_8842,c_5171,c_4751,c_4714,c_4711,c_118])).

%------------------------------------------------------------------------------
