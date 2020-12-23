%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0060+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:16 EST 2020

% Result     : Theorem 51.18s
% Output     : CNFRefutation 51.18s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 197 expanded)
%              Number of clauses        :   46 (  51 expanded)
%              Number of leaves         :   18 (  42 expanded)
%              Depth                    :   11
%              Number of atoms          :  465 (1132 expanded)
%              Number of equality atoms :   65 ( 150 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f181,plain,(
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

fof(f182,plain,(
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
    inference(flattening,[],[f181])).

fof(f183,plain,(
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
    inference(rectify,[],[f182])).

fof(f184,plain,(
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

fof(f185,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f183,f184])).

fof(f240,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f185])).

fof(f423,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f240])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f171,plain,(
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

fof(f172,plain,(
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
    inference(flattening,[],[f171])).

fof(f173,plain,(
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
    inference(rectify,[],[f172])).

fof(f174,plain,(
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

fof(f175,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f173,f174])).

fof(f227,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f175])).

fof(f418,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f227])).

fof(f89,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f340,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f89])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f218,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f111,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f167,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f111])).

fof(f168,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f167])).

fof(f169,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f170,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f168,f169])).

fof(f224,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f170])).

fof(f72,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f322,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f72])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f176,plain,(
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

fof(f177,plain,(
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
    inference(flattening,[],[f176])).

fof(f178,plain,(
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
    inference(rectify,[],[f177])).

fof(f179,plain,(
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

fof(f180,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f178,f179])).

fof(f233,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f180])).

fof(f86,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f337,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f86])).

fof(f360,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f233,f337])).

fof(f421,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f360])).

fof(f234,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f180])).

fof(f359,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f234,f337])).

fof(f420,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f359])).

fof(f82,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f154,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f82])).

fof(f333,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f154])).

fof(f239,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f185])).

fof(f424,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f239])).

fof(f241,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f185])).

fof(f422,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f241])).

fof(f228,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f175])).

fof(f417,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f228])).

fof(f70,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f148,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f70])).

fof(f320,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f148])).

fof(f235,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f180])).

fof(f358,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f235,f337])).

fof(f419,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f358])).

fof(f30,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f117,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f192,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f117])).

fof(f193,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK7(X0,X1),X1)
          | ~ r2_hidden(sK7(X0,X1),X0) )
        & ( r2_hidden(sK7(X0,X1),X1)
          | r2_hidden(sK7(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f194,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK7(X0,X1),X1)
          | ~ r2_hidden(sK7(X0,X1),X0) )
        & ( r2_hidden(sK7(X0,X1),X1)
          | r2_hidden(sK7(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f192,f193])).

fof(f263,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r2_hidden(sK7(X0,X1),X1)
      | ~ r2_hidden(sK7(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f194])).

fof(f262,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK7(X0,X1),X1)
      | r2_hidden(sK7(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f194])).

fof(f93,conjecture,(
    ! [X0,X1,X2] : k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f94,negated_conjecture,(
    ~ ! [X0,X1,X2] : k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(negated_conjecture,[],[f93])).

fof(f156,plain,(
    ? [X0,X1,X2] : k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) != k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(ennf_transformation,[],[f94])).

fof(f214,plain,
    ( ? [X0,X1,X2] : k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) != k4_xboole_0(X0,k2_xboole_0(X1,X2))
   => k3_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,sK17)) != k4_xboole_0(sK15,k2_xboole_0(sK16,sK17)) ),
    introduced(choice_axiom,[])).

fof(f215,plain,(
    k3_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,sK17)) != k4_xboole_0(sK15,k2_xboole_0(sK16,sK17)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15,sK16,sK17])],[f156,f214])).

fof(f344,plain,(
    k3_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,sK17)) != k4_xboole_0(sK15,k2_xboole_0(sK16,sK17)) ),
    inference(cnf_transformation,[],[f215])).

fof(f414,plain,(
    k4_xboole_0(sK15,k2_xboole_0(sK16,sK17)) != k4_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,sK17))) ),
    inference(definition_unfolding,[],[f344,f337])).

cnf(c_26,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f423])).

cnf(c_213766,plain,
    ( ~ r2_hidden(sK7(k4_xboole_0(sK15,k2_xboole_0(sK16,sK17)),k4_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,sK17)))),k4_xboole_0(sK15,sK17))
    | ~ r2_hidden(sK7(k4_xboole_0(sK15,k2_xboole_0(sK16,sK17)),k4_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,sK17)))),sK17) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_212920,plain,
    ( ~ r2_hidden(sK7(k4_xboole_0(sK15,k2_xboole_0(sK16,sK17)),k4_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,sK17)))),k4_xboole_0(sK15,sK16))
    | ~ r2_hidden(sK7(k4_xboole_0(sK15,k2_xboole_0(sK16,sK17)),k4_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,sK17)))),sK16) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_15,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f418])).

cnf(c_121,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f340])).

cnf(c_2,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f218])).

cnf(c_2070,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k2_xboole_0(X1,X2)) ),
    inference(theory_normalisation,[status(thm)],[c_15,c_121,c_2])).

cnf(c_6718,plain,
    ( r2_hidden(sK7(k4_xboole_0(sK15,k2_xboole_0(sK16,sK17)),k4_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,sK17)))),X0)
    | r2_hidden(sK7(k4_xboole_0(sK15,k2_xboole_0(sK16,sK17)),k4_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,sK17)))),X1)
    | ~ r2_hidden(sK7(k4_xboole_0(sK15,k2_xboole_0(sK16,sK17)),k4_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,sK17)))),k2_xboole_0(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_2070])).

cnf(c_122953,plain,
    ( ~ r2_hidden(sK7(k4_xboole_0(sK15,k2_xboole_0(sK16,sK17)),k4_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,sK17)))),k2_xboole_0(sK16,sK17))
    | r2_hidden(sK7(k4_xboole_0(sK15,k2_xboole_0(sK16,sK17)),k4_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,sK17)))),sK17)
    | r2_hidden(sK7(k4_xboole_0(sK15,k2_xboole_0(sK16,sK17)),k4_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,sK17)))),sK16) ),
    inference(instantiation,[status(thm)],[c_6718])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f224])).

cnf(c_6740,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(sK7(k4_xboole_0(sK15,k2_xboole_0(sK16,sK17)),k4_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,sK17)))),X0)
    | r2_hidden(sK7(k4_xboole_0(sK15,k2_xboole_0(sK16,sK17)),k4_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,sK17)))),X1) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_67623,plain,
    ( ~ r1_tarski(k4_xboole_0(sK15,k2_xboole_0(sK16,sK17)),X0)
    | r2_hidden(sK7(k4_xboole_0(sK15,k2_xboole_0(sK16,sK17)),k4_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,sK17)))),X0)
    | ~ r2_hidden(sK7(k4_xboole_0(sK15,k2_xboole_0(sK16,sK17)),k4_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,sK17)))),k4_xboole_0(sK15,k2_xboole_0(sK16,sK17))) ),
    inference(instantiation,[status(thm)],[c_6740])).

cnf(c_121011,plain,
    ( ~ r1_tarski(k4_xboole_0(sK15,k2_xboole_0(sK16,sK17)),k4_xboole_0(sK15,sK17))
    | ~ r2_hidden(sK7(k4_xboole_0(sK15,k2_xboole_0(sK16,sK17)),k4_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,sK17)))),k4_xboole_0(sK15,k2_xboole_0(sK16,sK17)))
    | r2_hidden(sK7(k4_xboole_0(sK15,k2_xboole_0(sK16,sK17)),k4_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,sK17)))),k4_xboole_0(sK15,sK17)) ),
    inference(instantiation,[status(thm)],[c_67623])).

cnf(c_104,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f322])).

cnf(c_74801,plain,
    ( r1_tarski(k4_xboole_0(sK17,sK16),sK17) ),
    inference(instantiation,[status(thm)],[c_104])).

cnf(c_21,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f421])).

cnf(c_6720,plain,
    ( r2_hidden(sK7(k4_xboole_0(sK15,k2_xboole_0(sK16,sK17)),k4_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,sK17)))),X0)
    | ~ r2_hidden(sK7(k4_xboole_0(sK15,k2_xboole_0(sK16,sK17)),k4_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,sK17)))),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_74599,plain,
    ( ~ r2_hidden(sK7(k4_xboole_0(sK15,k2_xboole_0(sK16,sK17)),k4_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,sK17)))),k4_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,sK17))))
    | r2_hidden(sK7(k4_xboole_0(sK15,k2_xboole_0(sK16,sK17)),k4_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,sK17)))),k4_xboole_0(sK15,sK16)) ),
    inference(instantiation,[status(thm)],[c_6720])).

cnf(c_20,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f420])).

cnf(c_6719,plain,
    ( r2_hidden(sK7(k4_xboole_0(sK15,k2_xboole_0(sK16,sK17)),k4_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,sK17)))),X0)
    | ~ r2_hidden(sK7(k4_xboole_0(sK15,k2_xboole_0(sK16,sK17)),k4_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,sK17)))),k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_74596,plain,
    ( ~ r2_hidden(sK7(k4_xboole_0(sK15,k2_xboole_0(sK16,sK17)),k4_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,sK17)))),k4_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,sK17))))
    | r2_hidden(sK7(k4_xboole_0(sK15,k2_xboole_0(sK16,sK17)),k4_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,sK17)))),k4_xboole_0(sK15,sK17)) ),
    inference(instantiation,[status(thm)],[c_6719])).

cnf(c_115,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X2))
    | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f333])).

cnf(c_8749,plain,
    ( r1_tarski(X0,k2_xboole_0(sK16,sK17))
    | ~ r1_tarski(k4_xboole_0(X0,sK16),sK17) ),
    inference(instantiation,[status(thm)],[c_115])).

cnf(c_48658,plain,
    ( ~ r1_tarski(k4_xboole_0(sK17,sK16),sK17)
    | r1_tarski(sK17,k2_xboole_0(sK16,sK17)) ),
    inference(instantiation,[status(thm)],[c_8749])).

cnf(c_4537,plain,
    ( ~ r1_tarski(X0,sK15)
    | ~ r2_hidden(sK7(k4_xboole_0(sK15,k2_xboole_0(sK16,sK17)),k4_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,sK17)))),X0)
    | r2_hidden(sK7(k4_xboole_0(sK15,k2_xboole_0(sK16,sK17)),k4_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,sK17)))),sK15) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_24693,plain,
    ( ~ r1_tarski(k4_xboole_0(sK15,sK16),sK15)
    | ~ r2_hidden(sK7(k4_xboole_0(sK15,k2_xboole_0(sK16,sK17)),k4_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,sK17)))),k4_xboole_0(sK15,sK16))
    | r2_hidden(sK7(k4_xboole_0(sK15,k2_xboole_0(sK16,sK17)),k4_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,sK17)))),sK15) ),
    inference(instantiation,[status(thm)],[c_4537])).

cnf(c_27,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f424])).

cnf(c_4516,plain,
    ( ~ r2_hidden(sK7(k4_xboole_0(sK15,k2_xboole_0(sK16,sK17)),k4_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,sK17)))),k4_xboole_0(sK15,X0))
    | r2_hidden(sK7(k4_xboole_0(sK15,k2_xboole_0(sK16,sK17)),k4_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,sK17)))),sK15) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_19077,plain,
    ( ~ r2_hidden(sK7(k4_xboole_0(sK15,k2_xboole_0(sK16,sK17)),k4_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,sK17)))),k4_xboole_0(sK15,k2_xboole_0(sK16,sK17)))
    | r2_hidden(sK7(k4_xboole_0(sK15,k2_xboole_0(sK16,sK17)),k4_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,sK17)))),sK15) ),
    inference(instantiation,[status(thm)],[c_4516])).

cnf(c_25,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f422])).

cnf(c_9860,plain,
    ( r2_hidden(sK7(k4_xboole_0(sK15,k2_xboole_0(sK16,sK17)),k4_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,sK17)))),k4_xboole_0(sK15,sK16))
    | r2_hidden(sK7(k4_xboole_0(sK15,k2_xboole_0(sK16,sK17)),k4_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,sK17)))),sK16)
    | ~ r2_hidden(sK7(k4_xboole_0(sK15,k2_xboole_0(sK16,sK17)),k4_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,sK17)))),sK15) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f417])).

cnf(c_5807,plain,
    ( r2_hidden(sK7(k4_xboole_0(sK15,k2_xboole_0(sK16,sK17)),k4_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,sK17)))),k2_xboole_0(sK16,sK17))
    | ~ r2_hidden(sK7(k4_xboole_0(sK15,k2_xboole_0(sK16,sK17)),k4_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,sK17)))),sK16) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_102,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) ),
    inference(cnf_transformation,[],[f320])).

cnf(c_5539,plain,
    ( r1_tarski(k4_xboole_0(sK15,k2_xboole_0(sK16,sK17)),k4_xboole_0(sK15,sK17))
    | ~ r1_tarski(sK17,k2_xboole_0(sK16,sK17)) ),
    inference(instantiation,[status(thm)],[c_102])).

cnf(c_5189,plain,
    ( r1_tarski(k4_xboole_0(sK15,sK16),sK15) ),
    inference(instantiation,[status(thm)],[c_104])).

cnf(c_4719,plain,
    ( ~ r2_hidden(sK7(k4_xboole_0(sK15,k2_xboole_0(sK16,sK17)),k4_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,sK17)))),k4_xboole_0(sK15,k2_xboole_0(sK16,sK17)))
    | ~ r2_hidden(sK7(k4_xboole_0(sK15,k2_xboole_0(sK16,sK17)),k4_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,sK17)))),k2_xboole_0(sK16,sK17)) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_19,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f419])).

cnf(c_4675,plain,
    ( r2_hidden(sK7(k4_xboole_0(sK15,k2_xboole_0(sK16,sK17)),k4_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,sK17)))),k4_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,sK17))))
    | ~ r2_hidden(sK7(k4_xboole_0(sK15,k2_xboole_0(sK16,sK17)),k4_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,sK17)))),k4_xboole_0(sK15,sK17))
    | ~ r2_hidden(sK7(k4_xboole_0(sK15,k2_xboole_0(sK16,sK17)),k4_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,sK17)))),k4_xboole_0(sK15,sK16)) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_4146,plain,
    ( r2_hidden(sK7(k4_xboole_0(sK15,k2_xboole_0(sK16,sK17)),k4_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,sK17)))),k4_xboole_0(sK15,k2_xboole_0(sK16,sK17)))
    | r2_hidden(sK7(k4_xboole_0(sK15,k2_xboole_0(sK16,sK17)),k4_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,sK17)))),k2_xboole_0(sK16,sK17))
    | ~ r2_hidden(sK7(k4_xboole_0(sK15,k2_xboole_0(sK16,sK17)),k4_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,sK17)))),sK15) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_44,plain,
    ( ~ r2_hidden(sK7(X0,X1),X1)
    | ~ r2_hidden(sK7(X0,X1),X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f263])).

cnf(c_3986,plain,
    ( ~ r2_hidden(sK7(k4_xboole_0(sK15,k2_xboole_0(sK16,sK17)),k4_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,sK17)))),k4_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,sK17))))
    | ~ r2_hidden(sK7(k4_xboole_0(sK15,k2_xboole_0(sK16,sK17)),k4_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,sK17)))),k4_xboole_0(sK15,k2_xboole_0(sK16,sK17)))
    | k4_xboole_0(sK15,k2_xboole_0(sK16,sK17)) = k4_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,sK17))) ),
    inference(instantiation,[status(thm)],[c_44])).

cnf(c_45,plain,
    ( r2_hidden(sK7(X0,X1),X1)
    | r2_hidden(sK7(X0,X1),X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f262])).

cnf(c_3987,plain,
    ( r2_hidden(sK7(k4_xboole_0(sK15,k2_xboole_0(sK16,sK17)),k4_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,sK17)))),k4_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,sK17))))
    | r2_hidden(sK7(k4_xboole_0(sK15,k2_xboole_0(sK16,sK17)),k4_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,sK17)))),k4_xboole_0(sK15,k2_xboole_0(sK16,sK17)))
    | k4_xboole_0(sK15,k2_xboole_0(sK16,sK17)) = k4_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,sK17))) ),
    inference(instantiation,[status(thm)],[c_45])).

cnf(c_125,negated_conjecture,
    ( k4_xboole_0(sK15,k2_xboole_0(sK16,sK17)) != k4_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,sK17))) ),
    inference(cnf_transformation,[],[f414])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_213766,c_212920,c_122953,c_121011,c_74801,c_74599,c_74596,c_48658,c_24693,c_19077,c_9860,c_5807,c_5539,c_5189,c_4719,c_4675,c_4146,c_3986,c_3987,c_125])).

%------------------------------------------------------------------------------
