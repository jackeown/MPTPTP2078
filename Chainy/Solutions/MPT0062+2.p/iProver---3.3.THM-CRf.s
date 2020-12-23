%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0062+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:16 EST 2020

% Result     : Theorem 31.29s
% Output     : CNFRefutation 31.29s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 906 expanded)
%              Number of clauses        :   46 ( 229 expanded)
%              Number of leaves         :   16 ( 209 expanded)
%              Depth                    :   17
%              Number of atoms          :  353 (4170 expanded)
%              Number of equality atoms :   50 ( 657 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f174,plain,(
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
    inference(flattening,[],[f173])).

fof(f175,plain,(
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
    inference(rectify,[],[f174])).

fof(f176,plain,(
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

fof(f177,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f175,f176])).

fof(f232,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X1)
      | r2_hidden(sK2(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f177])).

fof(f95,conjecture,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f96,negated_conjecture,(
    ~ ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f95])).

fof(f158,plain,(
    ? [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f96])).

fof(f216,plain,
    ( ? [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))
   => k2_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(sK16,sK15)) != k4_xboole_0(k2_xboole_0(sK15,sK16),k3_xboole_0(sK15,sK16)) ),
    introduced(choice_axiom,[])).

fof(f217,plain,(
    k2_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(sK16,sK15)) != k4_xboole_0(k2_xboole_0(sK15,sK16),k3_xboole_0(sK15,sK16)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15,sK16])],[f158,f216])).

fof(f348,plain,(
    k2_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(sK16,sK15)) != k4_xboole_0(k2_xboole_0(sK15,sK16),k3_xboole_0(sK15,sK16)) ),
    inference(cnf_transformation,[],[f217])).

fof(f86,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f339,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f86])).

fof(f420,plain,(
    k2_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(sK16,sK15)) != k4_xboole_0(k2_xboole_0(sK15,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK16))) ),
    inference(definition_unfolding,[],[f348,f339])).

fof(f71,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f151,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f71])).

fof(f152,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f151])).

fof(f323,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f152])).

fof(f72,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f324,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f72])).

fof(f82,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f156,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f82])).

fof(f335,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f156])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f113,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f169,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f113])).

fof(f170,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f169])).

fof(f171,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f172,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f170,f171])).

fof(f226,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f172])).

fof(f49,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f299,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f49])).

fof(f386,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f299,f339])).

fof(f100,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f160,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f100])).

fof(f352,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f160])).

fof(f233,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK2(X0,X1,X2),X0)
      | ~ r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f177])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f184,plain,(
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
    inference(flattening,[],[f183])).

fof(f185,plain,(
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
    inference(rectify,[],[f184])).

fof(f186,plain,(
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

fof(f187,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f185,f186])).

fof(f242,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f187])).

fof(f429,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f242])).

fof(f243,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f187])).

fof(f428,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f243])).

fof(f241,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f187])).

fof(f430,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f241])).

fof(f229,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f177])).

fof(f424,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f229])).

fof(f89,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f342,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f89])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f220,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f234,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK2(X0,X1,X2),X1)
      | ~ r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f177])).

fof(f230,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f177])).

fof(f423,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f230])).

cnf(c_12,plain,
    ( r2_hidden(sK2(X0,X1,X2),X1)
    | r2_hidden(sK2(X0,X1,X2),X2)
    | r2_hidden(sK2(X0,X1,X2),X0)
    | k2_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f232])).

cnf(c_127,negated_conjecture,
    ( k2_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(sK16,sK15)) != k4_xboole_0(k2_xboole_0(sK15,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK16))) ),
    inference(cnf_transformation,[],[f420])).

cnf(c_91721,plain,
    ( r2_hidden(sK2(k4_xboole_0(sK15,sK16),k4_xboole_0(sK16,sK15),k4_xboole_0(k2_xboole_0(sK15,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)))),k4_xboole_0(k2_xboole_0(sK15,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK16))))
    | r2_hidden(sK2(k4_xboole_0(sK15,sK16),k4_xboole_0(sK16,sK15),k4_xboole_0(k2_xboole_0(sK15,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)))),k4_xboole_0(sK16,sK15))
    | r2_hidden(sK2(k4_xboole_0(sK15,sK16),k4_xboole_0(sK16,sK15),k4_xboole_0(k2_xboole_0(sK15,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)))),k4_xboole_0(sK15,sK16)) ),
    inference(resolution,[status(thm)],[c_12,c_127])).

cnf(c_103,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X3)
    | r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f323])).

cnf(c_5814,plain,
    ( r1_tarski(k4_xboole_0(sK16,sK15),k4_xboole_0(k2_xboole_0(sK15,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK16))))
    | ~ r1_tarski(k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)),sK15)
    | ~ r1_tarski(sK16,k2_xboole_0(sK15,sK16)) ),
    inference(instantiation,[status(thm)],[c_103])).

cnf(c_104,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f324])).

cnf(c_27237,plain,
    ( r1_tarski(k4_xboole_0(sK16,sK15),sK16) ),
    inference(instantiation,[status(thm)],[c_104])).

cnf(c_115,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X2))
    | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f335])).

cnf(c_27362,plain,
    ( ~ r1_tarski(k4_xboole_0(sK16,sK15),sK16)
    | r1_tarski(sK16,k2_xboole_0(sK15,sK16)) ),
    inference(instantiation,[status(thm)],[c_115])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f226])).

cnf(c_6193,plain,
    ( ~ r1_tarski(k4_xboole_0(sK16,sK15),X0)
    | r2_hidden(sK2(k4_xboole_0(sK15,sK16),k4_xboole_0(sK16,sK15),k4_xboole_0(k2_xboole_0(sK15,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)))),X0)
    | ~ r2_hidden(sK2(k4_xboole_0(sK15,sK16),k4_xboole_0(sK16,sK15),k4_xboole_0(k2_xboole_0(sK15,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)))),k4_xboole_0(sK16,sK15)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_74364,plain,
    ( ~ r1_tarski(k4_xboole_0(sK16,sK15),k4_xboole_0(k2_xboole_0(sK15,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK16))))
    | r2_hidden(sK2(k4_xboole_0(sK15,sK16),k4_xboole_0(sK16,sK15),k4_xboole_0(k2_xboole_0(sK15,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)))),k4_xboole_0(k2_xboole_0(sK15,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK16))))
    | ~ r2_hidden(sK2(k4_xboole_0(sK15,sK16),k4_xboole_0(sK16,sK15),k4_xboole_0(k2_xboole_0(sK15,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)))),k4_xboole_0(sK16,sK15)) ),
    inference(instantiation,[status(thm)],[c_6193])).

cnf(c_79,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f386])).

cnf(c_76023,plain,
    ( r1_tarski(k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)),sK15) ),
    inference(instantiation,[status(thm)],[c_79])).

cnf(c_93181,plain,
    ( r2_hidden(sK2(k4_xboole_0(sK15,sK16),k4_xboole_0(sK16,sK15),k4_xboole_0(k2_xboole_0(sK15,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)))),k4_xboole_0(k2_xboole_0(sK15,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK16))))
    | r2_hidden(sK2(k4_xboole_0(sK15,sK16),k4_xboole_0(sK16,sK15),k4_xboole_0(k2_xboole_0(sK15,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)))),k4_xboole_0(sK15,sK16)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_91721,c_127,c_5177,c_5814,c_27237,c_27362,c_74364,c_76023])).

cnf(c_131,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f352])).

cnf(c_93197,plain,
    ( r2_hidden(sK2(k4_xboole_0(sK15,sK16),k4_xboole_0(sK16,sK15),k4_xboole_0(k2_xboole_0(sK15,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)))),k4_xboole_0(sK15,sK16))
    | ~ v1_xboole_0(k4_xboole_0(k2_xboole_0(sK15,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)))) ),
    inference(resolution,[status(thm)],[c_93181,c_131])).

cnf(c_11,plain,
    ( ~ r2_hidden(sK2(X0,X1,X2),X2)
    | ~ r2_hidden(sK2(X0,X1,X2),X0)
    | k2_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f233])).

cnf(c_94849,plain,
    ( ~ r2_hidden(sK2(k4_xboole_0(sK15,sK16),k4_xboole_0(sK16,sK15),k4_xboole_0(k2_xboole_0(sK15,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)))),k4_xboole_0(k2_xboole_0(sK15,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK16))))
    | ~ v1_xboole_0(k4_xboole_0(k2_xboole_0(sK15,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK16))))
    | k2_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(sK16,sK15)) = k4_xboole_0(k2_xboole_0(sK15,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK16))) ),
    inference(resolution,[status(thm)],[c_93197,c_11])).

cnf(c_12187,plain,
    ( ~ r2_hidden(sK2(k4_xboole_0(sK15,sK16),k4_xboole_0(sK16,sK15),k4_xboole_0(k2_xboole_0(sK15,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)))),k4_xboole_0(k2_xboole_0(sK15,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK16))))
    | ~ r2_hidden(sK2(k4_xboole_0(sK15,sK16),k4_xboole_0(sK16,sK15),k4_xboole_0(k2_xboole_0(sK15,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)))),k4_xboole_0(sK15,sK16))
    | k2_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(sK16,sK15)) = k4_xboole_0(k2_xboole_0(sK15,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK16))) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_26,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f429])).

cnf(c_93211,plain,
    ( ~ r2_hidden(sK2(k4_xboole_0(sK15,sK16),k4_xboole_0(sK16,sK15),k4_xboole_0(k2_xboole_0(sK15,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)))),k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)))
    | r2_hidden(sK2(k4_xboole_0(sK15,sK16),k4_xboole_0(sK16,sK15),k4_xboole_0(k2_xboole_0(sK15,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)))),k4_xboole_0(sK15,sK16)) ),
    inference(resolution,[status(thm)],[c_93181,c_26])).

cnf(c_94882,plain,
    ( ~ r2_hidden(sK2(k4_xboole_0(sK15,sK16),k4_xboole_0(sK16,sK15),k4_xboole_0(k2_xboole_0(sK15,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)))),k4_xboole_0(sK15,k4_xboole_0(sK15,sK16))) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_93211,c_26])).

cnf(c_25,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f428])).

cnf(c_99246,plain,
    ( r2_hidden(sK2(k4_xboole_0(sK15,sK16),k4_xboole_0(sK16,sK15),k4_xboole_0(k2_xboole_0(sK15,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)))),k4_xboole_0(sK15,sK16))
    | ~ r2_hidden(sK2(k4_xboole_0(sK15,sK16),k4_xboole_0(sK16,sK15),k4_xboole_0(k2_xboole_0(sK15,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)))),sK15) ),
    inference(resolution,[status(thm)],[c_94882,c_25])).

cnf(c_27,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f430])).

cnf(c_94853,plain,
    ( r2_hidden(sK2(k4_xboole_0(sK15,sK16),k4_xboole_0(sK16,sK15),k4_xboole_0(k2_xboole_0(sK15,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)))),sK15)
    | ~ v1_xboole_0(k4_xboole_0(k2_xboole_0(sK15,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)))) ),
    inference(resolution,[status(thm)],[c_93197,c_27])).

cnf(c_15,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f424])).

cnf(c_121,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f342])).

cnf(c_2,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f220])).

cnf(c_1683,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k2_xboole_0(X1,X2)) ),
    inference(theory_normalisation,[status(thm)],[c_15,c_121,c_2])).

cnf(c_19596,plain,
    ( ~ r2_hidden(sK2(k4_xboole_0(sK15,sK16),k4_xboole_0(sK16,sK15),k4_xboole_0(k2_xboole_0(sK15,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)))),k2_xboole_0(sK15,sK16))
    | r2_hidden(sK2(k4_xboole_0(sK15,sK16),k4_xboole_0(sK16,sK15),k4_xboole_0(k2_xboole_0(sK15,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)))),sK16)
    | r2_hidden(sK2(k4_xboole_0(sK15,sK16),k4_xboole_0(sK16,sK15),k4_xboole_0(k2_xboole_0(sK15,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)))),sK15) ),
    inference(instantiation,[status(thm)],[c_1683])).

cnf(c_93213,plain,
    ( r2_hidden(sK2(k4_xboole_0(sK15,sK16),k4_xboole_0(sK16,sK15),k4_xboole_0(k2_xboole_0(sK15,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)))),k4_xboole_0(sK15,sK16))
    | r2_hidden(sK2(k4_xboole_0(sK15,sK16),k4_xboole_0(sK16,sK15),k4_xboole_0(k2_xboole_0(sK15,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)))),k2_xboole_0(sK15,sK16)) ),
    inference(resolution,[status(thm)],[c_93181,c_27])).

cnf(c_94877,plain,
    ( r2_hidden(sK2(k4_xboole_0(sK15,sK16),k4_xboole_0(sK16,sK15),k4_xboole_0(k2_xboole_0(sK15,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)))),k2_xboole_0(sK15,sK16))
    | r2_hidden(sK2(k4_xboole_0(sK15,sK16),k4_xboole_0(sK16,sK15),k4_xboole_0(k2_xboole_0(sK15,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)))),sK15) ),
    inference(resolution,[status(thm)],[c_93213,c_27])).

cnf(c_10,plain,
    ( ~ r2_hidden(sK2(X0,X1,X2),X1)
    | ~ r2_hidden(sK2(X0,X1,X2),X2)
    | k2_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f234])).

cnf(c_93209,plain,
    ( ~ r2_hidden(sK2(k4_xboole_0(sK15,sK16),k4_xboole_0(sK16,sK15),k4_xboole_0(k2_xboole_0(sK15,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)))),k4_xboole_0(sK16,sK15))
    | r2_hidden(sK2(k4_xboole_0(sK15,sK16),k4_xboole_0(sK16,sK15),k4_xboole_0(k2_xboole_0(sK15,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)))),k4_xboole_0(sK15,sK16))
    | k2_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(sK16,sK15)) = k4_xboole_0(k2_xboole_0(sK15,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK16))) ),
    inference(resolution,[status(thm)],[c_93181,c_10])).

cnf(c_5177,plain,
    ( ~ r2_hidden(sK2(k4_xboole_0(sK15,sK16),k4_xboole_0(sK16,sK15),k4_xboole_0(k2_xboole_0(sK15,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)))),k4_xboole_0(k2_xboole_0(sK15,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK16))))
    | ~ r2_hidden(sK2(k4_xboole_0(sK15,sK16),k4_xboole_0(sK16,sK15),k4_xboole_0(k2_xboole_0(sK15,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)))),k4_xboole_0(sK16,sK15))
    | k2_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(sK16,sK15)) = k4_xboole_0(k2_xboole_0(sK15,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK16))) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_97942,plain,
    ( ~ r2_hidden(sK2(k4_xboole_0(sK15,sK16),k4_xboole_0(sK16,sK15),k4_xboole_0(k2_xboole_0(sK15,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)))),k4_xboole_0(sK16,sK15)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_93209,c_127,c_5177,c_5814,c_27237,c_27362,c_74364,c_76023])).

cnf(c_97956,plain,
    ( ~ r2_hidden(sK2(k4_xboole_0(sK15,sK16),k4_xboole_0(sK16,sK15),k4_xboole_0(k2_xboole_0(sK15,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)))),sK16)
    | r2_hidden(sK2(k4_xboole_0(sK15,sK16),k4_xboole_0(sK16,sK15),k4_xboole_0(k2_xboole_0(sK15,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)))),sK15) ),
    inference(resolution,[status(thm)],[c_97942,c_25])).

cnf(c_103816,plain,
    ( r2_hidden(sK2(k4_xboole_0(sK15,sK16),k4_xboole_0(sK16,sK15),k4_xboole_0(k2_xboole_0(sK15,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)))),sK15) ),
    inference(global_propositional_subsumption,[status(thm)],[c_94853,c_19596,c_94877,c_97956])).

cnf(c_118604,plain,
    ( ~ r2_hidden(sK2(k4_xboole_0(sK15,sK16),k4_xboole_0(sK16,sK15),k4_xboole_0(k2_xboole_0(sK15,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)))),k4_xboole_0(k2_xboole_0(sK15,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_94849,c_127,c_12187,c_19596,c_94877,c_97956,c_99246])).

cnf(c_119069,plain,
    ( r2_hidden(sK2(k4_xboole_0(sK15,sK16),k4_xboole_0(sK16,sK15),k4_xboole_0(k2_xboole_0(sK15,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)))),k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)))
    | ~ r2_hidden(sK2(k4_xboole_0(sK15,sK16),k4_xboole_0(sK16,sK15),k4_xboole_0(k2_xboole_0(sK15,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)))),k2_xboole_0(sK15,sK16)) ),
    inference(resolution,[status(thm)],[c_118604,c_25])).

cnf(c_158107,plain,
    ( ~ r2_hidden(sK2(k4_xboole_0(sK15,sK16),k4_xboole_0(sK16,sK15),k4_xboole_0(k2_xboole_0(sK15,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)))),k2_xboole_0(sK15,sK16)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_119069,c_94882])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f423])).

cnf(c_162193,plain,
    ( ~ r2_hidden(sK2(k4_xboole_0(sK15,sK16),k4_xboole_0(sK16,sK15),k4_xboole_0(k2_xboole_0(sK15,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)))),sK15) ),
    inference(resolution,[status(thm)],[c_158107,c_14])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_162193,c_103816])).

%------------------------------------------------------------------------------
