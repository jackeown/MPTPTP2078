%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0056+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:16 EST 2020

% Result     : Theorem 31.38s
% Output     : CNFRefutation 31.38s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 602 expanded)
%              Number of clauses        :   42 ( 107 expanded)
%              Number of leaves         :   14 ( 147 expanded)
%              Depth                    :   15
%              Number of atoms          :  406 (3420 expanded)
%              Number of equality atoms :   52 ( 594 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(nnf_transformation,[],[f10])).

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
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f171])).

fof(f173,plain,(
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
    inference(rectify,[],[f172])).

fof(f174,plain,(
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

fof(f175,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f173,f174])).

fof(f230,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f175])).

fof(f85,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f331,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f85])).

fof(f348,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f230,f331])).

fof(f404,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f348])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(nnf_transformation,[],[f11])).

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
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f176])).

fof(f178,plain,(
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
    inference(rectify,[],[f177])).

fof(f179,plain,(
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

fof(f180,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f178,f179])).

fof(f237,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK4(X0,X1,X2),X0)
      | r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f180])).

fof(f86,conjecture,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f87,negated_conjecture,(
    ~ ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(negated_conjecture,[],[f86])).

fof(f151,plain,(
    ? [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) != k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(ennf_transformation,[],[f87])).

fof(f209,plain,
    ( ? [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) != k4_xboole_0(k3_xboole_0(X0,X1),X2)
   => k3_xboole_0(sK15,k4_xboole_0(sK16,sK17)) != k4_xboole_0(k3_xboole_0(sK15,sK16),sK17) ),
    introduced(choice_axiom,[])).

fof(f210,plain,(
    k3_xboole_0(sK15,k4_xboole_0(sK16,sK17)) != k4_xboole_0(k3_xboole_0(sK15,sK16),sK17) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15,sK16,sK17])],[f151,f209])).

fof(f332,plain,(
    k3_xboole_0(sK15,k4_xboole_0(sK16,sK17)) != k4_xboole_0(k3_xboole_0(sK15,sK16),sK17) ),
    inference(cnf_transformation,[],[f210])).

fof(f398,plain,(
    k4_xboole_0(k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)),sK17) != k4_xboole_0(sK15,k4_xboole_0(sK15,k4_xboole_0(sK16,sK17))) ),
    inference(definition_unfolding,[],[f332,f331,f331])).

fof(f229,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f175])).

fof(f349,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f229,f331])).

fof(f405,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f349])).

fof(f235,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f180])).

fof(f408,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f235])).

fof(f238,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK4(X0,X1,X2),X1)
      | r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f180])).

fof(f33,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f102,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f33])).

fof(f115,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f102])).

fof(f195,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK10(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f196,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK10(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f115,f195])).

fof(f267,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f196])).

fof(f364,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(definition_unfolding,[],[f267,f331])).

fof(f234,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f180])).

fof(f409,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f234])).

fof(f236,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f180])).

fof(f407,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f236])).

fof(f228,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f175])).

fof(f350,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f228,f331])).

fof(f406,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f350])).

fof(f32,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f101,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f32])).

fof(f114,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f101])).

fof(f193,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK9(X0,X1),X1)
        & r2_hidden(sK9(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f194,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK9(X0,X1),X1)
          & r2_hidden(sK9(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f114,f193])).

fof(f265,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f194])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f106,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f162,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f106])).

fof(f163,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f162])).

fof(f164,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f165,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f163,f164])).

fof(f219,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f165])).

fof(f239,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK4(X0,X1,X2),X1)
      | ~ r2_hidden(sK4(X0,X1,X2),X0)
      | ~ r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f180])).

fof(f37,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f201,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f202,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f201])).

fof(f275,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f202])).

fof(f411,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f275])).

cnf(c_19,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f404])).

cnf(c_8924,plain,
    ( ~ r2_hidden(sK4(k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)),sK17,k4_xboole_0(sK15,k4_xboole_0(sK15,k4_xboole_0(sK16,sK17)))),X0)
    | r2_hidden(sK4(k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)),sK17,k4_xboole_0(sK15,k4_xboole_0(sK15,k4_xboole_0(sK16,sK17)))),k4_xboole_0(sK15,k4_xboole_0(sK15,X0)))
    | ~ r2_hidden(sK4(k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)),sK17,k4_xboole_0(sK15,k4_xboole_0(sK15,k4_xboole_0(sK16,sK17)))),sK15) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_166700,plain,
    ( r2_hidden(sK4(k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)),sK17,k4_xboole_0(sK15,k4_xboole_0(sK15,k4_xboole_0(sK16,sK17)))),k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)))
    | ~ r2_hidden(sK4(k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)),sK17,k4_xboole_0(sK15,k4_xboole_0(sK15,k4_xboole_0(sK16,sK17)))),sK16)
    | ~ r2_hidden(sK4(k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)),sK17,k4_xboole_0(sK15,k4_xboole_0(sK15,k4_xboole_0(sK16,sK17)))),sK15) ),
    inference(instantiation,[status(thm)],[c_8924])).

cnf(c_24,plain,
    ( r2_hidden(sK4(X0,X1,X2),X0)
    | r2_hidden(sK4(X0,X1,X2),X2)
    | k4_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f237])).

cnf(c_118,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)),sK17) != k4_xboole_0(sK15,k4_xboole_0(sK15,k4_xboole_0(sK16,sK17))) ),
    inference(cnf_transformation,[],[f398])).

cnf(c_47487,plain,
    ( r2_hidden(sK4(k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)),sK17,k4_xboole_0(sK15,k4_xboole_0(sK15,k4_xboole_0(sK16,sK17)))),k4_xboole_0(sK15,k4_xboole_0(sK15,k4_xboole_0(sK16,sK17))))
    | r2_hidden(sK4(k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)),sK17,k4_xboole_0(sK15,k4_xboole_0(sK15,k4_xboole_0(sK16,sK17)))),k4_xboole_0(sK15,k4_xboole_0(sK15,sK16))) ),
    inference(resolution,[status(thm)],[c_24,c_118])).

cnf(c_20,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f405])).

cnf(c_49140,plain,
    ( r2_hidden(sK4(k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)),sK17,k4_xboole_0(sK15,k4_xboole_0(sK15,k4_xboole_0(sK16,sK17)))),k4_xboole_0(sK16,sK17))
    | r2_hidden(sK4(k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)),sK17,k4_xboole_0(sK15,k4_xboole_0(sK15,k4_xboole_0(sK16,sK17)))),k4_xboole_0(sK15,k4_xboole_0(sK15,sK16))) ),
    inference(resolution,[status(thm)],[c_47487,c_20])).

cnf(c_26,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f408])).

cnf(c_53126,plain,
    ( r2_hidden(sK4(k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)),sK17,k4_xboole_0(sK15,k4_xboole_0(sK15,k4_xboole_0(sK16,sK17)))),k4_xboole_0(sK16,sK17))
    | ~ r2_hidden(sK4(k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)),sK17,k4_xboole_0(sK15,k4_xboole_0(sK15,k4_xboole_0(sK16,sK17)))),k4_xboole_0(sK15,sK16)) ),
    inference(resolution,[status(thm)],[c_49140,c_26])).

cnf(c_4836,plain,
    ( r2_hidden(sK4(k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)),sK17,k4_xboole_0(sK15,k4_xboole_0(sK15,k4_xboole_0(sK16,sK17)))),k4_xboole_0(sK16,sK17))
    | ~ r2_hidden(sK4(k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)),sK17,k4_xboole_0(sK15,k4_xboole_0(sK15,k4_xboole_0(sK16,sK17)))),k4_xboole_0(sK15,k4_xboole_0(sK15,k4_xboole_0(sK16,sK17)))) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_23,plain,
    ( ~ r2_hidden(sK4(X0,X1,X2),X1)
    | r2_hidden(sK4(X0,X1,X2),X2)
    | k4_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f238])).

cnf(c_47603,plain,
    ( r2_hidden(sK4(k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)),sK17,k4_xboole_0(sK15,k4_xboole_0(sK15,k4_xboole_0(sK16,sK17)))),k4_xboole_0(sK15,k4_xboole_0(sK15,k4_xboole_0(sK16,sK17))))
    | ~ r2_hidden(sK4(k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)),sK17,k4_xboole_0(sK15,k4_xboole_0(sK15,k4_xboole_0(sK16,sK17)))),sK17)
    | k4_xboole_0(k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)),sK17) = k4_xboole_0(sK15,k4_xboole_0(sK15,k4_xboole_0(sK16,sK17))) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_53,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(cnf_transformation,[],[f364])).

cnf(c_49146,plain,
    ( ~ r1_xboole_0(sK15,k4_xboole_0(sK16,sK17))
    | r2_hidden(sK4(k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)),sK17,k4_xboole_0(sK15,k4_xboole_0(sK15,k4_xboole_0(sK16,sK17)))),k4_xboole_0(sK15,k4_xboole_0(sK15,sK16))) ),
    inference(resolution,[status(thm)],[c_47487,c_53])).

cnf(c_51862,plain,
    ( ~ r1_xboole_0(sK15,k4_xboole_0(sK16,sK17))
    | r2_hidden(sK4(k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)),sK17,k4_xboole_0(sK15,k4_xboole_0(sK15,k4_xboole_0(sK16,sK17)))),sK16) ),
    inference(resolution,[status(thm)],[c_49146,c_20])).

cnf(c_27,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f409])).

cnf(c_14564,plain,
    ( ~ r2_hidden(sK4(k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)),sK17,k4_xboole_0(sK15,k4_xboole_0(sK15,k4_xboole_0(sK16,sK17)))),k4_xboole_0(sK16,sK17))
    | r2_hidden(sK4(k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)),sK17,k4_xboole_0(sK15,k4_xboole_0(sK15,k4_xboole_0(sK16,sK17)))),sK16) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_53124,plain,
    ( r2_hidden(sK4(k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)),sK17,k4_xboole_0(sK15,k4_xboole_0(sK15,k4_xboole_0(sK16,sK17)))),k4_xboole_0(sK16,sK17))
    | r2_hidden(sK4(k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)),sK17,k4_xboole_0(sK15,k4_xboole_0(sK15,k4_xboole_0(sK16,sK17)))),sK16) ),
    inference(resolution,[status(thm)],[c_49140,c_20])).

cnf(c_65809,plain,
    ( r2_hidden(sK4(k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)),sK17,k4_xboole_0(sK15,k4_xboole_0(sK15,k4_xboole_0(sK16,sK17)))),sK16) ),
    inference(global_propositional_subsumption,[status(thm)],[c_51862,c_14564,c_53124])).

cnf(c_25,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f407])).

cnf(c_8759,plain,
    ( r2_hidden(sK4(k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)),sK17,k4_xboole_0(sK15,k4_xboole_0(sK15,k4_xboole_0(sK16,sK17)))),X0)
    | r2_hidden(sK4(k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)),sK17,k4_xboole_0(sK15,k4_xboole_0(sK15,k4_xboole_0(sK16,sK17)))),k4_xboole_0(sK16,X0))
    | ~ r2_hidden(sK4(k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)),sK17,k4_xboole_0(sK15,k4_xboole_0(sK15,k4_xboole_0(sK16,sK17)))),sK16) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_85844,plain,
    ( r2_hidden(sK4(k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)),sK17,k4_xboole_0(sK15,k4_xboole_0(sK15,k4_xboole_0(sK16,sK17)))),k4_xboole_0(sK16,sK17))
    | r2_hidden(sK4(k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)),sK17,k4_xboole_0(sK15,k4_xboole_0(sK15,k4_xboole_0(sK16,sK17)))),sK17)
    | ~ r2_hidden(sK4(k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)),sK17,k4_xboole_0(sK15,k4_xboole_0(sK15,k4_xboole_0(sK16,sK17)))),sK16) ),
    inference(instantiation,[status(thm)],[c_8759])).

cnf(c_94988,plain,
    ( r2_hidden(sK4(k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)),sK17,k4_xboole_0(sK15,k4_xboole_0(sK15,k4_xboole_0(sK16,sK17)))),k4_xboole_0(sK16,sK17)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_53126,c_118,c_4836,c_14564,c_47603,c_53124,c_85844])).

cnf(c_49144,plain,
    ( r2_hidden(sK4(k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)),sK17,k4_xboole_0(sK15,k4_xboole_0(sK15,k4_xboole_0(sK16,sK17)))),k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)))
    | r2_hidden(sK4(k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)),sK17,k4_xboole_0(sK15,k4_xboole_0(sK15,k4_xboole_0(sK16,sK17)))),sK15) ),
    inference(resolution,[status(thm)],[c_47487,c_27])).

cnf(c_21,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f406])).

cnf(c_6007,plain,
    ( ~ r2_hidden(sK4(k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)),sK17,k4_xboole_0(sK15,k4_xboole_0(sK15,k4_xboole_0(sK16,sK17)))),k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)))
    | r2_hidden(sK4(k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)),sK17,k4_xboole_0(sK15,k4_xboole_0(sK15,k4_xboole_0(sK16,sK17)))),sK15) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_53083,plain,
    ( r2_hidden(sK4(k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)),sK17,k4_xboole_0(sK15,k4_xboole_0(sK15,k4_xboole_0(sK16,sK17)))),sK15) ),
    inference(global_propositional_subsumption,[status(thm)],[c_49144,c_6007])).

cnf(c_50,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,X0)
    | ~ r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f265])).

cnf(c_53098,plain,
    ( ~ r1_xboole_0(X0,sK15)
    | ~ r2_hidden(sK4(k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)),sK17,k4_xboole_0(sK15,k4_xboole_0(sK15,k4_xboole_0(sK16,sK17)))),X0) ),
    inference(resolution,[status(thm)],[c_53083,c_50])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f219])).

cnf(c_49136,plain,
    ( ~ r1_tarski(k4_xboole_0(sK15,k4_xboole_0(sK15,k4_xboole_0(sK16,sK17))),X0)
    | r2_hidden(sK4(k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)),sK17,k4_xboole_0(sK15,k4_xboole_0(sK15,k4_xboole_0(sK16,sK17)))),X0)
    | r2_hidden(sK4(k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)),sK17,k4_xboole_0(sK15,k4_xboole_0(sK15,k4_xboole_0(sK16,sK17)))),k4_xboole_0(sK15,k4_xboole_0(sK15,sK16))) ),
    inference(resolution,[status(thm)],[c_47487,c_9])).

cnf(c_63140,plain,
    ( ~ r1_xboole_0(k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)),sK15)
    | ~ r1_tarski(k4_xboole_0(sK15,k4_xboole_0(sK15,k4_xboole_0(sK16,sK17))),X0)
    | r2_hidden(sK4(k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)),sK17,k4_xboole_0(sK15,k4_xboole_0(sK15,k4_xboole_0(sK16,sK17)))),X0) ),
    inference(resolution,[status(thm)],[c_53098,c_49136])).

cnf(c_4826,plain,
    ( ~ r1_tarski(k4_xboole_0(sK15,k4_xboole_0(sK15,k4_xboole_0(sK16,sK17))),X0)
    | r2_hidden(sK4(k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)),sK17,k4_xboole_0(sK15,k4_xboole_0(sK15,k4_xboole_0(sK16,sK17)))),X0)
    | ~ r2_hidden(sK4(k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)),sK17,k4_xboole_0(sK15,k4_xboole_0(sK15,k4_xboole_0(sK16,sK17)))),k4_xboole_0(sK15,k4_xboole_0(sK15,k4_xboole_0(sK16,sK17)))) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_86994,plain,
    ( ~ r2_hidden(sK4(k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)),sK17,k4_xboole_0(sK15,k4_xboole_0(sK15,k4_xboole_0(sK16,sK17)))),k4_xboole_0(sK16,sK17))
    | r2_hidden(sK4(k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)),sK17,k4_xboole_0(sK15,k4_xboole_0(sK15,k4_xboole_0(sK16,sK17)))),k4_xboole_0(sK15,k4_xboole_0(sK15,k4_xboole_0(sK16,sK17))))
    | ~ r2_hidden(sK4(k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)),sK17,k4_xboole_0(sK15,k4_xboole_0(sK15,k4_xboole_0(sK16,sK17)))),sK15) ),
    inference(instantiation,[status(thm)],[c_8924])).

cnf(c_88569,plain,
    ( ~ r1_tarski(k4_xboole_0(sK15,k4_xboole_0(sK15,k4_xboole_0(sK16,sK17))),X0)
    | r2_hidden(sK4(k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)),sK17,k4_xboole_0(sK15,k4_xboole_0(sK15,k4_xboole_0(sK16,sK17)))),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_63140,c_118,c_4826,c_4836,c_6007,c_14564,c_47603,c_49144,c_53124,c_85844,c_86994])).

cnf(c_22,plain,
    ( ~ r2_hidden(sK4(X0,X1,X2),X0)
    | ~ r2_hidden(sK4(X0,X1,X2),X2)
    | r2_hidden(sK4(X0,X1,X2),X1)
    | k4_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f239])).

cnf(c_88605,plain,
    ( ~ r1_tarski(k4_xboole_0(sK15,k4_xboole_0(sK15,k4_xboole_0(sK16,sK17))),k4_xboole_0(sK15,k4_xboole_0(sK15,k4_xboole_0(sK16,sK17))))
    | ~ r2_hidden(sK4(k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)),sK17,k4_xboole_0(sK15,k4_xboole_0(sK15,k4_xboole_0(sK16,sK17)))),k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)))
    | r2_hidden(sK4(k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)),sK17,k4_xboole_0(sK15,k4_xboole_0(sK15,k4_xboole_0(sK16,sK17)))),sK17)
    | k4_xboole_0(k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)),sK17) = k4_xboole_0(sK15,k4_xboole_0(sK15,k4_xboole_0(sK16,sK17))) ),
    inference(resolution,[status(thm)],[c_88569,c_22])).

cnf(c_64,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f411])).

cnf(c_16431,plain,
    ( r1_tarski(k4_xboole_0(sK15,k4_xboole_0(sK15,k4_xboole_0(sK16,sK17))),k4_xboole_0(sK15,k4_xboole_0(sK15,k4_xboole_0(sK16,sK17)))) ),
    inference(instantiation,[status(thm)],[c_64])).

cnf(c_14561,plain,
    ( ~ r2_hidden(sK4(k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)),sK17,k4_xboole_0(sK15,k4_xboole_0(sK15,k4_xboole_0(sK16,sK17)))),k4_xboole_0(sK16,sK17))
    | ~ r2_hidden(sK4(k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)),sK17,k4_xboole_0(sK15,k4_xboole_0(sK15,k4_xboole_0(sK16,sK17)))),sK17) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_166700,c_94988,c_88605,c_65809,c_53083,c_16431,c_14561,c_118])).

%------------------------------------------------------------------------------
