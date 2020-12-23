%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0059+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:16 EST 2020

% Result     : Theorem 31.87s
% Output     : CNFRefutation 31.87s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 638 expanded)
%              Number of clauses        :   38 ( 147 expanded)
%              Number of leaves         :   13 ( 145 expanded)
%              Depth                    :   17
%              Number of atoms          :  406 (3467 expanded)
%              Number of equality atoms :   57 ( 549 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

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

fof(f170,plain,(
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
    inference(flattening,[],[f170])).

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
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f171])).

fof(f173,plain,(
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

fof(f174,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f172,f173])).

fof(f229,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X1)
      | r2_hidden(sK2(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f174])).

fof(f92,conjecture,(
    ! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f93,negated_conjecture,(
    ~ ! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(negated_conjecture,[],[f92])).

fof(f155,plain,(
    ? [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) != k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(ennf_transformation,[],[f93])).

fof(f213,plain,
    ( ? [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) != k4_xboole_0(X0,k4_xboole_0(X1,X2))
   => k2_xboole_0(k4_xboole_0(sK15,sK16),k3_xboole_0(sK15,sK17)) != k4_xboole_0(sK15,k4_xboole_0(sK16,sK17)) ),
    introduced(choice_axiom,[])).

fof(f214,plain,(
    k2_xboole_0(k4_xboole_0(sK15,sK16),k3_xboole_0(sK15,sK17)) != k4_xboole_0(sK15,k4_xboole_0(sK16,sK17)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15,sK16,sK17])],[f155,f213])).

fof(f342,plain,(
    k2_xboole_0(k4_xboole_0(sK15,sK16),k3_xboole_0(sK15,sK17)) != k4_xboole_0(sK15,k4_xboole_0(sK16,sK17)) ),
    inference(cnf_transformation,[],[f214])).

fof(f86,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f336,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f86])).

fof(f411,plain,(
    k2_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK17))) != k4_xboole_0(sK15,k4_xboole_0(sK16,sK17)) ),
    inference(definition_unfolding,[],[f342,f336])).

fof(f70,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f147,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f70])).

fof(f319,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f147])).

fof(f72,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f321,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f72])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f110,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f166,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f110])).

fof(f167,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f166])).

fof(f168,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f169,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f167,f168])).

fof(f223,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f169])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f180,plain,(
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
    inference(flattening,[],[f180])).

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
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f181])).

fof(f183,plain,(
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

fof(f184,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f182,f183])).

fof(f238,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f184])).

fof(f421,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f238])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f175,plain,(
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
    inference(flattening,[],[f175])).

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
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f176])).

fof(f178,plain,(
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

fof(f179,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f177,f178])).

fof(f232,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f179])).

fof(f358,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f232,f336])).

fof(f418,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f358])).

fof(f231,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK2(X0,X1,X2),X1)
      | ~ r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f174])).

fof(f240,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f184])).

fof(f419,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f240])).

fof(f239,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f184])).

fof(f420,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f239])).

fof(f233,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f179])).

fof(f357,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f233,f336])).

fof(f417,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f357])).

fof(f234,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f179])).

fof(f356,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f234,f336])).

fof(f416,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f356])).

fof(f230,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK2(X0,X1,X2),X0)
      | ~ r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f174])).

cnf(c_12,plain,
    ( r2_hidden(sK2(X0,X1,X2),X1)
    | r2_hidden(sK2(X0,X1,X2),X2)
    | r2_hidden(sK2(X0,X1,X2),X0)
    | k2_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f229])).

cnf(c_124,negated_conjecture,
    ( k2_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK17))) != k4_xboole_0(sK15,k4_xboole_0(sK16,sK17)) ),
    inference(cnf_transformation,[],[f411])).

cnf(c_45407,plain,
    ( r2_hidden(sK2(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK17)),k4_xboole_0(sK15,k4_xboole_0(sK16,sK17))),k4_xboole_0(sK15,k4_xboole_0(sK16,sK17)))
    | r2_hidden(sK2(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK17)),k4_xboole_0(sK15,k4_xboole_0(sK16,sK17))),k4_xboole_0(sK15,k4_xboole_0(sK15,sK17)))
    | r2_hidden(sK2(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK17)),k4_xboole_0(sK15,k4_xboole_0(sK16,sK17))),k4_xboole_0(sK15,sK16)) ),
    inference(resolution,[status(thm)],[c_12,c_124])).

cnf(c_4794,plain,
    ( r2_hidden(sK2(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK17)),k4_xboole_0(sK15,k4_xboole_0(sK16,sK17))),k4_xboole_0(sK15,k4_xboole_0(sK16,sK17)))
    | r2_hidden(sK2(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK17)),k4_xboole_0(sK15,k4_xboole_0(sK16,sK17))),k4_xboole_0(sK15,k4_xboole_0(sK15,sK17)))
    | r2_hidden(sK2(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK17)),k4_xboole_0(sK15,k4_xboole_0(sK16,sK17))),k4_xboole_0(sK15,sK16))
    | k2_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK17))) = k4_xboole_0(sK15,k4_xboole_0(sK16,sK17)) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_102,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) ),
    inference(cnf_transformation,[],[f319])).

cnf(c_5363,plain,
    ( ~ r1_tarski(k4_xboole_0(sK16,sK17),sK16)
    | r1_tarski(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,k4_xboole_0(sK16,sK17))) ),
    inference(instantiation,[status(thm)],[c_102])).

cnf(c_104,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f321])).

cnf(c_9194,plain,
    ( r1_tarski(k4_xboole_0(sK16,sK17),sK16) ),
    inference(instantiation,[status(thm)],[c_104])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f223])).

cnf(c_10217,plain,
    ( ~ r1_tarski(k4_xboole_0(sK15,sK16),X0)
    | r2_hidden(sK2(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK17)),k4_xboole_0(sK15,k4_xboole_0(sK16,sK17))),X0)
    | ~ r2_hidden(sK2(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK17)),k4_xboole_0(sK15,k4_xboole_0(sK16,sK17))),k4_xboole_0(sK15,sK16)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_32000,plain,
    ( ~ r1_tarski(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,k4_xboole_0(sK16,sK17)))
    | r2_hidden(sK2(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK17)),k4_xboole_0(sK15,k4_xboole_0(sK16,sK17))),k4_xboole_0(sK15,k4_xboole_0(sK16,sK17)))
    | ~ r2_hidden(sK2(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK17)),k4_xboole_0(sK15,k4_xboole_0(sK16,sK17))),k4_xboole_0(sK15,sK16)) ),
    inference(instantiation,[status(thm)],[c_10217])).

cnf(c_45474,plain,
    ( r2_hidden(sK2(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK17)),k4_xboole_0(sK15,k4_xboole_0(sK16,sK17))),k4_xboole_0(sK15,k4_xboole_0(sK15,sK17)))
    | r2_hidden(sK2(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK17)),k4_xboole_0(sK15,k4_xboole_0(sK16,sK17))),k4_xboole_0(sK15,k4_xboole_0(sK16,sK17))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_45407,c_124,c_4794,c_5363,c_9194,c_32000])).

cnf(c_45475,plain,
    ( r2_hidden(sK2(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK17)),k4_xboole_0(sK15,k4_xboole_0(sK16,sK17))),k4_xboole_0(sK15,k4_xboole_0(sK16,sK17)))
    | r2_hidden(sK2(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK17)),k4_xboole_0(sK15,k4_xboole_0(sK16,sK17))),k4_xboole_0(sK15,k4_xboole_0(sK15,sK17))) ),
    inference(renaming,[status(thm)],[c_45474])).

cnf(c_27,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f421])).

cnf(c_45501,plain,
    ( r2_hidden(sK2(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK17)),k4_xboole_0(sK15,k4_xboole_0(sK16,sK17))),k4_xboole_0(sK15,k4_xboole_0(sK15,sK17)))
    | r2_hidden(sK2(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK17)),k4_xboole_0(sK15,k4_xboole_0(sK16,sK17))),sK15) ),
    inference(resolution,[status(thm)],[c_45475,c_27])).

cnf(c_21,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f418])).

cnf(c_7030,plain,
    ( ~ r2_hidden(sK2(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK17)),k4_xboole_0(sK15,k4_xboole_0(sK16,sK17))),k4_xboole_0(sK15,k4_xboole_0(sK15,sK17)))
    | r2_hidden(sK2(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK17)),k4_xboole_0(sK15,k4_xboole_0(sK16,sK17))),sK15) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_46086,plain,
    ( r2_hidden(sK2(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK17)),k4_xboole_0(sK15,k4_xboole_0(sK16,sK17))),sK15) ),
    inference(global_propositional_subsumption,[status(thm)],[c_45501,c_7030])).

cnf(c_46101,plain,
    ( ~ r1_tarski(sK15,X0)
    | r2_hidden(sK2(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK17)),k4_xboole_0(sK15,k4_xboole_0(sK16,sK17))),X0) ),
    inference(resolution,[status(thm)],[c_46086,c_9])).

cnf(c_10,plain,
    ( ~ r2_hidden(sK2(X0,X1,X2),X1)
    | ~ r2_hidden(sK2(X0,X1,X2),X2)
    | k2_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f231])).

cnf(c_47992,plain,
    ( ~ r1_tarski(sK15,k4_xboole_0(sK15,k4_xboole_0(sK16,sK17)))
    | ~ r2_hidden(sK2(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK17)),k4_xboole_0(sK15,k4_xboole_0(sK16,sK17))),k4_xboole_0(sK15,k4_xboole_0(sK15,sK17)))
    | k2_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK17))) = k4_xboole_0(sK15,k4_xboole_0(sK16,sK17)) ),
    inference(resolution,[status(thm)],[c_46101,c_10])).

cnf(c_5429,plain,
    ( ~ r2_hidden(sK2(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK17)),k4_xboole_0(sK15,k4_xboole_0(sK16,sK17))),k4_xboole_0(sK15,k4_xboole_0(sK16,sK17)))
    | ~ r2_hidden(sK2(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK17)),k4_xboole_0(sK15,k4_xboole_0(sK16,sK17))),k4_xboole_0(sK15,k4_xboole_0(sK15,sK17)))
    | k2_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK17))) = k4_xboole_0(sK15,k4_xboole_0(sK16,sK17)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_25,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f419])).

cnf(c_15202,plain,
    ( r2_hidden(sK2(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK17)),k4_xboole_0(sK15,k4_xboole_0(sK16,sK17))),X0)
    | r2_hidden(sK2(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK17)),k4_xboole_0(sK15,k4_xboole_0(sK16,sK17))),k4_xboole_0(sK15,X0))
    | ~ r2_hidden(sK2(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK17)),k4_xboole_0(sK15,k4_xboole_0(sK16,sK17))),sK15) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_48984,plain,
    ( r2_hidden(sK2(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK17)),k4_xboole_0(sK15,k4_xboole_0(sK16,sK17))),k4_xboole_0(sK16,sK17))
    | r2_hidden(sK2(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK17)),k4_xboole_0(sK15,k4_xboole_0(sK16,sK17))),k4_xboole_0(sK15,k4_xboole_0(sK16,sK17)))
    | ~ r2_hidden(sK2(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK17)),k4_xboole_0(sK15,k4_xboole_0(sK16,sK17))),sK15) ),
    inference(instantiation,[status(thm)],[c_15202])).

cnf(c_26,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f420])).

cnf(c_45499,plain,
    ( ~ r2_hidden(sK2(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK17)),k4_xboole_0(sK15,k4_xboole_0(sK16,sK17))),k4_xboole_0(sK16,sK17))
    | r2_hidden(sK2(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK17)),k4_xboole_0(sK15,k4_xboole_0(sK16,sK17))),k4_xboole_0(sK15,k4_xboole_0(sK15,sK17))) ),
    inference(resolution,[status(thm)],[c_45475,c_26])).

cnf(c_20,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f417])).

cnf(c_47208,plain,
    ( ~ r2_hidden(sK2(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK17)),k4_xboole_0(sK15,k4_xboole_0(sK16,sK17))),k4_xboole_0(sK16,sK17))
    | r2_hidden(sK2(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK17)),k4_xboole_0(sK15,k4_xboole_0(sK16,sK17))),sK17) ),
    inference(resolution,[status(thm)],[c_45499,c_20])).

cnf(c_52112,plain,
    ( ~ r2_hidden(sK2(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK17)),k4_xboole_0(sK15,k4_xboole_0(sK16,sK17))),k4_xboole_0(sK16,sK17)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_47208,c_26])).

cnf(c_139752,plain,
    ( ~ r2_hidden(sK2(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK17)),k4_xboole_0(sK15,k4_xboole_0(sK16,sK17))),k4_xboole_0(sK15,k4_xboole_0(sK15,sK17))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_47992,c_124,c_5429,c_7030,c_45501,c_48984,c_52112])).

cnf(c_19,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f416])).

cnf(c_139777,plain,
    ( ~ r2_hidden(sK2(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK17)),k4_xboole_0(sK15,k4_xboole_0(sK16,sK17))),sK17)
    | ~ r2_hidden(sK2(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK17)),k4_xboole_0(sK15,k4_xboole_0(sK16,sK17))),sK15) ),
    inference(resolution,[status(thm)],[c_139752,c_19])).

cnf(c_61408,plain,
    ( r2_hidden(sK2(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK17)),k4_xboole_0(sK15,k4_xboole_0(sK16,sK17))),sK17)
    | ~ r2_hidden(sK2(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK17)),k4_xboole_0(sK15,k4_xboole_0(sK16,sK17))),sK16) ),
    inference(resolution,[status(thm)],[c_52112,c_25])).

cnf(c_56646,plain,
    ( r2_hidden(sK2(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK17)),k4_xboole_0(sK15,k4_xboole_0(sK16,sK17))),k4_xboole_0(sK15,sK16))
    | r2_hidden(sK2(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK17)),k4_xboole_0(sK15,k4_xboole_0(sK16,sK17))),sK16)
    | ~ r2_hidden(sK2(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK17)),k4_xboole_0(sK15,k4_xboole_0(sK16,sK17))),sK15) ),
    inference(instantiation,[status(thm)],[c_15202])).

cnf(c_11,plain,
    ( ~ r2_hidden(sK2(X0,X1,X2),X2)
    | ~ r2_hidden(sK2(X0,X1,X2),X0)
    | k2_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f230])).

cnf(c_10226,plain,
    ( ~ r2_hidden(sK2(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK17)),k4_xboole_0(sK15,k4_xboole_0(sK16,sK17))),k4_xboole_0(sK15,k4_xboole_0(sK16,sK17)))
    | ~ r2_hidden(sK2(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK17)),k4_xboole_0(sK15,k4_xboole_0(sK16,sK17))),k4_xboole_0(sK15,sK16))
    | k2_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK17))) = k4_xboole_0(sK15,k4_xboole_0(sK16,sK17)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_139777,c_61408,c_56646,c_52112,c_48984,c_46086,c_10226,c_124])).

%------------------------------------------------------------------------------
