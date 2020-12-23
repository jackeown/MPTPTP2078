%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0267+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:20 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   47 (  91 expanded)
%              Number of leaves         :    7 (  21 expanded)
%              Depth                    :   14
%              Number of atoms          :  244 ( 619 expanded)
%              Number of equality atoms :   96 ( 205 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f840,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f741,f837,f735])).

fof(f735,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f507])).

fof(f507,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f457])).

fof(f457,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f455,f456])).

fof(f456,plain,(
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

fof(f455,plain,(
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
    inference(rectify,[],[f454])).

fof(f454,plain,(
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
    inference(flattening,[],[f453])).

fof(f453,plain,(
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

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f837,plain,(
    r2_hidden(sK0,k4_xboole_0(sK1,k2_tarski(sK0,sK0))) ),
    inference(trivial_inequality_removal,[],[f835])).

fof(f835,plain,
    ( sK0 != sK0
    | r2_hidden(sK0,k4_xboole_0(sK1,k2_tarski(sK0,sK0))) ),
    inference(backward_demodulation,[],[f753,f834])).

fof(f834,plain,(
    sK0 = sK2 ),
    inference(subsumption_resolution,[],[f833,f744])).

fof(f744,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k2_tarski(X0,X1))
      | X0 = X4
      | X1 = X4 ) ),
    inference(equality_resolution,[],[f518])).

fof(f518,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f467])).

fof(f467,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK6(X0,X1,X2) != X1
              & sK6(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK6(X0,X1,X2),X2) )
          & ( sK6(X0,X1,X2) = X1
            | sK6(X0,X1,X2) = X0
            | r2_hidden(sK6(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f465,f466])).

fof(f466,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK6(X0,X1,X2) != X1
            & sK6(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK6(X0,X1,X2),X2) )
        & ( sK6(X0,X1,X2) = X1
          | sK6(X0,X1,X2) = X0
          | r2_hidden(sK6(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f465,plain,(
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
    inference(rectify,[],[f464])).

fof(f464,plain,(
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
    inference(flattening,[],[f463])).

fof(f463,plain,(
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
    inference(nnf_transformation,[],[f176])).

fof(f176,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(f833,plain,
    ( sK0 = sK2
    | r2_hidden(sK0,k2_tarski(sK2,sK2)) ),
    inference(subsumption_resolution,[],[f832,f754])).

fof(f754,plain,(
    r2_hidden(sK0,sK1) ),
    inference(subsumption_resolution,[],[f646,f736])).

fof(f736,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f506])).

fof(f506,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f457])).

fof(f646,plain,
    ( r2_hidden(sK0,sK1)
    | r2_hidden(sK0,k4_xboole_0(sK1,k2_tarski(sK2,sK2))) ),
    inference(definition_unfolding,[],[f489,f620])).

fof(f620,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f254])).

fof(f254,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f489,plain,
    ( r2_hidden(sK0,sK1)
    | r2_hidden(sK0,k4_xboole_0(sK1,k1_tarski(sK2))) ),
    inference(cnf_transformation,[],[f443])).

fof(f443,plain,
    ( ( sK0 = sK2
      | ~ r2_hidden(sK0,sK1)
      | ~ r2_hidden(sK0,k4_xboole_0(sK1,k1_tarski(sK2))) )
    & ( ( sK0 != sK2
        & r2_hidden(sK0,sK1) )
      | r2_hidden(sK0,k4_xboole_0(sK1,k1_tarski(sK2))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f441,f442])).

fof(f442,plain,
    ( ? [X0,X1,X2] :
        ( ( X0 = X2
          | ~ r2_hidden(X0,X1)
          | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) )
        & ( ( X0 != X2
            & r2_hidden(X0,X1) )
          | r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) )
   => ( ( sK0 = sK2
        | ~ r2_hidden(sK0,sK1)
        | ~ r2_hidden(sK0,k4_xboole_0(sK1,k1_tarski(sK2))) )
      & ( ( sK0 != sK2
          & r2_hidden(sK0,sK1) )
        | r2_hidden(sK0,k4_xboole_0(sK1,k1_tarski(sK2))) ) ) ),
    introduced(choice_axiom,[])).

fof(f441,plain,(
    ? [X0,X1,X2] :
      ( ( X0 = X2
        | ~ r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(flattening,[],[f440])).

fof(f440,plain,(
    ? [X0,X1,X2] :
      ( ( X0 = X2
        | ~ r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(nnf_transformation,[],[f370])).

fof(f370,plain,(
    ? [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <~> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f364])).

fof(f364,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
      <=> ( X0 != X2
          & r2_hidden(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f363])).

fof(f363,conjecture,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(f832,plain,
    ( sK0 = sK2
    | r2_hidden(sK0,k2_tarski(sK2,sK2))
    | ~ r2_hidden(sK0,sK1) ),
    inference(resolution,[],[f752,f734])).

fof(f734,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f508])).

fof(f508,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f457])).

fof(f752,plain,
    ( ~ r2_hidden(sK0,k4_xboole_0(sK1,k2_tarski(sK2,sK2)))
    | sK0 = sK2 ),
    inference(subsumption_resolution,[],[f644,f736])).

fof(f644,plain,
    ( sK0 = sK2
    | ~ r2_hidden(sK0,sK1)
    | ~ r2_hidden(sK0,k4_xboole_0(sK1,k2_tarski(sK2,sK2))) ),
    inference(definition_unfolding,[],[f491,f620])).

fof(f491,plain,
    ( sK0 = sK2
    | ~ r2_hidden(sK0,sK1)
    | ~ r2_hidden(sK0,k4_xboole_0(sK1,k1_tarski(sK2))) ),
    inference(cnf_transformation,[],[f443])).

fof(f753,plain,
    ( sK0 != sK2
    | r2_hidden(sK0,k4_xboole_0(sK1,k2_tarski(sK0,sK0))) ),
    inference(inner_rewriting,[],[f645])).

fof(f645,plain,
    ( sK0 != sK2
    | r2_hidden(sK0,k4_xboole_0(sK1,k2_tarski(sK2,sK2))) ),
    inference(definition_unfolding,[],[f490,f620])).

fof(f490,plain,
    ( sK0 != sK2
    | r2_hidden(sK0,k4_xboole_0(sK1,k1_tarski(sK2))) ),
    inference(cnf_transformation,[],[f443])).

fof(f741,plain,(
    ! [X4,X0] : r2_hidden(X4,k2_tarski(X0,X4)) ),
    inference(equality_resolution,[],[f740])).

fof(f740,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f520])).

fof(f520,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f467])).
%------------------------------------------------------------------------------
