%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:34 EST 2020

% Result     : Theorem 1.32s
% Output     : Refutation 1.32s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 342 expanded)
%              Number of leaves         :   28 ( 118 expanded)
%              Depth                    :   20
%              Number of atoms          :  436 (1575 expanded)
%              Number of equality atoms :  190 ( 762 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f421,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f78,f87,f93,f100,f106,f137,f165,f169,f177,f222,f290,f299,f418])).

fof(f418,plain,(
    ~ spl10_17 ),
    inference(avatar_contradiction_clause,[],[f393])).

fof(f393,plain,
    ( $false
    | ~ spl10_17 ),
    inference(subsumption_resolution,[],[f73,f317])).

fof(f317,plain,
    ( ! [X0,X1] : X0 = X1
    | ~ spl10_17 ),
    inference(superposition,[],[f309,f309])).

fof(f309,plain,
    ( ! [X0] : sK0 = X0
    | ~ spl10_17 ),
    inference(resolution,[],[f289,f70])).

fof(f70,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k2_tarski(X0,X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_tarski(X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f47,f56])).

fof(f56,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f47,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK9(X0,X1) != X0
            | ~ r2_hidden(sK9(X0,X1),X1) )
          & ( sK9(X0,X1) = X0
            | r2_hidden(sK9(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f26,f27])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK9(X0,X1) != X0
          | ~ r2_hidden(sK9(X0,X1),X1) )
        & ( sK9(X0,X1) = X0
          | r2_hidden(sK9(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
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
    inference(rectify,[],[f25])).

fof(f25,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f289,plain,
    ( ! [X5] : r2_hidden(sK0,X5)
    | ~ spl10_17 ),
    inference(avatar_component_clause,[],[f288])).

fof(f288,plain,
    ( spl10_17
  <=> ! [X5] : r2_hidden(sK0,X5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_17])])).

fof(f73,plain,(
    ! [X1] : k2_tarski(X1,X1) != k4_xboole_0(k2_tarski(X1,X1),k2_tarski(X1,X1)) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k2_tarski(X0,X0) != k4_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X1)) ) ),
    inference(definition_unfolding,[],[f54,f56,f56,f56])).

fof(f54,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
        | X0 = X1 )
      & ( X0 != X1
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f299,plain,
    ( ~ spl10_11
    | ~ spl10_16 ),
    inference(avatar_contradiction_clause,[],[f291])).

fof(f291,plain,
    ( $false
    | ~ spl10_11
    | ~ spl10_16 ),
    inference(subsumption_resolution,[],[f157,f286])).

fof(f286,plain,
    ( ! [X4] : ~ r2_hidden(X4,k1_xboole_0)
    | ~ spl10_16 ),
    inference(avatar_component_clause,[],[f285])).

fof(f285,plain,
    ( spl10_16
  <=> ! [X4] : ~ r2_hidden(X4,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).

fof(f157,plain,
    ( r2_hidden(sK0,k1_xboole_0)
    | ~ spl10_11 ),
    inference(avatar_component_clause,[],[f155])).

fof(f155,plain,
    ( spl10_11
  <=> r2_hidden(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).

fof(f290,plain,
    ( spl10_16
    | spl10_17
    | ~ spl10_7 ),
    inference(avatar_split_clause,[],[f280,f130,f288,f285])).

fof(f130,plain,
    ( spl10_7
  <=> k1_xboole_0 = k2_tarski(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).

fof(f280,plain,
    ( ! [X4,X5] :
        ( r2_hidden(sK0,X5)
        | ~ r2_hidden(X4,k1_xboole_0) )
    | ~ spl10_7 ),
    inference(duplicate_literal_removal,[],[f279])).

fof(f279,plain,
    ( ! [X4,X5] :
        ( r2_hidden(sK0,X5)
        | ~ r2_hidden(X4,k1_xboole_0)
        | ~ r2_hidden(X4,k1_xboole_0) )
    | ~ spl10_7 ),
    inference(superposition,[],[f272,f266])).

fof(f266,plain,
    ( ! [X6] :
        ( sK0 = k2_mcart_1(X6)
        | ~ r2_hidden(X6,k1_xboole_0) )
    | ~ spl10_7 ),
    inference(duplicate_literal_removal,[],[f265])).

fof(f265,plain,
    ( ! [X6] :
        ( sK0 = k2_mcart_1(X6)
        | ~ r2_hidden(X6,k1_xboole_0)
        | ~ r2_hidden(X6,k1_xboole_0) )
    | ~ spl10_7 ),
    inference(superposition,[],[f190,f209])).

fof(f209,plain,
    ( ! [X10,X11] :
        ( sK7(k1_xboole_0,X10,X11) = k2_mcart_1(X11)
        | ~ r2_hidden(X11,k1_xboole_0) )
    | ~ spl10_7 ),
    inference(superposition,[],[f35,f202])).

fof(f202,plain,
    ( ! [X0,X1] :
        ( k4_tarski(sK0,sK7(k1_xboole_0,X0,X1)) = X1
        | ~ r2_hidden(X1,k1_xboole_0) )
    | ~ spl10_7 ),
    inference(duplicate_literal_removal,[],[f201])).

fof(f201,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,k1_xboole_0)
        | k4_tarski(sK0,sK7(k1_xboole_0,X0,X1)) = X1
        | ~ r2_hidden(X1,k1_xboole_0) )
    | ~ spl10_7 ),
    inference(forward_demodulation,[],[f194,f72])).

fof(f72,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f194,plain,
    ( ! [X0,X1] :
        ( k4_tarski(sK0,sK7(k1_xboole_0,X0,X1)) = X1
        | ~ r2_hidden(X1,k2_zfmisc_1(k1_xboole_0,X0))
        | ~ r2_hidden(X1,k1_xboole_0) )
    | ~ spl10_7 ),
    inference(superposition,[],[f65,f189])).

fof(f189,plain,
    ( ! [X0,X1] :
        ( sK0 = sK6(k1_xboole_0,X0,X1)
        | ~ r2_hidden(X1,k1_xboole_0) )
    | ~ spl10_7 ),
    inference(forward_demodulation,[],[f185,f72])).

fof(f185,plain,
    ( ! [X0,X1] :
        ( sK0 = sK6(k1_xboole_0,X0,X1)
        | ~ r2_hidden(X1,k2_zfmisc_1(k1_xboole_0,X0)) )
    | ~ spl10_7 ),
    inference(resolution,[],[f175,f67])).

fof(f67,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK6(X0,X1,X8),X0)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK6(X0,X1,X8),X0)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ( ( ! [X4,X5] :
                ( k4_tarski(X4,X5) != sK3(X0,X1,X2)
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X0) )
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( ( sK3(X0,X1,X2) = k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2))
              & r2_hidden(sK5(X0,X1,X2),X1)
              & r2_hidden(sK4(X0,X1,X2),X0) )
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k4_tarski(X9,X10) != X8
                  | ~ r2_hidden(X10,X1)
                  | ~ r2_hidden(X9,X0) ) )
            & ( ( k4_tarski(sK6(X0,X1,X8),sK7(X0,X1,X8)) = X8
                & r2_hidden(sK7(X0,X1,X8),X1)
                & r2_hidden(sK6(X0,X1,X8),X0) )
              | ~ r2_hidden(X8,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7])],[f18,f21,f20,f19])).

fof(f19,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4,X5] :
                ( k4_tarski(X4,X5) != X3
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X6,X7] :
                ( k4_tarski(X6,X7) = X3
                & r2_hidden(X7,X1)
                & r2_hidden(X6,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X5,X4] :
              ( k4_tarski(X4,X5) != sK3(X0,X1,X2)
              | ~ r2_hidden(X5,X1)
              | ~ r2_hidden(X4,X0) )
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ? [X7,X6] :
              ( k4_tarski(X6,X7) = sK3(X0,X1,X2)
              & r2_hidden(X7,X1)
              & r2_hidden(X6,X0) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X2,X1,X0] :
      ( ? [X7,X6] :
          ( k4_tarski(X6,X7) = sK3(X0,X1,X2)
          & r2_hidden(X7,X1)
          & r2_hidden(X6,X0) )
     => ( sK3(X0,X1,X2) = k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2))
        & r2_hidden(sK5(X0,X1,X2),X1)
        & r2_hidden(sK4(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X8,X1,X0] :
      ( ? [X11,X12] :
          ( k4_tarski(X11,X12) = X8
          & r2_hidden(X12,X1)
          & r2_hidden(X11,X0) )
     => ( k4_tarski(sK6(X0,X1,X8),sK7(X0,X1,X8)) = X8
        & r2_hidden(sK7(X0,X1,X8),X1)
        & r2_hidden(sK6(X0,X1,X8),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ? [X3] :
            ( ( ! [X4,X5] :
                  ( k4_tarski(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X6,X7] :
                  ( k4_tarski(X6,X7) = X3
                  & r2_hidden(X7,X1)
                  & r2_hidden(X6,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k4_tarski(X9,X10) != X8
                  | ~ r2_hidden(X10,X1)
                  | ~ r2_hidden(X9,X0) ) )
            & ( ? [X11,X12] :
                  ( k4_tarski(X11,X12) = X8
                  & r2_hidden(X12,X1)
                  & r2_hidden(X11,X0) )
              | ~ r2_hidden(X8,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ? [X3] :
            ( ( ! [X4,X5] :
                  ( k4_tarski(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X4,X5] :
                  ( k4_tarski(X4,X5) = X3
                  & r2_hidden(X5,X1)
                  & r2_hidden(X4,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ! [X4,X5] :
                  ( k4_tarski(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) ) )
            & ( ? [X4,X5] :
                  ( k4_tarski(X4,X5) = X3
                  & r2_hidden(X5,X1)
                  & r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(f175,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,k1_xboole_0)
        | sK0 = X2 )
    | ~ spl10_7 ),
    inference(superposition,[],[f70,f132])).

fof(f132,plain,
    ( k1_xboole_0 = k2_tarski(sK0,sK0)
    | ~ spl10_7 ),
    inference(avatar_component_clause,[],[f130])).

fof(f65,plain,(
    ! [X0,X8,X1] :
      ( k4_tarski(sK6(X0,X1,X8),sK7(X0,X1,X8)) = X8
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X2,X0,X8,X1] :
      ( k4_tarski(sK6(X0,X1,X8),sK7(X0,X1,X8)) = X8
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f35,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f190,plain,
    ( ! [X2,X3] :
        ( sK0 = sK7(X2,k1_xboole_0,X3)
        | ~ r2_hidden(X3,k1_xboole_0) )
    | ~ spl10_7 ),
    inference(forward_demodulation,[],[f186,f71])).

fof(f71,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f186,plain,
    ( ! [X2,X3] :
        ( sK0 = sK7(X2,k1_xboole_0,X3)
        | ~ r2_hidden(X3,k2_zfmisc_1(X2,k1_xboole_0)) )
    | ~ spl10_7 ),
    inference(resolution,[],[f175,f66])).

fof(f66,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK7(X0,X1,X8),X1)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK7(X0,X1,X8),X1)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f272,plain,
    ( ! [X4,X5] :
        ( r2_hidden(k2_mcart_1(X5),X4)
        | ~ r2_hidden(X5,k1_xboole_0) )
    | ~ spl10_7 ),
    inference(duplicate_literal_removal,[],[f271])).

fof(f271,plain,
    ( ! [X4,X5] :
        ( ~ r2_hidden(X5,k1_xboole_0)
        | r2_hidden(k2_mcart_1(X5),X4)
        | ~ r2_hidden(X5,k1_xboole_0) )
    | ~ spl10_7 ),
    inference(forward_demodulation,[],[f264,f72])).

fof(f264,plain,
    ( ! [X4,X5] :
        ( r2_hidden(k2_mcart_1(X5),X4)
        | ~ r2_hidden(X5,k2_zfmisc_1(k1_xboole_0,X4))
        | ~ r2_hidden(X5,k1_xboole_0) )
    | ~ spl10_7 ),
    inference(superposition,[],[f66,f209])).

fof(f222,plain,
    ( k1_mcart_1(sK0) != sK1
    | sK0 != k1_mcart_1(sK0)
    | r2_hidden(sK1,k2_tarski(sK0,sK0))
    | ~ r2_hidden(sK0,k2_tarski(sK0,sK0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f177,plain,
    ( spl10_11
    | ~ spl10_7 ),
    inference(avatar_split_clause,[],[f176,f130,f155])).

fof(f176,plain,
    ( r2_hidden(sK0,k1_xboole_0)
    | ~ spl10_7 ),
    inference(superposition,[],[f69,f132])).

fof(f69,plain,(
    ! [X3] : r2_hidden(X3,k2_tarski(X3,X3)) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k2_tarski(X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k2_tarski(X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f48,f56])).

fof(f48,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f169,plain,(
    spl10_12 ),
    inference(avatar_contradiction_clause,[],[f166])).

fof(f166,plain,
    ( $false
    | spl10_12 ),
    inference(unit_resulting_resolution,[],[f69,f164])).

fof(f164,plain,
    ( ~ r2_hidden(sK0,k2_tarski(sK0,sK0))
    | spl10_12 ),
    inference(avatar_component_clause,[],[f162])).

fof(f162,plain,
    ( spl10_12
  <=> r2_hidden(sK0,k2_tarski(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).

fof(f165,plain,
    ( spl10_7
    | ~ spl10_12
    | ~ spl10_6 ),
    inference(avatar_split_clause,[],[f160,f103,f162,f130])).

fof(f103,plain,
    ( spl10_6
  <=> sK0 = k4_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f160,plain,
    ( ~ r2_hidden(sK0,k2_tarski(sK0,sK0))
    | k1_xboole_0 = k2_tarski(sK0,sK0)
    | ~ spl10_6 ),
    inference(equality_resolution,[],[f139])).

fof(f139,plain,
    ( ! [X0] :
        ( sK0 != X0
        | ~ r2_hidden(sK0,k2_tarski(X0,X0))
        | k2_tarski(X0,X0) = k1_xboole_0 )
    | ~ spl10_6 ),
    inference(duplicate_literal_removal,[],[f138])).

fof(f138,plain,
    ( ! [X0] :
        ( sK0 != X0
        | ~ r2_hidden(sK0,k2_tarski(X0,X0))
        | k2_tarski(X0,X0) = k1_xboole_0
        | k2_tarski(X0,X0) = k1_xboole_0 )
    | ~ spl10_6 ),
    inference(superposition,[],[f125,f110])).

fof(f110,plain,(
    ! [X1] :
      ( sK8(k2_tarski(X1,X1)) = X1
      | k1_xboole_0 = k2_tarski(X1,X1) ) ),
    inference(resolution,[],[f70,f44])).

fof(f44,plain,(
    ! [X0] :
      ( r2_hidden(sK8(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( ! [X2,X3] :
            ( k4_tarski(X2,X3) != sK8(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK8(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f13,f23])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] :
            ( k4_tarski(X2,X3) != sK8(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK8(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3] :
                  ~ ( k4_tarski(X2,X3) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).

fof(f125,plain,
    ( ! [X1] :
        ( sK0 != sK8(X1)
        | ~ r2_hidden(sK0,X1)
        | k1_xboole_0 = X1 )
    | ~ spl10_6 ),
    inference(superposition,[],[f46,f105])).

fof(f105,plain,
    ( sK0 = k4_tarski(sK1,sK0)
    | ~ spl10_6 ),
    inference(avatar_component_clause,[],[f103])).

fof(f46,plain,(
    ! [X2,X0,X3] :
      ( k4_tarski(X2,X3) != sK8(X0)
      | ~ r2_hidden(X3,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f137,plain,
    ( spl10_7
    | ~ spl10_8
    | ~ spl10_1 ),
    inference(avatar_split_clause,[],[f123,f75,f134,f130])).

fof(f134,plain,
    ( spl10_8
  <=> r2_hidden(sK1,k2_tarski(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f75,plain,
    ( spl10_1
  <=> sK0 = k4_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f123,plain,
    ( ~ r2_hidden(sK1,k2_tarski(sK0,sK0))
    | k1_xboole_0 = k2_tarski(sK0,sK0)
    | ~ spl10_1 ),
    inference(equality_resolution,[],[f122])).

fof(f122,plain,
    ( ! [X0] :
        ( sK0 != X0
        | ~ r2_hidden(sK1,k2_tarski(X0,X0))
        | k2_tarski(X0,X0) = k1_xboole_0 )
    | ~ spl10_1 ),
    inference(duplicate_literal_removal,[],[f117])).

fof(f117,plain,
    ( ! [X0] :
        ( sK0 != X0
        | ~ r2_hidden(sK1,k2_tarski(X0,X0))
        | k2_tarski(X0,X0) = k1_xboole_0
        | k2_tarski(X0,X0) = k1_xboole_0 )
    | ~ spl10_1 ),
    inference(superposition,[],[f115,f110])).

fof(f115,plain,
    ( ! [X0] :
        ( sK0 != sK8(X0)
        | ~ r2_hidden(sK1,X0)
        | k1_xboole_0 = X0 )
    | ~ spl10_1 ),
    inference(superposition,[],[f45,f77])).

fof(f77,plain,
    ( sK0 = k4_tarski(sK1,sK2)
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f75])).

fof(f45,plain,(
    ! [X2,X0,X3] :
      ( k4_tarski(X2,X3) != sK8(X0)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f106,plain,
    ( spl10_6
    | ~ spl10_1
    | ~ spl10_5 ),
    inference(avatar_split_clause,[],[f101,f97,f75,f103])).

fof(f97,plain,
    ( spl10_5
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f101,plain,
    ( sK0 = k4_tarski(sK1,sK0)
    | ~ spl10_1
    | ~ spl10_5 ),
    inference(superposition,[],[f77,f99])).

fof(f99,plain,
    ( sK0 = sK2
    | ~ spl10_5 ),
    inference(avatar_component_clause,[],[f97])).

fof(f100,plain,
    ( spl10_5
    | ~ spl10_1
    | ~ spl10_3 ),
    inference(avatar_split_clause,[],[f95,f84,f75,f97])).

fof(f84,plain,
    ( spl10_3
  <=> sK0 = k2_mcart_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f95,plain,
    ( sK0 = sK2
    | ~ spl10_1
    | ~ spl10_3 ),
    inference(forward_demodulation,[],[f94,f86])).

fof(f86,plain,
    ( sK0 = k2_mcart_1(sK0)
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f84])).

fof(f94,plain,
    ( k2_mcart_1(sK0) = sK2
    | ~ spl10_1 ),
    inference(superposition,[],[f35,f77])).

fof(f93,plain,
    ( spl10_4
    | ~ spl10_1 ),
    inference(avatar_split_clause,[],[f88,f75,f90])).

fof(f90,plain,
    ( spl10_4
  <=> k1_mcart_1(sK0) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f88,plain,
    ( k1_mcart_1(sK0) = sK1
    | ~ spl10_1 ),
    inference(superposition,[],[f34,f77])).

fof(f34,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f87,plain,
    ( spl10_2
    | spl10_3 ),
    inference(avatar_split_clause,[],[f33,f84,f80])).

fof(f80,plain,
    ( spl10_2
  <=> sK0 = k1_mcart_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f33,plain,
    ( sK0 = k2_mcart_1(sK0)
    | sK0 = k1_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ( sK0 = k2_mcart_1(sK0)
      | sK0 = k1_mcart_1(sK0) )
    & sK0 = k4_tarski(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f15,f14])).

fof(f14,plain,
    ( ? [X0] :
        ( ( k2_mcart_1(X0) = X0
          | k1_mcart_1(X0) = X0 )
        & ? [X1,X2] : k4_tarski(X1,X2) = X0 )
   => ( ( sK0 = k2_mcart_1(sK0)
        | sK0 = k1_mcart_1(sK0) )
      & ? [X2,X1] : k4_tarski(X1,X2) = sK0 ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ? [X2,X1] : k4_tarski(X1,X2) = sK0
   => sK0 = k4_tarski(sK1,sK2) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ( k2_mcart_1(X0) = X0
        | k1_mcart_1(X0) = X0 )
      & ? [X1,X2] : k4_tarski(X1,X2) = X0 ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ? [X1,X2] : k4_tarski(X1,X2) = X0
       => ( k2_mcart_1(X0) != X0
          & k1_mcart_1(X0) != X0 ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).

fof(f78,plain,(
    spl10_1 ),
    inference(avatar_split_clause,[],[f32,f75])).

fof(f32,plain,(
    sK0 = k4_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n014.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:53:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.51  % (627)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.51  % (644)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.51  % (637)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.21/0.52  % (627)Refutation not found, incomplete strategy% (627)------------------------------
% 1.21/0.52  % (627)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.21/0.53  % (644)Refutation not found, incomplete strategy% (644)------------------------------
% 1.21/0.53  % (644)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.21/0.53  % (627)Termination reason: Refutation not found, incomplete strategy
% 1.21/0.53  
% 1.21/0.53  % (627)Memory used [KB]: 10618
% 1.21/0.53  % (627)Time elapsed: 0.111 s
% 1.21/0.53  % (627)------------------------------
% 1.21/0.53  % (627)------------------------------
% 1.21/0.53  % (644)Termination reason: Refutation not found, incomplete strategy
% 1.21/0.53  
% 1.21/0.53  % (644)Memory used [KB]: 6268
% 1.21/0.53  % (644)Time elapsed: 0.117 s
% 1.21/0.53  % (644)------------------------------
% 1.21/0.53  % (644)------------------------------
% 1.32/0.53  % (618)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.32/0.54  % (615)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.32/0.54  % (617)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.32/0.54  % (619)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.32/0.54  % (616)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.32/0.54  % (620)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.32/0.54  % (641)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.32/0.55  % (638)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.32/0.55  % (647)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.32/0.55  % (630)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.32/0.55  % (647)Refutation not found, incomplete strategy% (647)------------------------------
% 1.32/0.55  % (647)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.55  % (647)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.55  
% 1.32/0.55  % (647)Memory used [KB]: 1663
% 1.32/0.55  % (647)Time elapsed: 0.001 s
% 1.32/0.55  % (647)------------------------------
% 1.32/0.55  % (647)------------------------------
% 1.32/0.55  % (643)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.32/0.55  % (639)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.32/0.55  % (629)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.32/0.56  % (635)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.32/0.56  % (636)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.32/0.56  % (622)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.32/0.56  % (628)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.32/0.56  % (645)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.32/0.56  % (626)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.32/0.56  % (616)Refutation not found, incomplete strategy% (616)------------------------------
% 1.32/0.56  % (616)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.56  % (616)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.56  
% 1.32/0.56  % (616)Memory used [KB]: 1663
% 1.32/0.56  % (616)Time elapsed: 0.153 s
% 1.32/0.56  % (616)------------------------------
% 1.32/0.56  % (616)------------------------------
% 1.32/0.56  % (640)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.32/0.56  % (624)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.32/0.57  % (623)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.32/0.57  % (625)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.32/0.57  % (646)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.32/0.57  % (621)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.32/0.57  % (625)Refutation not found, incomplete strategy% (625)------------------------------
% 1.32/0.57  % (625)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.57  % (625)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.57  
% 1.32/0.57  % (625)Memory used [KB]: 10746
% 1.32/0.57  % (625)Time elapsed: 0.157 s
% 1.32/0.57  % (625)------------------------------
% 1.32/0.57  % (625)------------------------------
% 1.32/0.57  % (646)Refutation not found, incomplete strategy% (646)------------------------------
% 1.32/0.57  % (646)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.57  % (646)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.57  
% 1.32/0.57  % (646)Memory used [KB]: 10746
% 1.32/0.57  % (646)Time elapsed: 0.156 s
% 1.32/0.57  % (646)------------------------------
% 1.32/0.57  % (646)------------------------------
% 1.32/0.57  % (629)Refutation not found, incomplete strategy% (629)------------------------------
% 1.32/0.57  % (629)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.57  % (629)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.57  
% 1.32/0.57  % (629)Memory used [KB]: 1791
% 1.32/0.57  % (629)Time elapsed: 0.169 s
% 1.32/0.57  % (629)------------------------------
% 1.32/0.57  % (629)------------------------------
% 1.32/0.57  % (642)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.32/0.57  % (641)Refutation found. Thanks to Tanya!
% 1.32/0.57  % SZS status Theorem for theBenchmark
% 1.32/0.57  % SZS output start Proof for theBenchmark
% 1.32/0.57  fof(f421,plain,(
% 1.32/0.57    $false),
% 1.32/0.57    inference(avatar_sat_refutation,[],[f78,f87,f93,f100,f106,f137,f165,f169,f177,f222,f290,f299,f418])).
% 1.32/0.57  fof(f418,plain,(
% 1.32/0.57    ~spl10_17),
% 1.32/0.57    inference(avatar_contradiction_clause,[],[f393])).
% 1.32/0.57  fof(f393,plain,(
% 1.32/0.57    $false | ~spl10_17),
% 1.32/0.57    inference(subsumption_resolution,[],[f73,f317])).
% 1.32/0.57  fof(f317,plain,(
% 1.32/0.57    ( ! [X0,X1] : (X0 = X1) ) | ~spl10_17),
% 1.32/0.57    inference(superposition,[],[f309,f309])).
% 1.32/0.57  fof(f309,plain,(
% 1.32/0.57    ( ! [X0] : (sK0 = X0) ) | ~spl10_17),
% 1.32/0.57    inference(resolution,[],[f289,f70])).
% 1.32/0.57  fof(f70,plain,(
% 1.32/0.57    ( ! [X0,X3] : (~r2_hidden(X3,k2_tarski(X0,X0)) | X0 = X3) )),
% 1.32/0.57    inference(equality_resolution,[],[f60])).
% 1.32/0.57  fof(f60,plain,(
% 1.32/0.57    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_tarski(X0,X0) != X1) )),
% 1.32/0.57    inference(definition_unfolding,[],[f47,f56])).
% 1.32/0.57  fof(f56,plain,(
% 1.32/0.57    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.32/0.57    inference(cnf_transformation,[],[f2])).
% 1.32/0.57  fof(f2,axiom,(
% 1.32/0.57    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.32/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.32/0.57  fof(f47,plain,(
% 1.32/0.57    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 1.32/0.57    inference(cnf_transformation,[],[f28])).
% 1.32/0.57  fof(f28,plain,(
% 1.32/0.57    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK9(X0,X1) != X0 | ~r2_hidden(sK9(X0,X1),X1)) & (sK9(X0,X1) = X0 | r2_hidden(sK9(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.32/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f26,f27])).
% 1.32/0.57  fof(f27,plain,(
% 1.32/0.57    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK9(X0,X1) != X0 | ~r2_hidden(sK9(X0,X1),X1)) & (sK9(X0,X1) = X0 | r2_hidden(sK9(X0,X1),X1))))),
% 1.32/0.57    introduced(choice_axiom,[])).
% 1.32/0.57  fof(f26,plain,(
% 1.32/0.57    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.32/0.57    inference(rectify,[],[f25])).
% 1.32/0.57  fof(f25,plain,(
% 1.32/0.57    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.32/0.57    inference(nnf_transformation,[],[f1])).
% 1.32/0.57  fof(f1,axiom,(
% 1.32/0.57    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.32/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 1.32/0.57  fof(f289,plain,(
% 1.32/0.57    ( ! [X5] : (r2_hidden(sK0,X5)) ) | ~spl10_17),
% 1.32/0.57    inference(avatar_component_clause,[],[f288])).
% 1.32/0.57  fof(f288,plain,(
% 1.32/0.57    spl10_17 <=> ! [X5] : r2_hidden(sK0,X5)),
% 1.32/0.57    introduced(avatar_definition,[new_symbols(naming,[spl10_17])])).
% 1.32/0.57  fof(f73,plain,(
% 1.32/0.57    ( ! [X1] : (k2_tarski(X1,X1) != k4_xboole_0(k2_tarski(X1,X1),k2_tarski(X1,X1))) )),
% 1.32/0.57    inference(equality_resolution,[],[f62])).
% 1.32/0.57  fof(f62,plain,(
% 1.32/0.57    ( ! [X0,X1] : (X0 != X1 | k2_tarski(X0,X0) != k4_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X1))) )),
% 1.32/0.57    inference(definition_unfolding,[],[f54,f56,f56,f56])).
% 1.32/0.57  fof(f54,plain,(
% 1.32/0.57    ( ! [X0,X1] : (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 1.32/0.57    inference(cnf_transformation,[],[f31])).
% 1.32/0.57  fof(f31,plain,(
% 1.32/0.57    ! [X0,X1] : ((k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) & (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))))),
% 1.32/0.57    inference(nnf_transformation,[],[f7])).
% 1.32/0.57  fof(f7,axiom,(
% 1.32/0.57    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 1.32/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 1.32/0.57  fof(f299,plain,(
% 1.32/0.57    ~spl10_11 | ~spl10_16),
% 1.32/0.57    inference(avatar_contradiction_clause,[],[f291])).
% 1.32/0.57  fof(f291,plain,(
% 1.32/0.57    $false | (~spl10_11 | ~spl10_16)),
% 1.32/0.57    inference(subsumption_resolution,[],[f157,f286])).
% 1.32/0.57  fof(f286,plain,(
% 1.32/0.57    ( ! [X4] : (~r2_hidden(X4,k1_xboole_0)) ) | ~spl10_16),
% 1.32/0.57    inference(avatar_component_clause,[],[f285])).
% 1.32/0.57  fof(f285,plain,(
% 1.32/0.57    spl10_16 <=> ! [X4] : ~r2_hidden(X4,k1_xboole_0)),
% 1.32/0.57    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).
% 1.32/0.57  fof(f157,plain,(
% 1.32/0.57    r2_hidden(sK0,k1_xboole_0) | ~spl10_11),
% 1.32/0.57    inference(avatar_component_clause,[],[f155])).
% 1.32/0.57  fof(f155,plain,(
% 1.32/0.57    spl10_11 <=> r2_hidden(sK0,k1_xboole_0)),
% 1.32/0.57    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).
% 1.32/0.57  fof(f290,plain,(
% 1.32/0.57    spl10_16 | spl10_17 | ~spl10_7),
% 1.32/0.57    inference(avatar_split_clause,[],[f280,f130,f288,f285])).
% 1.32/0.57  fof(f130,plain,(
% 1.32/0.57    spl10_7 <=> k1_xboole_0 = k2_tarski(sK0,sK0)),
% 1.32/0.57    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).
% 1.32/0.57  fof(f280,plain,(
% 1.32/0.57    ( ! [X4,X5] : (r2_hidden(sK0,X5) | ~r2_hidden(X4,k1_xboole_0)) ) | ~spl10_7),
% 1.32/0.57    inference(duplicate_literal_removal,[],[f279])).
% 1.32/0.57  fof(f279,plain,(
% 1.32/0.57    ( ! [X4,X5] : (r2_hidden(sK0,X5) | ~r2_hidden(X4,k1_xboole_0) | ~r2_hidden(X4,k1_xboole_0)) ) | ~spl10_7),
% 1.32/0.57    inference(superposition,[],[f272,f266])).
% 1.32/0.57  fof(f266,plain,(
% 1.32/0.57    ( ! [X6] : (sK0 = k2_mcart_1(X6) | ~r2_hidden(X6,k1_xboole_0)) ) | ~spl10_7),
% 1.32/0.57    inference(duplicate_literal_removal,[],[f265])).
% 1.32/0.57  fof(f265,plain,(
% 1.32/0.57    ( ! [X6] : (sK0 = k2_mcart_1(X6) | ~r2_hidden(X6,k1_xboole_0) | ~r2_hidden(X6,k1_xboole_0)) ) | ~spl10_7),
% 1.32/0.57    inference(superposition,[],[f190,f209])).
% 1.32/0.57  fof(f209,plain,(
% 1.32/0.57    ( ! [X10,X11] : (sK7(k1_xboole_0,X10,X11) = k2_mcart_1(X11) | ~r2_hidden(X11,k1_xboole_0)) ) | ~spl10_7),
% 1.32/0.57    inference(superposition,[],[f35,f202])).
% 1.32/0.57  fof(f202,plain,(
% 1.32/0.57    ( ! [X0,X1] : (k4_tarski(sK0,sK7(k1_xboole_0,X0,X1)) = X1 | ~r2_hidden(X1,k1_xboole_0)) ) | ~spl10_7),
% 1.32/0.57    inference(duplicate_literal_removal,[],[f201])).
% 1.32/0.57  fof(f201,plain,(
% 1.32/0.57    ( ! [X0,X1] : (~r2_hidden(X1,k1_xboole_0) | k4_tarski(sK0,sK7(k1_xboole_0,X0,X1)) = X1 | ~r2_hidden(X1,k1_xboole_0)) ) | ~spl10_7),
% 1.32/0.57    inference(forward_demodulation,[],[f194,f72])).
% 1.32/0.57  fof(f72,plain,(
% 1.32/0.57    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.32/0.57    inference(equality_resolution,[],[f52])).
% 1.32/0.57  fof(f52,plain,(
% 1.32/0.57    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X0) )),
% 1.32/0.57    inference(cnf_transformation,[],[f30])).
% 1.32/0.57  fof(f30,plain,(
% 1.32/0.57    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 1.32/0.57    inference(flattening,[],[f29])).
% 1.32/0.57  fof(f29,plain,(
% 1.32/0.57    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 1.32/0.57    inference(nnf_transformation,[],[f6])).
% 1.32/0.57  fof(f6,axiom,(
% 1.32/0.57    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.32/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.32/0.57  fof(f194,plain,(
% 1.32/0.57    ( ! [X0,X1] : (k4_tarski(sK0,sK7(k1_xboole_0,X0,X1)) = X1 | ~r2_hidden(X1,k2_zfmisc_1(k1_xboole_0,X0)) | ~r2_hidden(X1,k1_xboole_0)) ) | ~spl10_7),
% 1.32/0.57    inference(superposition,[],[f65,f189])).
% 1.32/0.57  fof(f189,plain,(
% 1.32/0.57    ( ! [X0,X1] : (sK0 = sK6(k1_xboole_0,X0,X1) | ~r2_hidden(X1,k1_xboole_0)) ) | ~spl10_7),
% 1.32/0.57    inference(forward_demodulation,[],[f185,f72])).
% 1.32/0.57  fof(f185,plain,(
% 1.32/0.57    ( ! [X0,X1] : (sK0 = sK6(k1_xboole_0,X0,X1) | ~r2_hidden(X1,k2_zfmisc_1(k1_xboole_0,X0))) ) | ~spl10_7),
% 1.32/0.57    inference(resolution,[],[f175,f67])).
% 1.32/0.57  fof(f67,plain,(
% 1.32/0.57    ( ! [X0,X8,X1] : (r2_hidden(sK6(X0,X1,X8),X0) | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 1.32/0.57    inference(equality_resolution,[],[f36])).
% 1.32/0.57  fof(f36,plain,(
% 1.32/0.57    ( ! [X2,X0,X8,X1] : (r2_hidden(sK6(X0,X1,X8),X0) | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 1.32/0.57    inference(cnf_transformation,[],[f22])).
% 1.32/0.57  fof(f22,plain,(
% 1.32/0.57    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ((! [X4,X5] : (k4_tarski(X4,X5) != sK3(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((sK3(X0,X1,X2) = k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)) & r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & ((k4_tarski(sK6(X0,X1,X8),sK7(X0,X1,X8)) = X8 & r2_hidden(sK7(X0,X1,X8),X1) & r2_hidden(sK6(X0,X1,X8),X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 1.32/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7])],[f18,f21,f20,f19])).
% 1.32/0.57  fof(f19,plain,(
% 1.32/0.57    ! [X2,X1,X0] : (? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2))) => ((! [X5,X4] : (k4_tarski(X4,X5) != sK3(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (? [X7,X6] : (k4_tarski(X6,X7) = sK3(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 1.32/0.57    introduced(choice_axiom,[])).
% 1.32/0.57  fof(f20,plain,(
% 1.32/0.57    ! [X2,X1,X0] : (? [X7,X6] : (k4_tarski(X6,X7) = sK3(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) => (sK3(X0,X1,X2) = k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)) & r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)))),
% 1.32/0.57    introduced(choice_axiom,[])).
% 1.32/0.57  fof(f21,plain,(
% 1.32/0.57    ! [X8,X1,X0] : (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) => (k4_tarski(sK6(X0,X1,X8),sK7(X0,X1,X8)) = X8 & r2_hidden(sK7(X0,X1,X8),X1) & r2_hidden(sK6(X0,X1,X8),X0)))),
% 1.32/0.57    introduced(choice_axiom,[])).
% 1.32/0.57  fof(f18,plain,(
% 1.32/0.57    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 1.32/0.57    inference(rectify,[],[f17])).
% 1.32/0.57  fof(f17,plain,(
% 1.32/0.57    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0))) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X3,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 1.32/0.57    inference(nnf_transformation,[],[f5])).
% 1.32/0.57  fof(f5,axiom,(
% 1.32/0.57    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 1.32/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).
% 1.32/0.57  fof(f175,plain,(
% 1.32/0.57    ( ! [X2] : (~r2_hidden(X2,k1_xboole_0) | sK0 = X2) ) | ~spl10_7),
% 1.32/0.57    inference(superposition,[],[f70,f132])).
% 1.32/0.57  fof(f132,plain,(
% 1.32/0.57    k1_xboole_0 = k2_tarski(sK0,sK0) | ~spl10_7),
% 1.32/0.57    inference(avatar_component_clause,[],[f130])).
% 1.32/0.57  fof(f65,plain,(
% 1.32/0.57    ( ! [X0,X8,X1] : (k4_tarski(sK6(X0,X1,X8),sK7(X0,X1,X8)) = X8 | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 1.32/0.57    inference(equality_resolution,[],[f38])).
% 1.32/0.57  fof(f38,plain,(
% 1.32/0.57    ( ! [X2,X0,X8,X1] : (k4_tarski(sK6(X0,X1,X8),sK7(X0,X1,X8)) = X8 | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 1.32/0.57    inference(cnf_transformation,[],[f22])).
% 1.32/0.57  fof(f35,plain,(
% 1.32/0.57    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 1.32/0.57    inference(cnf_transformation,[],[f8])).
% 1.32/0.57  fof(f8,axiom,(
% 1.32/0.57    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 1.32/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).
% 1.32/0.57  fof(f190,plain,(
% 1.32/0.57    ( ! [X2,X3] : (sK0 = sK7(X2,k1_xboole_0,X3) | ~r2_hidden(X3,k1_xboole_0)) ) | ~spl10_7),
% 1.32/0.57    inference(forward_demodulation,[],[f186,f71])).
% 1.32/0.57  fof(f71,plain,(
% 1.32/0.57    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.32/0.57    inference(equality_resolution,[],[f53])).
% 1.32/0.57  fof(f53,plain,(
% 1.32/0.57    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 1.32/0.57    inference(cnf_transformation,[],[f30])).
% 1.32/0.57  fof(f186,plain,(
% 1.32/0.57    ( ! [X2,X3] : (sK0 = sK7(X2,k1_xboole_0,X3) | ~r2_hidden(X3,k2_zfmisc_1(X2,k1_xboole_0))) ) | ~spl10_7),
% 1.32/0.57    inference(resolution,[],[f175,f66])).
% 1.32/0.57  fof(f66,plain,(
% 1.32/0.57    ( ! [X0,X8,X1] : (r2_hidden(sK7(X0,X1,X8),X1) | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 1.32/0.57    inference(equality_resolution,[],[f37])).
% 1.32/0.57  fof(f37,plain,(
% 1.32/0.57    ( ! [X2,X0,X8,X1] : (r2_hidden(sK7(X0,X1,X8),X1) | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 1.32/0.57    inference(cnf_transformation,[],[f22])).
% 1.32/0.57  fof(f272,plain,(
% 1.32/0.57    ( ! [X4,X5] : (r2_hidden(k2_mcart_1(X5),X4) | ~r2_hidden(X5,k1_xboole_0)) ) | ~spl10_7),
% 1.32/0.57    inference(duplicate_literal_removal,[],[f271])).
% 1.32/0.57  fof(f271,plain,(
% 1.32/0.57    ( ! [X4,X5] : (~r2_hidden(X5,k1_xboole_0) | r2_hidden(k2_mcart_1(X5),X4) | ~r2_hidden(X5,k1_xboole_0)) ) | ~spl10_7),
% 1.32/0.57    inference(forward_demodulation,[],[f264,f72])).
% 1.32/0.57  fof(f264,plain,(
% 1.32/0.57    ( ! [X4,X5] : (r2_hidden(k2_mcart_1(X5),X4) | ~r2_hidden(X5,k2_zfmisc_1(k1_xboole_0,X4)) | ~r2_hidden(X5,k1_xboole_0)) ) | ~spl10_7),
% 1.32/0.57    inference(superposition,[],[f66,f209])).
% 1.32/0.57  fof(f222,plain,(
% 1.32/0.57    k1_mcart_1(sK0) != sK1 | sK0 != k1_mcart_1(sK0) | r2_hidden(sK1,k2_tarski(sK0,sK0)) | ~r2_hidden(sK0,k2_tarski(sK0,sK0))),
% 1.32/0.57    introduced(theory_tautology_sat_conflict,[])).
% 1.32/0.57  fof(f177,plain,(
% 1.32/0.57    spl10_11 | ~spl10_7),
% 1.32/0.57    inference(avatar_split_clause,[],[f176,f130,f155])).
% 1.32/0.57  fof(f176,plain,(
% 1.32/0.57    r2_hidden(sK0,k1_xboole_0) | ~spl10_7),
% 1.32/0.57    inference(superposition,[],[f69,f132])).
% 1.32/0.57  fof(f69,plain,(
% 1.32/0.57    ( ! [X3] : (r2_hidden(X3,k2_tarski(X3,X3))) )),
% 1.32/0.57    inference(equality_resolution,[],[f68])).
% 1.32/0.57  fof(f68,plain,(
% 1.32/0.57    ( ! [X3,X1] : (r2_hidden(X3,X1) | k2_tarski(X3,X3) != X1) )),
% 1.32/0.57    inference(equality_resolution,[],[f59])).
% 1.32/0.57  fof(f59,plain,(
% 1.32/0.57    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k2_tarski(X0,X0) != X1) )),
% 1.32/0.57    inference(definition_unfolding,[],[f48,f56])).
% 1.32/0.57  fof(f48,plain,(
% 1.32/0.57    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 1.32/0.57    inference(cnf_transformation,[],[f28])).
% 1.32/0.57  fof(f169,plain,(
% 1.32/0.57    spl10_12),
% 1.32/0.57    inference(avatar_contradiction_clause,[],[f166])).
% 1.32/0.57  fof(f166,plain,(
% 1.32/0.57    $false | spl10_12),
% 1.32/0.57    inference(unit_resulting_resolution,[],[f69,f164])).
% 1.32/0.57  fof(f164,plain,(
% 1.32/0.57    ~r2_hidden(sK0,k2_tarski(sK0,sK0)) | spl10_12),
% 1.32/0.57    inference(avatar_component_clause,[],[f162])).
% 1.32/0.57  fof(f162,plain,(
% 1.32/0.57    spl10_12 <=> r2_hidden(sK0,k2_tarski(sK0,sK0))),
% 1.32/0.57    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).
% 1.32/0.57  fof(f165,plain,(
% 1.32/0.57    spl10_7 | ~spl10_12 | ~spl10_6),
% 1.32/0.57    inference(avatar_split_clause,[],[f160,f103,f162,f130])).
% 1.32/0.57  fof(f103,plain,(
% 1.32/0.57    spl10_6 <=> sK0 = k4_tarski(sK1,sK0)),
% 1.32/0.57    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).
% 1.32/0.57  fof(f160,plain,(
% 1.32/0.57    ~r2_hidden(sK0,k2_tarski(sK0,sK0)) | k1_xboole_0 = k2_tarski(sK0,sK0) | ~spl10_6),
% 1.32/0.57    inference(equality_resolution,[],[f139])).
% 1.32/0.57  fof(f139,plain,(
% 1.32/0.57    ( ! [X0] : (sK0 != X0 | ~r2_hidden(sK0,k2_tarski(X0,X0)) | k2_tarski(X0,X0) = k1_xboole_0) ) | ~spl10_6),
% 1.32/0.57    inference(duplicate_literal_removal,[],[f138])).
% 1.32/0.57  fof(f138,plain,(
% 1.32/0.57    ( ! [X0] : (sK0 != X0 | ~r2_hidden(sK0,k2_tarski(X0,X0)) | k2_tarski(X0,X0) = k1_xboole_0 | k2_tarski(X0,X0) = k1_xboole_0) ) | ~spl10_6),
% 1.32/0.57    inference(superposition,[],[f125,f110])).
% 1.32/0.57  fof(f110,plain,(
% 1.32/0.57    ( ! [X1] : (sK8(k2_tarski(X1,X1)) = X1 | k1_xboole_0 = k2_tarski(X1,X1)) )),
% 1.32/0.57    inference(resolution,[],[f70,f44])).
% 1.32/0.57  fof(f44,plain,(
% 1.32/0.57    ( ! [X0] : (r2_hidden(sK8(X0),X0) | k1_xboole_0 = X0) )),
% 1.32/0.57    inference(cnf_transformation,[],[f24])).
% 1.32/0.57  fof(f24,plain,(
% 1.32/0.57    ! [X0] : ((! [X2,X3] : (k4_tarski(X2,X3) != sK8(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK8(X0),X0)) | k1_xboole_0 = X0)),
% 1.32/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f13,f23])).
% 1.32/0.57  fof(f23,plain,(
% 1.32/0.57    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X3,X2] : (k4_tarski(X2,X3) != sK8(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK8(X0),X0)))),
% 1.32/0.57    introduced(choice_axiom,[])).
% 1.32/0.57  fof(f13,plain,(
% 1.32/0.57    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 1.32/0.57    inference(ennf_transformation,[],[f9])).
% 1.32/0.57  fof(f9,axiom,(
% 1.32/0.57    ! [X0] : ~(! [X1] : ~(! [X2,X3] : ~(k4_tarski(X2,X3) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 1.32/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).
% 1.32/0.57  fof(f125,plain,(
% 1.32/0.57    ( ! [X1] : (sK0 != sK8(X1) | ~r2_hidden(sK0,X1) | k1_xboole_0 = X1) ) | ~spl10_6),
% 1.32/0.57    inference(superposition,[],[f46,f105])).
% 1.32/0.57  fof(f105,plain,(
% 1.32/0.57    sK0 = k4_tarski(sK1,sK0) | ~spl10_6),
% 1.32/0.57    inference(avatar_component_clause,[],[f103])).
% 1.32/0.57  fof(f46,plain,(
% 1.32/0.57    ( ! [X2,X0,X3] : (k4_tarski(X2,X3) != sK8(X0) | ~r2_hidden(X3,X0) | k1_xboole_0 = X0) )),
% 1.32/0.57    inference(cnf_transformation,[],[f24])).
% 1.32/0.57  fof(f137,plain,(
% 1.32/0.57    spl10_7 | ~spl10_8 | ~spl10_1),
% 1.32/0.57    inference(avatar_split_clause,[],[f123,f75,f134,f130])).
% 1.32/0.57  fof(f134,plain,(
% 1.32/0.57    spl10_8 <=> r2_hidden(sK1,k2_tarski(sK0,sK0))),
% 1.32/0.57    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).
% 1.32/0.57  fof(f75,plain,(
% 1.32/0.57    spl10_1 <=> sK0 = k4_tarski(sK1,sK2)),
% 1.32/0.57    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 1.32/0.57  fof(f123,plain,(
% 1.32/0.57    ~r2_hidden(sK1,k2_tarski(sK0,sK0)) | k1_xboole_0 = k2_tarski(sK0,sK0) | ~spl10_1),
% 1.32/0.57    inference(equality_resolution,[],[f122])).
% 1.32/0.57  fof(f122,plain,(
% 1.32/0.57    ( ! [X0] : (sK0 != X0 | ~r2_hidden(sK1,k2_tarski(X0,X0)) | k2_tarski(X0,X0) = k1_xboole_0) ) | ~spl10_1),
% 1.32/0.57    inference(duplicate_literal_removal,[],[f117])).
% 1.32/0.57  fof(f117,plain,(
% 1.32/0.57    ( ! [X0] : (sK0 != X0 | ~r2_hidden(sK1,k2_tarski(X0,X0)) | k2_tarski(X0,X0) = k1_xboole_0 | k2_tarski(X0,X0) = k1_xboole_0) ) | ~spl10_1),
% 1.32/0.57    inference(superposition,[],[f115,f110])).
% 1.32/0.57  fof(f115,plain,(
% 1.32/0.57    ( ! [X0] : (sK0 != sK8(X0) | ~r2_hidden(sK1,X0) | k1_xboole_0 = X0) ) | ~spl10_1),
% 1.32/0.57    inference(superposition,[],[f45,f77])).
% 1.32/0.57  fof(f77,plain,(
% 1.32/0.57    sK0 = k4_tarski(sK1,sK2) | ~spl10_1),
% 1.32/0.57    inference(avatar_component_clause,[],[f75])).
% 1.32/0.57  fof(f45,plain,(
% 1.32/0.57    ( ! [X2,X0,X3] : (k4_tarski(X2,X3) != sK8(X0) | ~r2_hidden(X2,X0) | k1_xboole_0 = X0) )),
% 1.32/0.57    inference(cnf_transformation,[],[f24])).
% 1.32/0.57  fof(f106,plain,(
% 1.32/0.57    spl10_6 | ~spl10_1 | ~spl10_5),
% 1.32/0.57    inference(avatar_split_clause,[],[f101,f97,f75,f103])).
% 1.32/0.57  fof(f97,plain,(
% 1.32/0.57    spl10_5 <=> sK0 = sK2),
% 1.32/0.57    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).
% 1.32/0.57  fof(f101,plain,(
% 1.32/0.57    sK0 = k4_tarski(sK1,sK0) | (~spl10_1 | ~spl10_5)),
% 1.32/0.57    inference(superposition,[],[f77,f99])).
% 1.32/0.57  fof(f99,plain,(
% 1.32/0.57    sK0 = sK2 | ~spl10_5),
% 1.32/0.57    inference(avatar_component_clause,[],[f97])).
% 1.32/0.57  fof(f100,plain,(
% 1.32/0.57    spl10_5 | ~spl10_1 | ~spl10_3),
% 1.32/0.57    inference(avatar_split_clause,[],[f95,f84,f75,f97])).
% 1.32/0.57  fof(f84,plain,(
% 1.32/0.57    spl10_3 <=> sK0 = k2_mcart_1(sK0)),
% 1.32/0.57    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).
% 1.32/0.57  fof(f95,plain,(
% 1.32/0.57    sK0 = sK2 | (~spl10_1 | ~spl10_3)),
% 1.32/0.57    inference(forward_demodulation,[],[f94,f86])).
% 1.32/0.57  fof(f86,plain,(
% 1.32/0.57    sK0 = k2_mcart_1(sK0) | ~spl10_3),
% 1.32/0.57    inference(avatar_component_clause,[],[f84])).
% 1.32/0.57  fof(f94,plain,(
% 1.32/0.57    k2_mcart_1(sK0) = sK2 | ~spl10_1),
% 1.32/0.57    inference(superposition,[],[f35,f77])).
% 1.32/0.57  fof(f93,plain,(
% 1.32/0.57    spl10_4 | ~spl10_1),
% 1.32/0.57    inference(avatar_split_clause,[],[f88,f75,f90])).
% 1.32/0.57  fof(f90,plain,(
% 1.32/0.57    spl10_4 <=> k1_mcart_1(sK0) = sK1),
% 1.32/0.57    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).
% 1.32/0.57  fof(f88,plain,(
% 1.32/0.57    k1_mcart_1(sK0) = sK1 | ~spl10_1),
% 1.32/0.57    inference(superposition,[],[f34,f77])).
% 1.32/0.57  fof(f34,plain,(
% 1.32/0.57    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 1.32/0.57    inference(cnf_transformation,[],[f8])).
% 1.32/0.57  fof(f87,plain,(
% 1.32/0.57    spl10_2 | spl10_3),
% 1.32/0.57    inference(avatar_split_clause,[],[f33,f84,f80])).
% 1.32/0.57  fof(f80,plain,(
% 1.32/0.57    spl10_2 <=> sK0 = k1_mcart_1(sK0)),
% 1.32/0.57    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 1.32/0.57  fof(f33,plain,(
% 1.32/0.57    sK0 = k2_mcart_1(sK0) | sK0 = k1_mcart_1(sK0)),
% 1.32/0.57    inference(cnf_transformation,[],[f16])).
% 1.32/0.57  fof(f16,plain,(
% 1.32/0.57    (sK0 = k2_mcart_1(sK0) | sK0 = k1_mcart_1(sK0)) & sK0 = k4_tarski(sK1,sK2)),
% 1.32/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f15,f14])).
% 1.32/0.57  fof(f14,plain,(
% 1.32/0.57    ? [X0] : ((k2_mcart_1(X0) = X0 | k1_mcart_1(X0) = X0) & ? [X1,X2] : k4_tarski(X1,X2) = X0) => ((sK0 = k2_mcart_1(sK0) | sK0 = k1_mcart_1(sK0)) & ? [X2,X1] : k4_tarski(X1,X2) = sK0)),
% 1.32/0.57    introduced(choice_axiom,[])).
% 1.32/0.57  fof(f15,plain,(
% 1.32/0.57    ? [X2,X1] : k4_tarski(X1,X2) = sK0 => sK0 = k4_tarski(sK1,sK2)),
% 1.32/0.57    introduced(choice_axiom,[])).
% 1.32/0.57  fof(f12,plain,(
% 1.32/0.57    ? [X0] : ((k2_mcart_1(X0) = X0 | k1_mcart_1(X0) = X0) & ? [X1,X2] : k4_tarski(X1,X2) = X0)),
% 1.32/0.57    inference(ennf_transformation,[],[f11])).
% 1.32/0.57  fof(f11,negated_conjecture,(
% 1.32/0.57    ~! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 1.32/0.57    inference(negated_conjecture,[],[f10])).
% 1.32/0.57  fof(f10,conjecture,(
% 1.32/0.57    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 1.32/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).
% 1.32/0.57  fof(f78,plain,(
% 1.32/0.57    spl10_1),
% 1.32/0.57    inference(avatar_split_clause,[],[f32,f75])).
% 1.32/0.57  fof(f32,plain,(
% 1.32/0.57    sK0 = k4_tarski(sK1,sK2)),
% 1.32/0.57    inference(cnf_transformation,[],[f16])).
% 1.32/0.57  % SZS output end Proof for theBenchmark
% 1.32/0.57  % (641)------------------------------
% 1.32/0.57  % (641)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.57  % (641)Termination reason: Refutation
% 1.32/0.57  
% 1.32/0.57  % (641)Memory used [KB]: 10874
% 1.32/0.57  % (641)Time elapsed: 0.169 s
% 1.32/0.57  % (641)------------------------------
% 1.32/0.57  % (641)------------------------------
% 1.32/0.57  % (642)Refutation not found, incomplete strategy% (642)------------------------------
% 1.32/0.57  % (642)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.57  % (642)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.57  
% 1.32/0.57  % (642)Memory used [KB]: 10746
% 1.32/0.57  % (642)Time elapsed: 0.167 s
% 1.32/0.57  % (642)------------------------------
% 1.32/0.57  % (642)------------------------------
% 1.32/0.58  % (612)Success in time 0.215 s
%------------------------------------------------------------------------------
