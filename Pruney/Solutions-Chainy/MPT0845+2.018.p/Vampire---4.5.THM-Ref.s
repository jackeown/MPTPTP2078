%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:08 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 116 expanded)
%              Number of leaves         :   19 (  48 expanded)
%              Depth                    :    9
%              Number of atoms          :  253 ( 423 expanded)
%              Number of equality atoms :   48 (  69 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f384,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f50,f213,f217,f252,f327,f328,f337,f379])).

fof(f379,plain,
    ( spl8_9
    | ~ spl8_6
    | ~ spl8_7 ),
    inference(avatar_split_clause,[],[f373,f215,f211,f249])).

fof(f249,plain,
    ( spl8_9
  <=> ! [X10] : ~ r2_hidden(X10,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f211,plain,
    ( spl8_6
  <=> r2_hidden(sK1(sK2(sK0),sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f215,plain,
    ( spl8_7
  <=> r2_hidden(sK1(sK2(sK0),sK0),sK2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f373,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK1(sK2(sK0),sK0),sK0)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl8_7 ),
    inference(resolution,[],[f216,f32])).

fof(f32,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,sK2(X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ! [X3] :
            ( ~ r2_hidden(X3,sK2(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK2(X1),X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f11,f17])).

fof(f17,plain,(
    ! [X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
     => ( ! [X3] :
            ( ~ r2_hidden(X3,sK2(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK2(X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ! [X3] :
                  ~ ( r2_hidden(X3,X2)
                    & r2_hidden(X3,X1) )
              & r2_hidden(X2,X1) )
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tarski)).

fof(f216,plain,
    ( r2_hidden(sK1(sK2(sK0),sK0),sK2(sK0))
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f215])).

fof(f337,plain,
    ( ~ spl8_6
    | ~ spl8_9 ),
    inference(avatar_contradiction_clause,[],[f331])).

fof(f331,plain,
    ( $false
    | ~ spl8_6
    | ~ spl8_9 ),
    inference(resolution,[],[f212,f250])).

fof(f250,plain,
    ( ! [X10] : ~ r2_hidden(X10,sK0)
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f249])).

fof(f212,plain,
    ( r2_hidden(sK1(sK2(sK0),sK0),sK0)
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f211])).

fof(f328,plain,
    ( ~ spl8_4
    | spl8_5
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f199,f177,f205,f202])).

fof(f202,plain,
    ( spl8_4
  <=> r1_xboole_0(sK2(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f205,plain,
    ( spl8_5
  <=> ! [X24] : sK0 = k2_zfmisc_1(sK0,X24) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f177,plain,
    ( spl8_3
  <=> ! [X1,X0] :
        ( k2_zfmisc_1(sK0,X0) = X1
        | r2_hidden(sK3(sK0,X0,X1),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f199,plain,
    ( ! [X24] :
        ( sK0 = k2_zfmisc_1(sK0,X24)
        | ~ r1_xboole_0(sK2(sK0),sK0) )
    | ~ spl8_3 ),
    inference(resolution,[],[f184,f26])).

fof(f26,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK0)
      | ~ r1_xboole_0(X1,sK0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ! [X1] :
        ( ~ r1_xboole_0(X1,sK0)
        | ~ r2_hidden(X1,sK0) )
    & k1_xboole_0 != sK0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f13])).

fof(f13,plain,
    ( ? [X0] :
        ( ! [X1] :
            ( ~ r1_xboole_0(X1,X0)
            | ~ r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 )
   => ( ! [X1] :
          ( ~ r1_xboole_0(X1,sK0)
          | ~ r2_hidden(X1,sK0) )
      & k1_xboole_0 != sK0 ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] :
      ( ! [X1] :
          ( ~ r1_xboole_0(X1,X0)
          | ~ r2_hidden(X1,X0) )
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ~ ( ! [X1] :
              ~ ( r1_xboole_0(X1,X0)
                & r2_hidden(X1,X0) )
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( r1_xboole_0(X1,X0)
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_mcart_1)).

fof(f184,plain,
    ( ! [X14,X15] :
        ( r2_hidden(sK2(X15),X15)
        | k2_zfmisc_1(sK0,X14) = X15 )
    | ~ spl8_3 ),
    inference(resolution,[],[f178,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r2_hidden(sK2(X1),X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f178,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK3(sK0,X0,X1),X1)
        | k2_zfmisc_1(sK0,X0) = X1 )
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f177])).

fof(f327,plain,
    ( spl8_1
    | ~ spl8_3
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f323,f205,f177,f48])).

fof(f48,plain,
    ( spl8_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f323,plain,
    ( k1_xboole_0 = sK0
    | ~ spl8_3
    | ~ spl8_5 ),
    inference(resolution,[],[f253,f27])).

fof(f27,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f253,plain,
    ( ! [X12,X11] :
        ( ~ r1_xboole_0(k2_tarski(sK2(X11),X12),X11)
        | sK0 = X11 )
    | ~ spl8_3
    | ~ spl8_5 ),
    inference(forward_demodulation,[],[f194,f206])).

fof(f206,plain,
    ( ! [X24] : sK0 = k2_zfmisc_1(sK0,X24)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f205])).

fof(f194,plain,
    ( ! [X12,X10,X11] :
        ( k2_zfmisc_1(sK0,X10) = X11
        | ~ r1_xboole_0(k2_tarski(sK2(X11),X12),X11) )
    | ~ spl8_3 ),
    inference(resolution,[],[f184,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ~ ( r2_hidden(X0,X2)
        & r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_zfmisc_1)).

fof(f252,plain,
    ( ~ spl8_4
    | spl8_3 ),
    inference(avatar_split_clause,[],[f229,f177,f202])).

fof(f229,plain,(
    ! [X33,X32] :
      ( r2_hidden(sK3(sK0,X32,X33),X33)
      | k2_zfmisc_1(sK0,X32) = X33
      | ~ r1_xboole_0(sK2(sK0),sK0) ) ),
    inference(resolution,[],[f54,f26])).

fof(f54,plain,(
    ! [X14,X15,X13] :
      ( r2_hidden(sK2(X13),X13)
      | r2_hidden(sK3(X13,X14,X15),X15)
      | k2_zfmisc_1(X13,X14) = X15 ) ),
    inference(resolution,[],[f37,f31])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X0)
      | k2_zfmisc_1(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7])],[f20,f23,f22,f21])).

fof(f21,plain,(
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

fof(f22,plain,(
    ! [X2,X1,X0] :
      ( ? [X7,X6] :
          ( k4_tarski(X6,X7) = sK3(X0,X1,X2)
          & r2_hidden(X7,X1)
          & r2_hidden(X6,X0) )
     => ( sK3(X0,X1,X2) = k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2))
        & r2_hidden(sK5(X0,X1,X2),X1)
        & r2_hidden(sK4(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X8,X1,X0] :
      ( ? [X11,X12] :
          ( k4_tarski(X11,X12) = X8
          & r2_hidden(X12,X1)
          & r2_hidden(X11,X0) )
     => ( k4_tarski(sK6(X0,X1,X8),sK7(X0,X1,X8)) = X8
        & r2_hidden(sK7(X0,X1,X8),X1)
        & r2_hidden(sK6(X0,X1,X8),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
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
    inference(rectify,[],[f19])).

fof(f19,plain,(
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
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(f217,plain,
    ( spl8_7
    | spl8_4 ),
    inference(avatar_split_clause,[],[f209,f202,f215])).

fof(f209,plain,
    ( r2_hidden(sK1(sK2(sK0),sK0),sK2(sK0))
    | spl8_4 ),
    inference(resolution,[],[f203,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f10,f15])).

fof(f15,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f203,plain,
    ( ~ r1_xboole_0(sK2(sK0),sK0)
    | spl8_4 ),
    inference(avatar_component_clause,[],[f202])).

fof(f213,plain,
    ( spl8_6
    | spl8_4 ),
    inference(avatar_split_clause,[],[f208,f202,f211])).

fof(f208,plain,
    ( r2_hidden(sK1(sK2(sK0),sK0),sK0)
    | spl8_4 ),
    inference(resolution,[],[f203,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f50,plain,(
    ~ spl8_1 ),
    inference(avatar_split_clause,[],[f25,f48])).

fof(f25,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:02:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (30491)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.48  % (30489)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.48  % (30502)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.48  % (30489)Refutation not found, incomplete strategy% (30489)------------------------------
% 0.21/0.48  % (30489)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (30502)Refutation not found, incomplete strategy% (30502)------------------------------
% 0.21/0.48  % (30502)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (30490)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.48  % (30502)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (30502)Memory used [KB]: 6140
% 0.21/0.48  % (30502)Time elapsed: 0.004 s
% 0.21/0.48  % (30502)------------------------------
% 0.21/0.48  % (30502)------------------------------
% 0.21/0.48  % (30489)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (30489)Memory used [KB]: 10618
% 0.21/0.48  % (30489)Time elapsed: 0.072 s
% 0.21/0.48  % (30489)------------------------------
% 0.21/0.48  % (30489)------------------------------
% 0.21/0.48  % (30495)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.49  % (30493)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.49  % (30499)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.49  % (30503)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.49  % (30492)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.49  % (30494)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.49  % (30488)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.50  % (30504)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.50  % (30496)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.50  % (30492)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f384,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f50,f213,f217,f252,f327,f328,f337,f379])).
% 0.21/0.50  fof(f379,plain,(
% 0.21/0.50    spl8_9 | ~spl8_6 | ~spl8_7),
% 0.21/0.50    inference(avatar_split_clause,[],[f373,f215,f211,f249])).
% 0.21/0.50  fof(f249,plain,(
% 0.21/0.50    spl8_9 <=> ! [X10] : ~r2_hidden(X10,sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 0.21/0.50  fof(f211,plain,(
% 0.21/0.50    spl8_6 <=> r2_hidden(sK1(sK2(sK0),sK0),sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.21/0.50  fof(f215,plain,(
% 0.21/0.50    spl8_7 <=> r2_hidden(sK1(sK2(sK0),sK0),sK2(sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 0.21/0.50  fof(f373,plain,(
% 0.21/0.50    ( ! [X0] : (~r2_hidden(sK1(sK2(sK0),sK0),sK0) | ~r2_hidden(X0,sK0)) ) | ~spl8_7),
% 0.21/0.50    inference(resolution,[],[f216,f32])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ( ! [X0,X3,X1] : (~r2_hidden(X3,sK2(X1)) | ~r2_hidden(X3,X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ! [X0,X1] : ((! [X3] : (~r2_hidden(X3,sK2(X1)) | ~r2_hidden(X3,X1)) & r2_hidden(sK2(X1),X1)) | ~r2_hidden(X0,X1))),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f11,f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ! [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) => (! [X3] : (~r2_hidden(X3,sK2(X1)) | ~r2_hidden(X3,X1)) & r2_hidden(sK2(X1),X1)))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f11,plain,(
% 0.21/0.50    ! [X0,X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) | ~r2_hidden(X0,X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0,X1] : ~(! [X2] : ~(! [X3] : ~(r2_hidden(X3,X2) & r2_hidden(X3,X1)) & r2_hidden(X2,X1)) & r2_hidden(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tarski)).
% 0.21/0.50  fof(f216,plain,(
% 0.21/0.50    r2_hidden(sK1(sK2(sK0),sK0),sK2(sK0)) | ~spl8_7),
% 0.21/0.50    inference(avatar_component_clause,[],[f215])).
% 0.21/0.50  fof(f337,plain,(
% 0.21/0.50    ~spl8_6 | ~spl8_9),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f331])).
% 0.21/0.50  fof(f331,plain,(
% 0.21/0.50    $false | (~spl8_6 | ~spl8_9)),
% 0.21/0.50    inference(resolution,[],[f212,f250])).
% 0.21/0.50  fof(f250,plain,(
% 0.21/0.50    ( ! [X10] : (~r2_hidden(X10,sK0)) ) | ~spl8_9),
% 0.21/0.50    inference(avatar_component_clause,[],[f249])).
% 0.21/0.50  fof(f212,plain,(
% 0.21/0.50    r2_hidden(sK1(sK2(sK0),sK0),sK0) | ~spl8_6),
% 0.21/0.50    inference(avatar_component_clause,[],[f211])).
% 0.21/0.50  fof(f328,plain,(
% 0.21/0.50    ~spl8_4 | spl8_5 | ~spl8_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f199,f177,f205,f202])).
% 0.21/0.50  fof(f202,plain,(
% 0.21/0.50    spl8_4 <=> r1_xboole_0(sK2(sK0),sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.21/0.50  fof(f205,plain,(
% 0.21/0.50    spl8_5 <=> ! [X24] : sK0 = k2_zfmisc_1(sK0,X24)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.21/0.50  fof(f177,plain,(
% 0.21/0.50    spl8_3 <=> ! [X1,X0] : (k2_zfmisc_1(sK0,X0) = X1 | r2_hidden(sK3(sK0,X0,X1),X1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.21/0.50  fof(f199,plain,(
% 0.21/0.50    ( ! [X24] : (sK0 = k2_zfmisc_1(sK0,X24) | ~r1_xboole_0(sK2(sK0),sK0)) ) | ~spl8_3),
% 0.21/0.50    inference(resolution,[],[f184,f26])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ( ! [X1] : (~r2_hidden(X1,sK0) | ~r1_xboole_0(X1,sK0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f14])).
% 0.21/0.50  fof(f14,plain,(
% 0.21/0.50    ! [X1] : (~r1_xboole_0(X1,sK0) | ~r2_hidden(X1,sK0)) & k1_xboole_0 != sK0),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f13])).
% 0.21/0.50  fof(f13,plain,(
% 0.21/0.50    ? [X0] : (! [X1] : (~r1_xboole_0(X1,X0) | ~r2_hidden(X1,X0)) & k1_xboole_0 != X0) => (! [X1] : (~r1_xboole_0(X1,sK0) | ~r2_hidden(X1,sK0)) & k1_xboole_0 != sK0)),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f9,plain,(
% 0.21/0.50    ? [X0] : (! [X1] : (~r1_xboole_0(X1,X0) | ~r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.21/0.50    inference(ennf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,negated_conjecture,(
% 0.21/0.50    ~! [X0] : ~(! [X1] : ~(r1_xboole_0(X1,X0) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.21/0.50    inference(negated_conjecture,[],[f6])).
% 0.21/0.50  fof(f6,conjecture,(
% 0.21/0.50    ! [X0] : ~(! [X1] : ~(r1_xboole_0(X1,X0) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_mcart_1)).
% 0.21/0.50  fof(f184,plain,(
% 0.21/0.50    ( ! [X14,X15] : (r2_hidden(sK2(X15),X15) | k2_zfmisc_1(sK0,X14) = X15) ) | ~spl8_3),
% 0.21/0.50    inference(resolution,[],[f178,f31])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r2_hidden(sK2(X1),X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f178,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r2_hidden(sK3(sK0,X0,X1),X1) | k2_zfmisc_1(sK0,X0) = X1) ) | ~spl8_3),
% 0.21/0.50    inference(avatar_component_clause,[],[f177])).
% 0.21/0.50  fof(f327,plain,(
% 0.21/0.50    spl8_1 | ~spl8_3 | ~spl8_5),
% 0.21/0.50    inference(avatar_split_clause,[],[f323,f205,f177,f48])).
% 0.21/0.50  fof(f48,plain,(
% 0.21/0.50    spl8_1 <=> k1_xboole_0 = sK0),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.21/0.50  fof(f323,plain,(
% 0.21/0.50    k1_xboole_0 = sK0 | (~spl8_3 | ~spl8_5)),
% 0.21/0.50    inference(resolution,[],[f253,f27])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.21/0.50  fof(f253,plain,(
% 0.21/0.50    ( ! [X12,X11] : (~r1_xboole_0(k2_tarski(sK2(X11),X12),X11) | sK0 = X11) ) | (~spl8_3 | ~spl8_5)),
% 0.21/0.50    inference(forward_demodulation,[],[f194,f206])).
% 0.21/0.50  fof(f206,plain,(
% 0.21/0.50    ( ! [X24] : (sK0 = k2_zfmisc_1(sK0,X24)) ) | ~spl8_5),
% 0.21/0.50    inference(avatar_component_clause,[],[f205])).
% 0.21/0.50  fof(f194,plain,(
% 0.21/0.50    ( ! [X12,X10,X11] : (k2_zfmisc_1(sK0,X10) = X11 | ~r1_xboole_0(k2_tarski(sK2(X11),X12),X11)) ) | ~spl8_3),
% 0.21/0.50    inference(resolution,[],[f184,f41])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k2_tarski(X0,X1),X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f12])).
% 0.21/0.50  fof(f12,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k2_tarski(X0,X1),X2))),
% 0.21/0.50    inference(ennf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : ~(r2_hidden(X0,X2) & r1_xboole_0(k2_tarski(X0,X1),X2))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_zfmisc_1)).
% 0.21/0.50  fof(f252,plain,(
% 0.21/0.50    ~spl8_4 | spl8_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f229,f177,f202])).
% 0.21/0.50  fof(f229,plain,(
% 0.21/0.50    ( ! [X33,X32] : (r2_hidden(sK3(sK0,X32,X33),X33) | k2_zfmisc_1(sK0,X32) = X33 | ~r1_xboole_0(sK2(sK0),sK0)) )),
% 0.21/0.50    inference(resolution,[],[f54,f26])).
% 0.21/0.50  fof(f54,plain,(
% 0.21/0.50    ( ! [X14,X15,X13] : (r2_hidden(sK2(X13),X13) | r2_hidden(sK3(X13,X14,X15),X15) | k2_zfmisc_1(X13,X14) = X15) )),
% 0.21/0.50    inference(resolution,[],[f37,f31])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),X0) | k2_zfmisc_1(X0,X1) = X2 | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f24])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ((! [X4,X5] : (k4_tarski(X4,X5) != sK3(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((sK3(X0,X1,X2) = k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)) & r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & ((k4_tarski(sK6(X0,X1,X8),sK7(X0,X1,X8)) = X8 & r2_hidden(sK7(X0,X1,X8),X1) & r2_hidden(sK6(X0,X1,X8),X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7])],[f20,f23,f22,f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ! [X2,X1,X0] : (? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2))) => ((! [X5,X4] : (k4_tarski(X4,X5) != sK3(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (? [X7,X6] : (k4_tarski(X6,X7) = sK3(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ! [X2,X1,X0] : (? [X7,X6] : (k4_tarski(X6,X7) = sK3(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) => (sK3(X0,X1,X2) = k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)) & r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ! [X8,X1,X0] : (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) => (k4_tarski(sK6(X0,X1,X8),sK7(X0,X1,X8)) = X8 & r2_hidden(sK7(X0,X1,X8),X1) & r2_hidden(sK6(X0,X1,X8),X0)))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 0.21/0.50    inference(rectify,[],[f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0))) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X3,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 0.21/0.50    inference(nnf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).
% 0.21/0.50  fof(f217,plain,(
% 0.21/0.50    spl8_7 | spl8_4),
% 0.21/0.50    inference(avatar_split_clause,[],[f209,f202,f215])).
% 0.21/0.50  fof(f209,plain,(
% 0.21/0.50    r2_hidden(sK1(sK2(sK0),sK0),sK2(sK0)) | spl8_4),
% 0.21/0.50    inference(resolution,[],[f203,f28])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f16])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f10,f15])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f10,plain,(
% 0.21/0.50    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.50    inference(ennf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,plain,(
% 0.21/0.50    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.50    inference(rectify,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.21/0.50  fof(f203,plain,(
% 0.21/0.50    ~r1_xboole_0(sK2(sK0),sK0) | spl8_4),
% 0.21/0.50    inference(avatar_component_clause,[],[f202])).
% 0.21/0.50  fof(f213,plain,(
% 0.21/0.50    spl8_6 | spl8_4),
% 0.21/0.50    inference(avatar_split_clause,[],[f208,f202,f211])).
% 0.21/0.50  fof(f208,plain,(
% 0.21/0.50    r2_hidden(sK1(sK2(sK0),sK0),sK0) | spl8_4),
% 0.21/0.50    inference(resolution,[],[f203,f29])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f16])).
% 0.21/0.50  fof(f50,plain,(
% 0.21/0.50    ~spl8_1),
% 0.21/0.50    inference(avatar_split_clause,[],[f25,f48])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    k1_xboole_0 != sK0),
% 0.21/0.50    inference(cnf_transformation,[],[f14])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (30492)------------------------------
% 0.21/0.50  % (30492)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (30492)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (30492)Memory used [KB]: 11001
% 0.21/0.50  % (30492)Time elapsed: 0.091 s
% 0.21/0.50  % (30492)------------------------------
% 0.21/0.50  % (30492)------------------------------
% 0.21/0.50  % (30505)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.50  % (30483)Success in time 0.145 s
%------------------------------------------------------------------------------
