%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:13 EST 2020

% Result     : Theorem 1.14s
% Output     : Refutation 1.14s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 265 expanded)
%              Number of leaves         :   21 (  85 expanded)
%              Depth                    :   14
%              Number of atoms          :  260 ( 909 expanded)
%              Number of equality atoms :   33 ( 112 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f329,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f74,f79,f101,f111,f225,f238,f256,f261,f328])).

fof(f328,plain,
    ( spl5_16
    | ~ spl5_17 ),
    inference(avatar_contradiction_clause,[],[f322])).

fof(f322,plain,
    ( $false
    | spl5_16
    | ~ spl5_17 ),
    inference(unit_resulting_resolution,[],[f62,f255,f321])).

fof(f321,plain,
    ( ! [X0] :
        ( r1_tarski(k1_mcart_1(sK0),X0)
        | ~ r1_tarski(sK1,X0) )
    | ~ spl5_17 ),
    inference(resolution,[],[f316,f64])).

fof(f64,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK3(X0,X1),X0)
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( r1_tarski(sK3(X0,X1),X0)
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f28,f29])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK3(X0,X1),X0)
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( r1_tarski(sK3(X0,X1),X0)
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f316,plain,
    ( ! [X6] :
        ( ~ r2_hidden(sK1,k1_zfmisc_1(X6))
        | r1_tarski(k1_mcart_1(sK0),X6) )
    | ~ spl5_17 ),
    inference(resolution,[],[f309,f65])).

fof(f65,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_zfmisc_1(X0))
      | r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f46])).

% (28541)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
fof(f46,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f309,plain,
    ( ! [X1] :
        ( r2_hidden(k1_mcart_1(sK0),X1)
        | ~ r2_hidden(sK1,X1) )
    | ~ spl5_17 ),
    inference(resolution,[],[f267,f198])).

fof(f198,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,k2_enumset1(X1,X1,X1,X1))
      | r2_hidden(X1,X0) ) ),
    inference(resolution,[],[f196,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f42,f57])).

fof(f57,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f43,f56])).

fof(f56,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f53,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f53,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f43,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f196,plain,(
    ! [X2,X3] :
      ( ~ r1_xboole_0(X2,X3)
      | r1_xboole_0(X3,X2) ) ),
    inference(duplicate_literal_removal,[],[f191])).

fof(f191,plain,(
    ! [X2,X3] :
      ( ~ r1_xboole_0(X2,X3)
      | r1_xboole_0(X3,X2)
      | r1_xboole_0(X3,X2) ) ),
    inference(resolution,[],[f124,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
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

fof(f124,plain,(
    ! [X6,X8,X7] :
      ( ~ r2_hidden(sK4(X7,X8),X6)
      | ~ r1_xboole_0(X6,X7)
      | r1_xboole_0(X7,X8) ) ),
    inference(resolution,[],[f52,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f267,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(X0,k2_enumset1(k1_mcart_1(sK0),k1_mcart_1(sK0),k1_mcart_1(sK0),k1_mcart_1(sK0)))
        | ~ r2_hidden(sK1,X0) )
    | ~ spl5_17 ),
    inference(resolution,[],[f260,f52])).

fof(f260,plain,
    ( r2_hidden(sK1,k2_enumset1(k1_mcart_1(sK0),k1_mcart_1(sK0),k1_mcart_1(sK0),k1_mcart_1(sK0)))
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f258])).

fof(f258,plain,
    ( spl5_17
  <=> r2_hidden(sK1,k2_enumset1(k1_mcart_1(sK0),k1_mcart_1(sK0),k1_mcart_1(sK0),k1_mcart_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f255,plain,
    ( ~ r1_tarski(k1_mcart_1(sK0),sK1)
    | spl5_16 ),
    inference(avatar_component_clause,[],[f253])).

fof(f253,plain,
    ( spl5_16
  <=> r1_tarski(k1_mcart_1(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f62,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f261,plain,
    ( spl5_17
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f217,f98,f258])).

fof(f98,plain,
    ( spl5_5
  <=> r2_hidden(k1_mcart_1(sK0),k2_enumset1(sK1,sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f217,plain,
    ( r2_hidden(sK1,k2_enumset1(k1_mcart_1(sK0),k1_mcart_1(sK0),k1_mcart_1(sK0),k1_mcart_1(sK0)))
    | ~ spl5_5 ),
    inference(resolution,[],[f201,f141])).

fof(f141,plain,(
    ! [X2] : r2_hidden(X2,k2_enumset1(X2,X2,X2,X2)) ),
    inference(resolution,[],[f60,f62])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_enumset1(X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f40,f57])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f201,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k1_mcart_1(sK0),X0)
        | r2_hidden(sK1,X0) )
    | ~ spl5_5 ),
    inference(resolution,[],[f198,f121])).

% (28530)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
fof(f121,plain,
    ( ! [X3] :
        ( ~ r1_xboole_0(X3,k2_enumset1(sK1,sK1,sK1,sK1))
        | ~ r2_hidden(k1_mcart_1(sK0),X3) )
    | ~ spl5_5 ),
    inference(resolution,[],[f52,f100])).

fof(f100,plain,
    ( r2_hidden(k1_mcart_1(sK0),k2_enumset1(sK1,sK1,sK1,sK1))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f98])).

fof(f256,plain,
    ( ~ spl5_16
    | spl5_1
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f239,f235,f67,f253])).

fof(f67,plain,
    ( spl5_1
  <=> sK1 = k1_mcart_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f235,plain,
    ( spl5_14
  <=> r1_tarski(sK1,k1_mcart_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f239,plain,
    ( sK1 = k1_mcart_1(sK0)
    | ~ r1_tarski(k1_mcart_1(sK0),sK1)
    | ~ spl5_14 ),
    inference(resolution,[],[f237,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f237,plain,
    ( r1_tarski(sK1,k1_mcart_1(sK0))
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f235])).

fof(f238,plain,
    ( spl5_14
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f226,f222,f235])).

fof(f222,plain,
    ( spl5_13
  <=> r2_hidden(sK1,k1_zfmisc_1(k1_mcart_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f226,plain,
    ( r1_tarski(sK1,k1_mcart_1(sK0))
    | ~ spl5_13 ),
    inference(resolution,[],[f224,f65])).

fof(f224,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(k1_mcart_1(sK0)))
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f222])).

fof(f225,plain,
    ( spl5_13
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f220,f98,f222])).

fof(f220,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(k1_mcart_1(sK0)))
    | ~ spl5_5 ),
    inference(resolution,[],[f216,f62])).

fof(f216,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k1_mcart_1(sK0),X1)
        | r2_hidden(sK1,k1_zfmisc_1(X1)) )
    | ~ spl5_5 ),
    inference(resolution,[],[f201,f64])).

fof(f111,plain,
    ( spl5_2
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f108,f76,f71])).

fof(f71,plain,
    ( spl5_2
  <=> r2_hidden(k2_mcart_1(sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f76,plain,
    ( spl5_3
  <=> r2_hidden(sK0,k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f108,plain,
    ( r2_hidden(k2_mcart_1(sK0),sK2)
    | ~ spl5_3 ),
    inference(resolution,[],[f36,f78])).

fof(f78,plain,
    ( r2_hidden(sK0,k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f76])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k2_mcart_1(X0),X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f101,plain,
    ( spl5_5
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f94,f76,f98])).

fof(f94,plain,
    ( r2_hidden(k1_mcart_1(sK0),k2_enumset1(sK1,sK1,sK1,sK1))
    | ~ spl5_3 ),
    inference(resolution,[],[f35,f78])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f79,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f58,f76])).

fof(f58,plain,(
    r2_hidden(sK0,k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) ),
    inference(definition_unfolding,[],[f33,f57])).

fof(f33,plain,(
    r2_hidden(sK0,k2_zfmisc_1(k1_tarski(sK1),sK2)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ( ~ r2_hidden(k2_mcart_1(sK0),sK2)
      | sK1 != k1_mcart_1(sK0) )
    & r2_hidden(sK0,k2_zfmisc_1(k1_tarski(sK1),sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f21])).

fof(f21,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r2_hidden(k2_mcart_1(X0),X2)
          | k1_mcart_1(X0) != X1 )
        & r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) )
   => ( ( ~ r2_hidden(k2_mcart_1(sK0),sK2)
        | sK1 != k1_mcart_1(sK0) )
      & r2_hidden(sK0,k2_zfmisc_1(k1_tarski(sK1),sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(k2_mcart_1(X0),X2)
        | k1_mcart_1(X0) != X1 )
      & r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2))
       => ( r2_hidden(k2_mcart_1(X0),X2)
          & k1_mcart_1(X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & k1_mcart_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_mcart_1)).

fof(f74,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f34,f71,f67])).

fof(f34,plain,
    ( ~ r2_hidden(k2_mcart_1(sK0),sK2)
    | sK1 != k1_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.36  % Computer   : n007.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % WCLimit    : 600
% 0.14/0.36  % DateTime   : Tue Dec  1 15:50:36 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.39  ipcrm: permission denied for id (797114369)
% 0.14/0.39  ipcrm: permission denied for id (797212674)
% 0.14/0.40  ipcrm: permission denied for id (797310981)
% 0.14/0.40  ipcrm: permission denied for id (797409288)
% 0.14/0.40  ipcrm: permission denied for id (797474826)
% 0.14/0.41  ipcrm: permission denied for id (797540364)
% 0.14/0.41  ipcrm: permission denied for id (797573133)
% 0.14/0.41  ipcrm: permission denied for id (797605902)
% 0.14/0.41  ipcrm: permission denied for id (797704209)
% 0.14/0.42  ipcrm: permission denied for id (797736978)
% 0.14/0.42  ipcrm: permission denied for id (797933592)
% 0.14/0.43  ipcrm: permission denied for id (798064667)
% 0.24/0.43  ipcrm: permission denied for id (798162974)
% 0.24/0.44  ipcrm: permission denied for id (798195743)
% 0.24/0.44  ipcrm: permission denied for id (798294050)
% 0.24/0.44  ipcrm: permission denied for id (798359588)
% 0.24/0.44  ipcrm: permission denied for id (798392357)
% 0.24/0.45  ipcrm: permission denied for id (798523433)
% 0.24/0.45  ipcrm: permission denied for id (798621740)
% 0.24/0.46  ipcrm: permission denied for id (798654509)
% 0.24/0.46  ipcrm: permission denied for id (798720047)
% 0.24/0.46  ipcrm: permission denied for id (798785585)
% 0.24/0.46  ipcrm: permission denied for id (798818354)
% 0.24/0.46  ipcrm: permission denied for id (798851123)
% 0.24/0.47  ipcrm: permission denied for id (798883892)
% 0.24/0.47  ipcrm: permission denied for id (798949430)
% 0.24/0.47  ipcrm: permission denied for id (799014968)
% 0.24/0.47  ipcrm: permission denied for id (799080506)
% 0.24/0.47  ipcrm: permission denied for id (799113275)
% 0.24/0.47  ipcrm: permission denied for id (799146044)
% 0.24/0.47  ipcrm: permission denied for id (799244351)
% 0.24/0.48  ipcrm: permission denied for id (799309889)
% 0.24/0.48  ipcrm: permission denied for id (799342658)
% 0.24/0.48  ipcrm: permission denied for id (799375427)
% 0.24/0.48  ipcrm: permission denied for id (799408196)
% 0.24/0.48  ipcrm: permission denied for id (799670348)
% 0.24/0.49  ipcrm: permission denied for id (799703117)
% 0.24/0.49  ipcrm: permission denied for id (799768655)
% 0.24/0.49  ipcrm: permission denied for id (799801424)
% 0.24/0.49  ipcrm: permission denied for id (799834193)
% 0.24/0.49  ipcrm: permission denied for id (799998038)
% 0.24/0.49  ipcrm: permission denied for id (800063576)
% 0.24/0.50  ipcrm: permission denied for id (800227421)
% 0.24/0.50  ipcrm: permission denied for id (800260190)
% 0.24/0.50  ipcrm: permission denied for id (800292959)
% 0.24/0.50  ipcrm: permission denied for id (800358497)
% 0.24/0.50  ipcrm: permission denied for id (800456804)
% 0.24/0.51  ipcrm: permission denied for id (800555111)
% 0.24/0.51  ipcrm: permission denied for id (800620649)
% 0.24/0.51  ipcrm: permission denied for id (800751725)
% 0.24/0.51  ipcrm: permission denied for id (800784494)
% 0.24/0.51  ipcrm: permission denied for id (800850032)
% 0.24/0.52  ipcrm: permission denied for id (800882801)
% 0.24/0.52  ipcrm: permission denied for id (800915570)
% 0.24/0.52  ipcrm: permission denied for id (801046645)
% 0.24/0.52  ipcrm: permission denied for id (801079414)
% 0.24/0.52  ipcrm: permission denied for id (801144952)
% 0.24/0.53  ipcrm: permission denied for id (801308797)
% 0.24/0.53  ipcrm: permission denied for id (801374335)
% 1.14/0.67  % (28551)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.14/0.68  % (28543)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.14/0.68  % (28535)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.14/0.68  % (28533)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.14/0.69  % (28528)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.14/0.69  % (28551)Refutation found. Thanks to Tanya!
% 1.14/0.69  % SZS status Theorem for theBenchmark
% 1.14/0.69  % (28534)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.14/0.69  % SZS output start Proof for theBenchmark
% 1.14/0.69  fof(f329,plain,(
% 1.14/0.69    $false),
% 1.14/0.69    inference(avatar_sat_refutation,[],[f74,f79,f101,f111,f225,f238,f256,f261,f328])).
% 1.14/0.70  fof(f328,plain,(
% 1.14/0.70    spl5_16 | ~spl5_17),
% 1.14/0.70    inference(avatar_contradiction_clause,[],[f322])).
% 1.14/0.70  fof(f322,plain,(
% 1.14/0.70    $false | (spl5_16 | ~spl5_17)),
% 1.14/0.70    inference(unit_resulting_resolution,[],[f62,f255,f321])).
% 1.14/0.70  fof(f321,plain,(
% 1.14/0.70    ( ! [X0] : (r1_tarski(k1_mcart_1(sK0),X0) | ~r1_tarski(sK1,X0)) ) | ~spl5_17),
% 1.14/0.70    inference(resolution,[],[f316,f64])).
% 1.14/0.70  fof(f64,plain,(
% 1.14/0.70    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 1.14/0.70    inference(equality_resolution,[],[f47])).
% 1.14/0.70  fof(f47,plain,(
% 1.14/0.70    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 1.14/0.70    inference(cnf_transformation,[],[f30])).
% 1.14/0.70  fof(f30,plain,(
% 1.14/0.70    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.14/0.70    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f28,f29])).
% 1.14/0.70  fof(f29,plain,(
% 1.14/0.70    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 1.14/0.70    introduced(choice_axiom,[])).
% 1.14/0.70  fof(f28,plain,(
% 1.14/0.70    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.14/0.70    inference(rectify,[],[f27])).
% 1.14/0.70  fof(f27,plain,(
% 1.14/0.70    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.14/0.70    inference(nnf_transformation,[],[f7])).
% 1.14/0.70  fof(f7,axiom,(
% 1.14/0.70    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.14/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.14/0.70  fof(f316,plain,(
% 1.14/0.70    ( ! [X6] : (~r2_hidden(sK1,k1_zfmisc_1(X6)) | r1_tarski(k1_mcart_1(sK0),X6)) ) | ~spl5_17),
% 1.14/0.70    inference(resolution,[],[f309,f65])).
% 1.14/0.70  fof(f65,plain,(
% 1.14/0.70    ( ! [X0,X3] : (~r2_hidden(X3,k1_zfmisc_1(X0)) | r1_tarski(X3,X0)) )),
% 1.14/0.70    inference(equality_resolution,[],[f46])).
% 1.14/0.70  % (28541)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.14/0.70  fof(f46,plain,(
% 1.14/0.70    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.14/0.70    inference(cnf_transformation,[],[f30])).
% 1.14/0.70  fof(f309,plain,(
% 1.14/0.70    ( ! [X1] : (r2_hidden(k1_mcart_1(sK0),X1) | ~r2_hidden(sK1,X1)) ) | ~spl5_17),
% 1.14/0.70    inference(resolution,[],[f267,f198])).
% 1.14/0.70  fof(f198,plain,(
% 1.14/0.70    ( ! [X0,X1] : (r1_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) | r2_hidden(X1,X0)) )),
% 1.14/0.70    inference(resolution,[],[f196,f61])).
% 1.14/0.70  fof(f61,plain,(
% 1.14/0.70    ( ! [X0,X1] : (r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 1.14/0.70    inference(definition_unfolding,[],[f42,f57])).
% 1.14/0.70  fof(f57,plain,(
% 1.14/0.70    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.14/0.70    inference(definition_unfolding,[],[f43,f56])).
% 1.14/0.70  fof(f56,plain,(
% 1.14/0.70    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.14/0.70    inference(definition_unfolding,[],[f53,f55])).
% 1.14/0.70  fof(f55,plain,(
% 1.14/0.70    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.14/0.70    inference(cnf_transformation,[],[f5])).
% 1.14/0.70  fof(f5,axiom,(
% 1.14/0.70    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.14/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.14/0.70  fof(f53,plain,(
% 1.14/0.70    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.14/0.70    inference(cnf_transformation,[],[f4])).
% 1.14/0.70  fof(f4,axiom,(
% 1.14/0.70    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.14/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.14/0.70  fof(f43,plain,(
% 1.14/0.70    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.14/0.70    inference(cnf_transformation,[],[f3])).
% 1.14/0.70  fof(f3,axiom,(
% 1.14/0.70    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.14/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.14/0.70  fof(f42,plain,(
% 1.14/0.70    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 1.14/0.70    inference(cnf_transformation,[],[f18])).
% 1.14/0.70  fof(f18,plain,(
% 1.14/0.70    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 1.14/0.70    inference(ennf_transformation,[],[f9])).
% 1.14/0.70  fof(f9,axiom,(
% 1.14/0.70    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 1.14/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 1.14/0.70  fof(f196,plain,(
% 1.14/0.70    ( ! [X2,X3] : (~r1_xboole_0(X2,X3) | r1_xboole_0(X3,X2)) )),
% 1.14/0.70    inference(duplicate_literal_removal,[],[f191])).
% 1.14/0.70  fof(f191,plain,(
% 1.14/0.70    ( ! [X2,X3] : (~r1_xboole_0(X2,X3) | r1_xboole_0(X3,X2) | r1_xboole_0(X3,X2)) )),
% 1.14/0.70    inference(resolution,[],[f124,f51])).
% 1.14/0.70  fof(f51,plain,(
% 1.14/0.70    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 1.14/0.70    inference(cnf_transformation,[],[f32])).
% 1.14/0.70  fof(f32,plain,(
% 1.14/0.70    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 1.14/0.70    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f31])).
% 1.14/0.70  fof(f31,plain,(
% 1.14/0.70    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 1.14/0.70    introduced(choice_axiom,[])).
% 1.14/0.70  fof(f19,plain,(
% 1.14/0.70    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.14/0.70    inference(ennf_transformation,[],[f15])).
% 1.14/0.70  fof(f15,plain,(
% 1.14/0.70    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.14/0.70    inference(rectify,[],[f1])).
% 1.14/0.70  fof(f1,axiom,(
% 1.14/0.70    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.14/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.14/0.70  fof(f124,plain,(
% 1.14/0.70    ( ! [X6,X8,X7] : (~r2_hidden(sK4(X7,X8),X6) | ~r1_xboole_0(X6,X7) | r1_xboole_0(X7,X8)) )),
% 1.14/0.70    inference(resolution,[],[f52,f50])).
% 1.14/0.70  fof(f50,plain,(
% 1.14/0.70    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 1.14/0.70    inference(cnf_transformation,[],[f32])).
% 1.14/0.70  fof(f52,plain,(
% 1.14/0.70    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X0)) )),
% 1.14/0.70    inference(cnf_transformation,[],[f32])).
% 1.14/0.70  fof(f267,plain,(
% 1.14/0.70    ( ! [X0] : (~r1_xboole_0(X0,k2_enumset1(k1_mcart_1(sK0),k1_mcart_1(sK0),k1_mcart_1(sK0),k1_mcart_1(sK0))) | ~r2_hidden(sK1,X0)) ) | ~spl5_17),
% 1.14/0.70    inference(resolution,[],[f260,f52])).
% 1.14/0.70  fof(f260,plain,(
% 1.14/0.70    r2_hidden(sK1,k2_enumset1(k1_mcart_1(sK0),k1_mcart_1(sK0),k1_mcart_1(sK0),k1_mcart_1(sK0))) | ~spl5_17),
% 1.14/0.70    inference(avatar_component_clause,[],[f258])).
% 1.14/0.70  fof(f258,plain,(
% 1.14/0.70    spl5_17 <=> r2_hidden(sK1,k2_enumset1(k1_mcart_1(sK0),k1_mcart_1(sK0),k1_mcart_1(sK0),k1_mcart_1(sK0)))),
% 1.14/0.70    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 1.14/0.70  fof(f255,plain,(
% 1.14/0.70    ~r1_tarski(k1_mcart_1(sK0),sK1) | spl5_16),
% 1.14/0.70    inference(avatar_component_clause,[],[f253])).
% 1.14/0.70  fof(f253,plain,(
% 1.14/0.70    spl5_16 <=> r1_tarski(k1_mcart_1(sK0),sK1)),
% 1.14/0.70    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 1.14/0.70  fof(f62,plain,(
% 1.14/0.70    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.14/0.70    inference(equality_resolution,[],[f38])).
% 1.14/0.70  fof(f38,plain,(
% 1.14/0.70    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.14/0.70    inference(cnf_transformation,[],[f24])).
% 1.14/0.70  fof(f24,plain,(
% 1.14/0.70    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.14/0.70    inference(flattening,[],[f23])).
% 1.14/0.70  fof(f23,plain,(
% 1.14/0.70    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.14/0.70    inference(nnf_transformation,[],[f2])).
% 1.14/0.70  fof(f2,axiom,(
% 1.14/0.70    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.14/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.14/0.70  fof(f261,plain,(
% 1.14/0.70    spl5_17 | ~spl5_5),
% 1.14/0.70    inference(avatar_split_clause,[],[f217,f98,f258])).
% 1.14/0.70  fof(f98,plain,(
% 1.14/0.70    spl5_5 <=> r2_hidden(k1_mcart_1(sK0),k2_enumset1(sK1,sK1,sK1,sK1))),
% 1.14/0.70    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 1.14/0.70  fof(f217,plain,(
% 1.14/0.70    r2_hidden(sK1,k2_enumset1(k1_mcart_1(sK0),k1_mcart_1(sK0),k1_mcart_1(sK0),k1_mcart_1(sK0))) | ~spl5_5),
% 1.14/0.70    inference(resolution,[],[f201,f141])).
% 1.14/0.70  fof(f141,plain,(
% 1.14/0.70    ( ! [X2] : (r2_hidden(X2,k2_enumset1(X2,X2,X2,X2))) )),
% 1.14/0.70    inference(resolution,[],[f60,f62])).
% 1.14/0.70  fof(f60,plain,(
% 1.14/0.70    ( ! [X0,X1] : (~r1_tarski(k2_enumset1(X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 1.14/0.70    inference(definition_unfolding,[],[f40,f57])).
% 1.14/0.70  fof(f40,plain,(
% 1.14/0.70    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)) )),
% 1.14/0.70    inference(cnf_transformation,[],[f25])).
% 1.14/0.70  fof(f25,plain,(
% 1.14/0.70    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 1.14/0.70    inference(nnf_transformation,[],[f8])).
% 1.14/0.70  fof(f8,axiom,(
% 1.14/0.70    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.14/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 1.14/0.70  fof(f201,plain,(
% 1.14/0.70    ( ! [X0] : (~r2_hidden(k1_mcart_1(sK0),X0) | r2_hidden(sK1,X0)) ) | ~spl5_5),
% 1.14/0.70    inference(resolution,[],[f198,f121])).
% 1.14/0.70  % (28530)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.14/0.70  fof(f121,plain,(
% 1.14/0.70    ( ! [X3] : (~r1_xboole_0(X3,k2_enumset1(sK1,sK1,sK1,sK1)) | ~r2_hidden(k1_mcart_1(sK0),X3)) ) | ~spl5_5),
% 1.14/0.70    inference(resolution,[],[f52,f100])).
% 1.14/0.70  fof(f100,plain,(
% 1.14/0.70    r2_hidden(k1_mcart_1(sK0),k2_enumset1(sK1,sK1,sK1,sK1)) | ~spl5_5),
% 1.14/0.70    inference(avatar_component_clause,[],[f98])).
% 1.14/0.70  fof(f256,plain,(
% 1.14/0.70    ~spl5_16 | spl5_1 | ~spl5_14),
% 1.14/0.70    inference(avatar_split_clause,[],[f239,f235,f67,f253])).
% 1.14/0.70  fof(f67,plain,(
% 1.14/0.70    spl5_1 <=> sK1 = k1_mcart_1(sK0)),
% 1.14/0.70    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.14/0.70  fof(f235,plain,(
% 1.14/0.70    spl5_14 <=> r1_tarski(sK1,k1_mcart_1(sK0))),
% 1.14/0.70    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 1.14/0.70  fof(f239,plain,(
% 1.14/0.70    sK1 = k1_mcart_1(sK0) | ~r1_tarski(k1_mcart_1(sK0),sK1) | ~spl5_14),
% 1.14/0.70    inference(resolution,[],[f237,f39])).
% 1.14/0.70  fof(f39,plain,(
% 1.14/0.70    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.14/0.70    inference(cnf_transformation,[],[f24])).
% 1.14/0.70  fof(f237,plain,(
% 1.14/0.70    r1_tarski(sK1,k1_mcart_1(sK0)) | ~spl5_14),
% 1.14/0.70    inference(avatar_component_clause,[],[f235])).
% 1.14/0.70  fof(f238,plain,(
% 1.14/0.70    spl5_14 | ~spl5_13),
% 1.14/0.70    inference(avatar_split_clause,[],[f226,f222,f235])).
% 1.14/0.70  fof(f222,plain,(
% 1.14/0.70    spl5_13 <=> r2_hidden(sK1,k1_zfmisc_1(k1_mcart_1(sK0)))),
% 1.14/0.70    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 1.14/0.70  fof(f226,plain,(
% 1.14/0.70    r1_tarski(sK1,k1_mcart_1(sK0)) | ~spl5_13),
% 1.14/0.70    inference(resolution,[],[f224,f65])).
% 1.14/0.70  fof(f224,plain,(
% 1.14/0.70    r2_hidden(sK1,k1_zfmisc_1(k1_mcart_1(sK0))) | ~spl5_13),
% 1.14/0.70    inference(avatar_component_clause,[],[f222])).
% 1.14/0.70  fof(f225,plain,(
% 1.14/0.70    spl5_13 | ~spl5_5),
% 1.14/0.70    inference(avatar_split_clause,[],[f220,f98,f222])).
% 1.14/0.70  fof(f220,plain,(
% 1.14/0.70    r2_hidden(sK1,k1_zfmisc_1(k1_mcart_1(sK0))) | ~spl5_5),
% 1.14/0.70    inference(resolution,[],[f216,f62])).
% 1.14/0.70  fof(f216,plain,(
% 1.14/0.70    ( ! [X1] : (~r1_tarski(k1_mcart_1(sK0),X1) | r2_hidden(sK1,k1_zfmisc_1(X1))) ) | ~spl5_5),
% 1.14/0.70    inference(resolution,[],[f201,f64])).
% 1.14/0.70  fof(f111,plain,(
% 1.14/0.70    spl5_2 | ~spl5_3),
% 1.14/0.70    inference(avatar_split_clause,[],[f108,f76,f71])).
% 1.14/0.70  fof(f71,plain,(
% 1.14/0.70    spl5_2 <=> r2_hidden(k2_mcart_1(sK0),sK2)),
% 1.14/0.70    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.14/0.70  fof(f76,plain,(
% 1.14/0.70    spl5_3 <=> r2_hidden(sK0,k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))),
% 1.14/0.70    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.14/0.70  fof(f108,plain,(
% 1.14/0.70    r2_hidden(k2_mcart_1(sK0),sK2) | ~spl5_3),
% 1.14/0.70    inference(resolution,[],[f36,f78])).
% 1.14/0.70  fof(f78,plain,(
% 1.14/0.70    r2_hidden(sK0,k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) | ~spl5_3),
% 1.14/0.70    inference(avatar_component_clause,[],[f76])).
% 1.14/0.70  fof(f36,plain,(
% 1.14/0.70    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k2_mcart_1(X0),X2)) )),
% 1.14/0.70    inference(cnf_transformation,[],[f17])).
% 1.14/0.70  fof(f17,plain,(
% 1.14/0.70    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 1.14/0.70    inference(ennf_transformation,[],[f12])).
% 1.14/0.70  fof(f12,axiom,(
% 1.14/0.70    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 1.14/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).
% 1.14/0.70  fof(f101,plain,(
% 1.14/0.70    spl5_5 | ~spl5_3),
% 1.14/0.70    inference(avatar_split_clause,[],[f94,f76,f98])).
% 1.14/0.70  fof(f94,plain,(
% 1.14/0.70    r2_hidden(k1_mcart_1(sK0),k2_enumset1(sK1,sK1,sK1,sK1)) | ~spl5_3),
% 1.14/0.70    inference(resolution,[],[f35,f78])).
% 1.14/0.70  fof(f35,plain,(
% 1.14/0.70    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k1_mcart_1(X0),X1)) )),
% 1.14/0.70    inference(cnf_transformation,[],[f17])).
% 1.14/0.70  fof(f79,plain,(
% 1.14/0.70    spl5_3),
% 1.14/0.70    inference(avatar_split_clause,[],[f58,f76])).
% 1.14/0.70  fof(f58,plain,(
% 1.14/0.70    r2_hidden(sK0,k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))),
% 1.14/0.70    inference(definition_unfolding,[],[f33,f57])).
% 1.14/0.70  fof(f33,plain,(
% 1.14/0.70    r2_hidden(sK0,k2_zfmisc_1(k1_tarski(sK1),sK2))),
% 1.14/0.70    inference(cnf_transformation,[],[f22])).
% 1.14/0.70  fof(f22,plain,(
% 1.14/0.70    (~r2_hidden(k2_mcart_1(sK0),sK2) | sK1 != k1_mcart_1(sK0)) & r2_hidden(sK0,k2_zfmisc_1(k1_tarski(sK1),sK2))),
% 1.14/0.70    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f21])).
% 1.14/0.70  fof(f21,plain,(
% 1.14/0.70    ? [X0,X1,X2] : ((~r2_hidden(k2_mcart_1(X0),X2) | k1_mcart_1(X0) != X1) & r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2))) => ((~r2_hidden(k2_mcart_1(sK0),sK2) | sK1 != k1_mcart_1(sK0)) & r2_hidden(sK0,k2_zfmisc_1(k1_tarski(sK1),sK2)))),
% 1.14/0.70    introduced(choice_axiom,[])).
% 1.14/0.70  fof(f16,plain,(
% 1.14/0.70    ? [X0,X1,X2] : ((~r2_hidden(k2_mcart_1(X0),X2) | k1_mcart_1(X0) != X1) & r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)))),
% 1.14/0.70    inference(ennf_transformation,[],[f14])).
% 1.14/0.70  fof(f14,negated_conjecture,(
% 1.14/0.70    ~! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) => (r2_hidden(k2_mcart_1(X0),X2) & k1_mcart_1(X0) = X1))),
% 1.14/0.70    inference(negated_conjecture,[],[f13])).
% 1.14/0.70  fof(f13,conjecture,(
% 1.14/0.70    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) => (r2_hidden(k2_mcart_1(X0),X2) & k1_mcart_1(X0) = X1))),
% 1.14/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_mcart_1)).
% 1.14/0.70  fof(f74,plain,(
% 1.14/0.70    ~spl5_1 | ~spl5_2),
% 1.14/0.70    inference(avatar_split_clause,[],[f34,f71,f67])).
% 1.14/0.70  fof(f34,plain,(
% 1.14/0.70    ~r2_hidden(k2_mcart_1(sK0),sK2) | sK1 != k1_mcart_1(sK0)),
% 1.14/0.70    inference(cnf_transformation,[],[f22])).
% 1.14/0.70  % SZS output end Proof for theBenchmark
% 1.14/0.70  % (28551)------------------------------
% 1.14/0.70  % (28551)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.14/0.70  % (28551)Termination reason: Refutation
% 1.14/0.70  
% 1.14/0.70  % (28551)Memory used [KB]: 11001
% 1.14/0.70  % (28551)Time elapsed: 0.079 s
% 1.14/0.70  % (28551)------------------------------
% 1.14/0.70  % (28551)------------------------------
% 1.14/0.70  % (28549)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.14/0.70  % (28542)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.14/0.70  % (28391)Success in time 0.316 s
%------------------------------------------------------------------------------
