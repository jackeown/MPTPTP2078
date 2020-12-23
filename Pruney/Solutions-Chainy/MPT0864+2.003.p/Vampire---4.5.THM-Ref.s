%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:31 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 233 expanded)
%              Number of leaves         :   16 (  71 expanded)
%              Depth                    :   15
%              Number of atoms          :  225 ( 721 expanded)
%              Number of equality atoms :  124 ( 450 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f250,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f100,f175,f249])).

fof(f249,plain,(
    ~ spl8_1 ),
    inference(avatar_contradiction_clause,[],[f248])).

fof(f248,plain,
    ( $false
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f247,f165])).

fof(f165,plain,(
    ! [X0] : k1_xboole_0 != k2_enumset1(X0,X0,X0,X0) ),
    inference(subsumption_resolution,[],[f164,f86])).

fof(f86,plain,(
    ! [X3] : r2_hidden(X3,k2_enumset1(X3,X3,X3,X3)) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k2_enumset1(X3,X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f55,f74])).

fof(f74,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f43,f73])).

fof(f73,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f48,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f48,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f43,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f55,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK6(X0,X1) != X0
            | ~ r2_hidden(sK6(X0,X1),X1) )
          & ( sK6(X0,X1) = X0
            | r2_hidden(sK6(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f30,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK6(X0,X1) != X0
          | ~ r2_hidden(sK6(X0,X1),X1) )
        & ( sK6(X0,X1) = X0
          | r2_hidden(sK6(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
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
    inference(rectify,[],[f29])).

% (30946)Refutation not found, incomplete strategy% (30946)------------------------------
% (30946)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (30946)Termination reason: Refutation not found, incomplete strategy

% (30946)Memory used [KB]: 6268
% (30946)Time elapsed: 0.128 s
% (30946)------------------------------
% (30946)------------------------------
% (30939)Refutation not found, incomplete strategy% (30939)------------------------------
% (30939)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (30939)Termination reason: Refutation not found, incomplete strategy

% (30939)Memory used [KB]: 1791
% (30939)Time elapsed: 0.130 s
% (30939)------------------------------
% (30939)------------------------------
fof(f29,plain,(
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
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f164,plain,(
    ! [X0] :
      ( k1_xboole_0 != k2_enumset1(X0,X0,X0,X0)
      | ~ r2_hidden(X0,k2_enumset1(X0,X0,X0,X0)) ) ),
    inference(superposition,[],[f80,f111])).

fof(f111,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(resolution,[],[f59,f83])).

fof(f83,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
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

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f80,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) != X0
      | ~ r2_hidden(X1,X0) ) ),
    inference(definition_unfolding,[],[f60,f74])).

% (30941)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f9])).

% (30937)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
fof(f9,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f247,plain,
    ( k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1)
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f246,f86])).

fof(f246,plain,
    ( ~ r2_hidden(sK1,k2_enumset1(sK1,sK1,sK1,sK1))
    | k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1)
    | ~ spl8_1 ),
    inference(duplicate_literal_removal,[],[f244])).

fof(f244,plain,
    ( ~ r2_hidden(sK1,k2_enumset1(sK1,sK1,sK1,sK1))
    | k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1)
    | k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1)
    | ~ spl8_1 ),
    inference(resolution,[],[f228,f45])).

fof(f45,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f26])).

% (30944)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
fof(f26,plain,(
    ! [X0] :
      ( ( ! [X2,X3] :
            ( k4_tarski(X2,X3) != sK5(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK5(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f16,f25])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] :
            ( k4_tarski(X2,X3) != sK5(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK5(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3] :
                  ~ ( k4_tarski(X2,X3) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_mcart_1)).

fof(f228,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK5(X0),k2_enumset1(sK1,sK1,sK1,sK1))
        | ~ r2_hidden(sK1,X0)
        | k1_xboole_0 = X0 )
    | ~ spl8_1 ),
    inference(extensionality_resolution,[],[f87,f213])).

fof(f213,plain,
    ( ! [X1] :
        ( sK1 != sK5(X1)
        | ~ r2_hidden(sK1,X1)
        | k1_xboole_0 = X1 )
    | ~ spl8_1 ),
    inference(superposition,[],[f46,f210])).

fof(f210,plain,
    ( sK1 = k4_tarski(sK1,sK3)
    | ~ spl8_1 ),
    inference(forward_demodulation,[],[f41,f176])).

fof(f176,plain,
    ( sK1 = sK2
    | ~ spl8_1 ),
    inference(backward_demodulation,[],[f105,f95])).

% (30923)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
fof(f95,plain,
    ( sK1 = k1_mcart_1(sK1)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl8_1
  <=> sK1 = k1_mcart_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f105,plain,(
    k1_mcart_1(sK1) = sK2 ),
    inference(superposition,[],[f49,f41])).

fof(f49,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f41,plain,(
    sK1 = k4_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ( sK1 = k2_mcart_1(sK1)
      | sK1 = k1_mcart_1(sK1) )
    & sK1 = k4_tarski(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f14,f21,f20])).

fof(f20,plain,
    ( ? [X0] :
        ( ( k2_mcart_1(X0) = X0
          | k1_mcart_1(X0) = X0 )
        & ? [X1,X2] : k4_tarski(X1,X2) = X0 )
   => ( ( sK1 = k2_mcart_1(sK1)
        | sK1 = k1_mcart_1(sK1) )
      & ? [X2,X1] : k4_tarski(X1,X2) = sK1 ) ),
    introduced(choice_axiom,[])).

% (30932)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% (30937)Refutation not found, incomplete strategy% (30937)------------------------------
% (30937)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (30937)Termination reason: Refutation not found, incomplete strategy

% (30937)Memory used [KB]: 10618
% (30937)Time elapsed: 0.129 s
% (30937)------------------------------
% (30937)------------------------------
% (30943)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
fof(f21,plain,
    ( ? [X2,X1] : k4_tarski(X1,X2) = sK1
   => sK1 = k4_tarski(sK2,sK3) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] :
      ( ( k2_mcart_1(X0) = X0
        | k1_mcart_1(X0) = X0 )
      & ? [X1,X2] : k4_tarski(X1,X2) = X0 ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ? [X1,X2] : k4_tarski(X1,X2) = X0
       => ( k2_mcart_1(X0) != X0
          & k1_mcart_1(X0) != X0 ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).

fof(f46,plain,(
    ! [X2,X0,X3] :
      ( k4_tarski(X2,X3) != sK5(X0)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f87,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k2_enumset1(X0,X0,X0,X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f54,f74])).

fof(f54,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f175,plain,(
    ~ spl8_2 ),
    inference(avatar_contradiction_clause,[],[f174])).

fof(f174,plain,
    ( $false
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f173,f165])).

fof(f173,plain,
    ( k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1)
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f172,f86])).

fof(f172,plain,
    ( ~ r2_hidden(sK1,k2_enumset1(sK1,sK1,sK1,sK1))
    | k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1)
    | ~ spl8_2 ),
    inference(duplicate_literal_removal,[],[f170])).

fof(f170,plain,
    ( ~ r2_hidden(sK1,k2_enumset1(sK1,sK1,sK1,sK1))
    | k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1)
    | k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1)
    | ~ spl8_2 ),
    inference(resolution,[],[f142,f45])).

fof(f142,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK5(X0),k2_enumset1(sK1,sK1,sK1,sK1))
        | ~ r2_hidden(sK1,X0)
        | k1_xboole_0 = X0 )
    | ~ spl8_2 ),
    inference(extensionality_resolution,[],[f87,f137])).

fof(f137,plain,
    ( ! [X0] :
        ( sK1 != sK5(X0)
        | ~ r2_hidden(sK1,X0)
        | k1_xboole_0 = X0 )
    | ~ spl8_2 ),
    inference(superposition,[],[f47,f108])).

fof(f108,plain,
    ( sK1 = k4_tarski(sK2,sK1)
    | ~ spl8_2 ),
    inference(backward_demodulation,[],[f41,f107])).

fof(f107,plain,
    ( sK1 = sK3
    | ~ spl8_2 ),
    inference(forward_demodulation,[],[f106,f99])).

fof(f99,plain,
    ( sK1 = k2_mcart_1(sK1)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl8_2
  <=> sK1 = k2_mcart_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f106,plain,(
    k2_mcart_1(sK1) = sK3 ),
    inference(superposition,[],[f50,f41])).

fof(f50,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f10])).

fof(f47,plain,(
    ! [X2,X0,X3] :
      ( k4_tarski(X2,X3) != sK5(X0)
      | ~ r2_hidden(X3,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f100,plain,
    ( spl8_1
    | spl8_2 ),
    inference(avatar_split_clause,[],[f42,f97,f93])).

fof(f42,plain,
    ( sK1 = k2_mcart_1(sK1)
    | sK1 = k1_mcart_1(sK1) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:31:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (30934)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.51  % (30926)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.51  % (30927)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (30922)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.52  % (30950)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.52  % (30950)Refutation not found, incomplete strategy% (30950)------------------------------
% 0.21/0.52  % (30950)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (30949)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.52  % (30950)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (30950)Memory used [KB]: 1663
% 0.21/0.52  % (30950)Time elapsed: 0.003 s
% 0.21/0.52  % (30950)------------------------------
% 0.21/0.52  % (30950)------------------------------
% 0.21/0.52  % (30936)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.52  % (30927)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % (30940)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.52  % (30924)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.52  % (30925)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.53  % (30921)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.53  % (30948)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.53  % (30945)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.53  % (30946)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.53  % (30948)Refutation not found, incomplete strategy% (30948)------------------------------
% 0.21/0.53  % (30948)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (30948)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (30948)Memory used [KB]: 6268
% 0.21/0.53  % (30948)Time elapsed: 0.132 s
% 0.21/0.53  % (30948)------------------------------
% 0.21/0.53  % (30948)------------------------------
% 0.21/0.53  % (30939)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f250,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(avatar_sat_refutation,[],[f100,f175,f249])).
% 0.21/0.53  fof(f249,plain,(
% 0.21/0.53    ~spl8_1),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f248])).
% 0.21/0.53  fof(f248,plain,(
% 0.21/0.53    $false | ~spl8_1),
% 0.21/0.53    inference(subsumption_resolution,[],[f247,f165])).
% 0.21/0.53  fof(f165,plain,(
% 0.21/0.53    ( ! [X0] : (k1_xboole_0 != k2_enumset1(X0,X0,X0,X0)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f164,f86])).
% 0.21/0.53  fof(f86,plain,(
% 0.21/0.53    ( ! [X3] : (r2_hidden(X3,k2_enumset1(X3,X3,X3,X3))) )),
% 0.21/0.53    inference(equality_resolution,[],[f85])).
% 0.21/0.53  fof(f85,plain,(
% 0.21/0.53    ( ! [X3,X1] : (r2_hidden(X3,X1) | k2_enumset1(X3,X3,X3,X3) != X1) )),
% 0.21/0.53    inference(equality_resolution,[],[f77])).
% 0.21/0.53  fof(f77,plain,(
% 0.21/0.53    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 0.21/0.53    inference(definition_unfolding,[],[f55,f74])).
% 0.21/0.53  fof(f74,plain,(
% 0.21/0.53    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f43,f73])).
% 0.21/0.53  fof(f73,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f48,f62])).
% 0.21/0.53  fof(f62,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.53  fof(f48,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,axiom,(
% 0.21/0.53    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.53  fof(f43,plain,(
% 0.21/0.53    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.53  fof(f55,plain,(
% 0.21/0.53    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 0.21/0.53    inference(cnf_transformation,[],[f32])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK6(X0,X1) != X0 | ~r2_hidden(sK6(X0,X1),X1)) & (sK6(X0,X1) = X0 | r2_hidden(sK6(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f30,f31])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK6(X0,X1) != X0 | ~r2_hidden(sK6(X0,X1),X1)) & (sK6(X0,X1) = X0 | r2_hidden(sK6(X0,X1),X1))))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.21/0.53    inference(rectify,[],[f29])).
% 0.21/0.53  % (30946)Refutation not found, incomplete strategy% (30946)------------------------------
% 0.21/0.53  % (30946)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (30946)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (30946)Memory used [KB]: 6268
% 0.21/0.53  % (30946)Time elapsed: 0.128 s
% 0.21/0.53  % (30946)------------------------------
% 0.21/0.53  % (30946)------------------------------
% 0.21/0.53  % (30939)Refutation not found, incomplete strategy% (30939)------------------------------
% 0.21/0.53  % (30939)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (30939)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (30939)Memory used [KB]: 1791
% 0.21/0.53  % (30939)Time elapsed: 0.130 s
% 0.21/0.53  % (30939)------------------------------
% 0.21/0.53  % (30939)------------------------------
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 0.21/0.53    inference(nnf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 0.21/0.53  fof(f164,plain,(
% 0.21/0.53    ( ! [X0] : (k1_xboole_0 != k2_enumset1(X0,X0,X0,X0) | ~r2_hidden(X0,k2_enumset1(X0,X0,X0,X0))) )),
% 0.21/0.53    inference(superposition,[],[f80,f111])).
% 0.21/0.53  fof(f111,plain,(
% 0.21/0.53    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.21/0.53    inference(resolution,[],[f59,f83])).
% 0.21/0.53  fof(f83,plain,(
% 0.21/0.53    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.53    inference(equality_resolution,[],[f52])).
% 0.21/0.53  fof(f52,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.53    inference(cnf_transformation,[],[f28])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.53    inference(flattening,[],[f27])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.53    inference(nnf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.53  fof(f59,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f33])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 0.21/0.53    inference(nnf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.21/0.53  fof(f80,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) != X0 | ~r2_hidden(X1,X0)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f60,f74])).
% 0.21/0.53  % (30941)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.53  fof(f60,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f34])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 0.21/0.53    inference(nnf_transformation,[],[f9])).
% 0.21/0.53  % (30937)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.53  fof(f9,axiom,(
% 0.21/0.53    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 0.21/0.53  fof(f247,plain,(
% 0.21/0.53    k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1) | ~spl8_1),
% 0.21/0.53    inference(subsumption_resolution,[],[f246,f86])).
% 0.21/0.53  fof(f246,plain,(
% 0.21/0.53    ~r2_hidden(sK1,k2_enumset1(sK1,sK1,sK1,sK1)) | k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1) | ~spl8_1),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f244])).
% 0.21/0.53  fof(f244,plain,(
% 0.21/0.53    ~r2_hidden(sK1,k2_enumset1(sK1,sK1,sK1,sK1)) | k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1) | k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1) | ~spl8_1),
% 0.21/0.53    inference(resolution,[],[f228,f45])).
% 0.21/0.53  fof(f45,plain,(
% 0.21/0.53    ( ! [X0] : (r2_hidden(sK5(X0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f26])).
% 0.21/0.53  % (30944)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ! [X0] : ((! [X2,X3] : (k4_tarski(X2,X3) != sK5(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK5(X0),X0)) | k1_xboole_0 = X0)),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f16,f25])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X3,X2] : (k4_tarski(X2,X3) != sK5(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK5(X0),X0)))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.21/0.53    inference(ennf_transformation,[],[f11])).
% 0.21/0.53  fof(f11,axiom,(
% 0.21/0.53    ! [X0] : ~(! [X1] : ~(! [X2,X3] : ~(k4_tarski(X2,X3) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_mcart_1)).
% 0.21/0.53  fof(f228,plain,(
% 0.21/0.53    ( ! [X0] : (~r2_hidden(sK5(X0),k2_enumset1(sK1,sK1,sK1,sK1)) | ~r2_hidden(sK1,X0) | k1_xboole_0 = X0) ) | ~spl8_1),
% 0.21/0.53    inference(extensionality_resolution,[],[f87,f213])).
% 0.21/0.53  fof(f213,plain,(
% 0.21/0.53    ( ! [X1] : (sK1 != sK5(X1) | ~r2_hidden(sK1,X1) | k1_xboole_0 = X1) ) | ~spl8_1),
% 0.21/0.53    inference(superposition,[],[f46,f210])).
% 0.21/0.53  fof(f210,plain,(
% 0.21/0.53    sK1 = k4_tarski(sK1,sK3) | ~spl8_1),
% 0.21/0.53    inference(forward_demodulation,[],[f41,f176])).
% 0.21/0.53  fof(f176,plain,(
% 0.21/0.53    sK1 = sK2 | ~spl8_1),
% 0.21/0.53    inference(backward_demodulation,[],[f105,f95])).
% 0.21/0.53  % (30923)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.53  fof(f95,plain,(
% 0.21/0.53    sK1 = k1_mcart_1(sK1) | ~spl8_1),
% 0.21/0.53    inference(avatar_component_clause,[],[f93])).
% 0.21/0.53  fof(f93,plain,(
% 0.21/0.53    spl8_1 <=> sK1 = k1_mcart_1(sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.21/0.53  fof(f105,plain,(
% 0.21/0.53    k1_mcart_1(sK1) = sK2),
% 0.21/0.53    inference(superposition,[],[f49,f41])).
% 0.21/0.53  fof(f49,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f10])).
% 0.21/0.53  fof(f10,axiom,(
% 0.21/0.53    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    sK1 = k4_tarski(sK2,sK3)),
% 0.21/0.53    inference(cnf_transformation,[],[f22])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    (sK1 = k2_mcart_1(sK1) | sK1 = k1_mcart_1(sK1)) & sK1 = k4_tarski(sK2,sK3)),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f14,f21,f20])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ? [X0] : ((k2_mcart_1(X0) = X0 | k1_mcart_1(X0) = X0) & ? [X1,X2] : k4_tarski(X1,X2) = X0) => ((sK1 = k2_mcart_1(sK1) | sK1 = k1_mcart_1(sK1)) & ? [X2,X1] : k4_tarski(X1,X2) = sK1)),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  % (30932)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.53  % (30937)Refutation not found, incomplete strategy% (30937)------------------------------
% 0.21/0.53  % (30937)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (30937)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (30937)Memory used [KB]: 10618
% 0.21/0.53  % (30937)Time elapsed: 0.129 s
% 0.21/0.53  % (30937)------------------------------
% 0.21/0.53  % (30937)------------------------------
% 0.21/0.54  % (30943)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.54  fof(f21,plain,(
% 0.21/0.54    ? [X2,X1] : k4_tarski(X1,X2) = sK1 => sK1 = k4_tarski(sK2,sK3)),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f14,plain,(
% 0.21/0.54    ? [X0] : ((k2_mcart_1(X0) = X0 | k1_mcart_1(X0) = X0) & ? [X1,X2] : k4_tarski(X1,X2) = X0)),
% 0.21/0.54    inference(ennf_transformation,[],[f13])).
% 0.21/0.54  fof(f13,negated_conjecture,(
% 0.21/0.54    ~! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 0.21/0.54    inference(negated_conjecture,[],[f12])).
% 0.21/0.54  fof(f12,conjecture,(
% 0.21/0.54    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).
% 0.21/0.54  fof(f46,plain,(
% 0.21/0.54    ( ! [X2,X0,X3] : (k4_tarski(X2,X3) != sK5(X0) | ~r2_hidden(X2,X0) | k1_xboole_0 = X0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f26])).
% 0.21/0.54  fof(f87,plain,(
% 0.21/0.54    ( ! [X0,X3] : (~r2_hidden(X3,k2_enumset1(X0,X0,X0,X0)) | X0 = X3) )),
% 0.21/0.54    inference(equality_resolution,[],[f78])).
% 0.21/0.54  fof(f78,plain,(
% 0.21/0.54    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 0.21/0.54    inference(definition_unfolding,[],[f54,f74])).
% 0.21/0.54  fof(f54,plain,(
% 0.21/0.54    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 0.21/0.54    inference(cnf_transformation,[],[f32])).
% 0.21/0.54  fof(f175,plain,(
% 0.21/0.54    ~spl8_2),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f174])).
% 0.21/0.54  fof(f174,plain,(
% 0.21/0.54    $false | ~spl8_2),
% 0.21/0.54    inference(subsumption_resolution,[],[f173,f165])).
% 0.21/0.54  fof(f173,plain,(
% 0.21/0.54    k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1) | ~spl8_2),
% 0.21/0.54    inference(subsumption_resolution,[],[f172,f86])).
% 0.21/0.54  fof(f172,plain,(
% 0.21/0.54    ~r2_hidden(sK1,k2_enumset1(sK1,sK1,sK1,sK1)) | k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1) | ~spl8_2),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f170])).
% 0.21/0.54  fof(f170,plain,(
% 0.21/0.54    ~r2_hidden(sK1,k2_enumset1(sK1,sK1,sK1,sK1)) | k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1) | k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1) | ~spl8_2),
% 0.21/0.54    inference(resolution,[],[f142,f45])).
% 0.21/0.54  fof(f142,plain,(
% 0.21/0.54    ( ! [X0] : (~r2_hidden(sK5(X0),k2_enumset1(sK1,sK1,sK1,sK1)) | ~r2_hidden(sK1,X0) | k1_xboole_0 = X0) ) | ~spl8_2),
% 0.21/0.54    inference(extensionality_resolution,[],[f87,f137])).
% 0.21/0.54  fof(f137,plain,(
% 0.21/0.54    ( ! [X0] : (sK1 != sK5(X0) | ~r2_hidden(sK1,X0) | k1_xboole_0 = X0) ) | ~spl8_2),
% 0.21/0.54    inference(superposition,[],[f47,f108])).
% 0.21/0.54  fof(f108,plain,(
% 0.21/0.54    sK1 = k4_tarski(sK2,sK1) | ~spl8_2),
% 0.21/0.54    inference(backward_demodulation,[],[f41,f107])).
% 0.21/0.54  fof(f107,plain,(
% 0.21/0.54    sK1 = sK3 | ~spl8_2),
% 0.21/0.54    inference(forward_demodulation,[],[f106,f99])).
% 0.21/0.54  fof(f99,plain,(
% 0.21/0.54    sK1 = k2_mcart_1(sK1) | ~spl8_2),
% 0.21/0.54    inference(avatar_component_clause,[],[f97])).
% 0.21/0.54  fof(f97,plain,(
% 0.21/0.54    spl8_2 <=> sK1 = k2_mcart_1(sK1)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.21/0.54  fof(f106,plain,(
% 0.21/0.54    k2_mcart_1(sK1) = sK3),
% 0.21/0.54    inference(superposition,[],[f50,f41])).
% 0.21/0.54  fof(f50,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 0.21/0.54    inference(cnf_transformation,[],[f10])).
% 0.21/0.54  fof(f47,plain,(
% 0.21/0.54    ( ! [X2,X0,X3] : (k4_tarski(X2,X3) != sK5(X0) | ~r2_hidden(X3,X0) | k1_xboole_0 = X0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f26])).
% 0.21/0.54  fof(f100,plain,(
% 0.21/0.54    spl8_1 | spl8_2),
% 0.21/0.54    inference(avatar_split_clause,[],[f42,f97,f93])).
% 0.21/0.54  fof(f42,plain,(
% 0.21/0.54    sK1 = k2_mcart_1(sK1) | sK1 = k1_mcart_1(sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f22])).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (30927)------------------------------
% 0.21/0.54  % (30927)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (30927)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (30927)Memory used [KB]: 10746
% 0.21/0.54  % (30927)Time elapsed: 0.118 s
% 0.21/0.54  % (30927)------------------------------
% 0.21/0.54  % (30927)------------------------------
% 0.21/0.54  % (30922)Refutation not found, incomplete strategy% (30922)------------------------------
% 0.21/0.54  % (30922)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (30922)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (30922)Memory used [KB]: 1663
% 0.21/0.54  % (30922)Time elapsed: 0.138 s
% 0.21/0.54  % (30922)------------------------------
% 0.21/0.54  % (30922)------------------------------
% 0.21/0.54  % (30949)Refutation not found, incomplete strategy% (30949)------------------------------
% 0.21/0.54  % (30949)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (30949)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (30949)Memory used [KB]: 10746
% 0.21/0.54  % (30949)Time elapsed: 0.132 s
% 0.21/0.54  % (30949)------------------------------
% 0.21/0.54  % (30949)------------------------------
% 0.21/0.54  % (30920)Success in time 0.178 s
%------------------------------------------------------------------------------
