%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:00 EST 2020

% Result     : Theorem 1.46s
% Output     : Refutation 1.46s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 124 expanded)
%              Number of leaves         :   18 (  48 expanded)
%              Depth                    :    7
%              Number of atoms          :  176 ( 312 expanded)
%              Number of equality atoms :   33 (  92 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f167,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f63,f68,f73,f78,f98,f115,f129,f133,f145,f154,f156,f164,f166])).

fof(f166,plain,
    ( spl10_2
    | ~ spl10_7 ),
    inference(avatar_contradiction_clause,[],[f165])).

fof(f165,plain,
    ( $false
    | spl10_2
    | ~ spl10_7 ),
    inference(unit_resulting_resolution,[],[f67,f103,f25])).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f103,plain,
    ( v1_xboole_0(sK1)
    | ~ spl10_7 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl10_7
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).

fof(f67,plain,
    ( k1_xboole_0 != sK1
    | spl10_2 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl10_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f164,plain,
    ( ~ spl10_5
    | spl10_7 ),
    inference(avatar_contradiction_clause,[],[f157])).

fof(f157,plain,
    ( $false
    | ~ spl10_5
    | spl10_7 ),
    inference(unit_resulting_resolution,[],[f104,f94,f26])).

fof(f26,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f94,plain,
    ( ! [X1] : ~ r2_hidden(X1,sK1)
    | ~ spl10_5 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl10_5
  <=> ! [X1] : ~ r2_hidden(X1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f104,plain,
    ( ~ v1_xboole_0(sK1)
    | spl10_7 ),
    inference(avatar_component_clause,[],[f102])).

fof(f156,plain,
    ( spl10_1
    | ~ spl10_12 ),
    inference(avatar_contradiction_clause,[],[f155])).

fof(f155,plain,
    ( $false
    | spl10_1
    | ~ spl10_12 ),
    inference(unit_resulting_resolution,[],[f62,f139,f25])).

fof(f139,plain,
    ( v1_xboole_0(sK0)
    | ~ spl10_12 ),
    inference(avatar_component_clause,[],[f138])).

fof(f138,plain,
    ( spl10_12
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).

fof(f62,plain,
    ( k1_xboole_0 != sK0
    | spl10_1 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl10_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f154,plain,
    ( spl10_12
    | ~ spl10_8 ),
    inference(avatar_split_clause,[],[f147,f106,f138])).

fof(f106,plain,
    ( spl10_8
  <=> ! [X0] : ~ r2_hidden(X0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f147,plain,
    ( v1_xboole_0(sK0)
    | ~ spl10_8 ),
    inference(resolution,[],[f107,f26])).

fof(f107,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK0)
    | ~ spl10_8 ),
    inference(avatar_component_clause,[],[f106])).

fof(f145,plain,
    ( spl10_10
    | ~ spl10_11 ),
    inference(avatar_split_clause,[],[f144,f131,f126])).

fof(f126,plain,
    ( spl10_10
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).

fof(f131,plain,
    ( spl10_11
  <=> ! [X0] :
        ( r2_hidden(X0,sK0)
        | ~ r2_hidden(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).

fof(f144,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl10_11 ),
    inference(duplicate_literal_removal,[],[f142])).

fof(f142,plain,
    ( r1_tarski(sK1,sK0)
    | r1_tarski(sK1,sK0)
    | ~ spl10_11 ),
    inference(resolution,[],[f136,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f136,plain,
    ( ! [X2] :
        ( ~ r2_hidden(sK4(X2,sK0),sK1)
        | r1_tarski(X2,sK0) )
    | ~ spl10_11 ),
    inference(resolution,[],[f132,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f132,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK0)
        | ~ r2_hidden(X0,sK1) )
    | ~ spl10_11 ),
    inference(avatar_component_clause,[],[f131])).

fof(f133,plain,
    ( spl10_8
    | spl10_11
    | ~ spl10_4 ),
    inference(avatar_split_clause,[],[f88,f75,f131,f106])).

fof(f75,plain,
    ( spl10_4
  <=> k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f88,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,sK0)
        | ~ r2_hidden(X0,sK1)
        | ~ r2_hidden(X1,sK0) )
    | ~ spl10_4 ),
    inference(resolution,[],[f80,f49])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f80,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(k4_tarski(X2,X3),k2_zfmisc_1(sK0,sK1))
        | r2_hidden(X3,sK0) )
    | ~ spl10_4 ),
    inference(superposition,[],[f48,f77])).

fof(f77,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK1,sK0)
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f75])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f129,plain,
    ( spl10_3
    | ~ spl10_10
    | ~ spl10_9 ),
    inference(avatar_split_clause,[],[f117,f112,f126,f70])).

fof(f70,plain,
    ( spl10_3
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f112,plain,
    ( spl10_9
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).

fof(f117,plain,
    ( ~ r1_tarski(sK1,sK0)
    | sK0 = sK1
    | ~ spl10_9 ),
    inference(resolution,[],[f114,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f114,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl10_9 ),
    inference(avatar_component_clause,[],[f112])).

fof(f115,plain,
    ( spl10_9
    | ~ spl10_6 ),
    inference(avatar_split_clause,[],[f110,f96,f112])).

fof(f96,plain,
    ( spl10_6
  <=> ! [X0] :
        ( r2_hidden(X0,sK1)
        | ~ r2_hidden(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f110,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl10_6 ),
    inference(duplicate_literal_removal,[],[f109])).

fof(f109,plain,
    ( r1_tarski(sK0,sK1)
    | r1_tarski(sK0,sK1)
    | ~ spl10_6 ),
    inference(resolution,[],[f100,f34])).

fof(f100,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK4(X1,sK1),sK0)
        | r1_tarski(X1,sK1) )
    | ~ spl10_6 ),
    inference(resolution,[],[f97,f35])).

fof(f97,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK1)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl10_6 ),
    inference(avatar_component_clause,[],[f96])).

fof(f98,plain,
    ( spl10_5
    | spl10_6
    | ~ spl10_4 ),
    inference(avatar_split_clause,[],[f84,f75,f96,f93])).

fof(f84,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,sK1)
        | ~ r2_hidden(X1,sK1)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl10_4 ),
    inference(resolution,[],[f79,f49])).

fof(f79,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK0,sK1))
        | r2_hidden(X0,sK1) )
    | ~ spl10_4 ),
    inference(superposition,[],[f47,f77])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f78,plain,(
    spl10_4 ),
    inference(avatar_split_clause,[],[f19,f75])).

fof(f19,plain,(
    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0)
       => ( X0 = X1
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0)
     => ( X0 = X1
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t114_zfmisc_1)).

fof(f73,plain,(
    ~ spl10_3 ),
    inference(avatar_split_clause,[],[f22,f70])).

fof(f22,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f15])).

fof(f68,plain,(
    ~ spl10_2 ),
    inference(avatar_split_clause,[],[f21,f65])).

fof(f21,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f15])).

fof(f63,plain,(
    ~ spl10_1 ),
    inference(avatar_split_clause,[],[f20,f60])).

fof(f20,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:06:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (16072)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (16069)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (16071)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (16080)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.28/0.53  % (16075)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.28/0.53  % (16085)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.28/0.53  % (16076)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.28/0.53  % (16073)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.28/0.54  % (16087)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.28/0.54  % (16090)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.28/0.54  % (16088)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.28/0.54  % (16089)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.28/0.54  % (16082)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.28/0.54  % (16067)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.28/0.54  % (16067)Refutation not found, incomplete strategy% (16067)------------------------------
% 1.28/0.54  % (16067)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.54  % (16067)Termination reason: Refutation not found, incomplete strategy
% 1.28/0.54  
% 1.28/0.54  % (16067)Memory used [KB]: 1663
% 1.28/0.54  % (16067)Time elapsed: 0.132 s
% 1.28/0.54  % (16067)------------------------------
% 1.28/0.54  % (16067)------------------------------
% 1.46/0.54  % (16089)Refutation found. Thanks to Tanya!
% 1.46/0.54  % SZS status Theorem for theBenchmark
% 1.46/0.54  % SZS output start Proof for theBenchmark
% 1.46/0.54  fof(f167,plain,(
% 1.46/0.54    $false),
% 1.46/0.54    inference(avatar_sat_refutation,[],[f63,f68,f73,f78,f98,f115,f129,f133,f145,f154,f156,f164,f166])).
% 1.46/0.54  fof(f166,plain,(
% 1.46/0.54    spl10_2 | ~spl10_7),
% 1.46/0.54    inference(avatar_contradiction_clause,[],[f165])).
% 1.46/0.54  fof(f165,plain,(
% 1.46/0.54    $false | (spl10_2 | ~spl10_7)),
% 1.46/0.54    inference(unit_resulting_resolution,[],[f67,f103,f25])).
% 1.46/0.54  fof(f25,plain,(
% 1.46/0.54    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 1.46/0.54    inference(cnf_transformation,[],[f16])).
% 1.46/0.54  fof(f16,plain,(
% 1.46/0.54    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.46/0.54    inference(ennf_transformation,[],[f3])).
% 1.46/0.54  fof(f3,axiom,(
% 1.46/0.54    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.46/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 1.46/0.54  fof(f103,plain,(
% 1.46/0.54    v1_xboole_0(sK1) | ~spl10_7),
% 1.46/0.54    inference(avatar_component_clause,[],[f102])).
% 1.46/0.54  fof(f102,plain,(
% 1.46/0.54    spl10_7 <=> v1_xboole_0(sK1)),
% 1.46/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).
% 1.46/0.54  fof(f67,plain,(
% 1.46/0.54    k1_xboole_0 != sK1 | spl10_2),
% 1.46/0.54    inference(avatar_component_clause,[],[f65])).
% 1.46/0.54  fof(f65,plain,(
% 1.46/0.54    spl10_2 <=> k1_xboole_0 = sK1),
% 1.46/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 1.46/0.54  fof(f164,plain,(
% 1.46/0.54    ~spl10_5 | spl10_7),
% 1.46/0.54    inference(avatar_contradiction_clause,[],[f157])).
% 1.46/0.54  fof(f157,plain,(
% 1.46/0.54    $false | (~spl10_5 | spl10_7)),
% 1.46/0.54    inference(unit_resulting_resolution,[],[f104,f94,f26])).
% 1.46/0.54  fof(f26,plain,(
% 1.46/0.54    ( ! [X0] : (r2_hidden(sK2(X0),X0) | v1_xboole_0(X0)) )),
% 1.46/0.54    inference(cnf_transformation,[],[f1])).
% 1.46/0.54  fof(f1,axiom,(
% 1.46/0.54    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.46/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.46/0.54  fof(f94,plain,(
% 1.46/0.54    ( ! [X1] : (~r2_hidden(X1,sK1)) ) | ~spl10_5),
% 1.46/0.54    inference(avatar_component_clause,[],[f93])).
% 1.46/0.54  fof(f93,plain,(
% 1.46/0.54    spl10_5 <=> ! [X1] : ~r2_hidden(X1,sK1)),
% 1.46/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).
% 1.46/0.54  fof(f104,plain,(
% 1.46/0.54    ~v1_xboole_0(sK1) | spl10_7),
% 1.46/0.54    inference(avatar_component_clause,[],[f102])).
% 1.46/0.54  fof(f156,plain,(
% 1.46/0.54    spl10_1 | ~spl10_12),
% 1.46/0.54    inference(avatar_contradiction_clause,[],[f155])).
% 1.46/0.54  fof(f155,plain,(
% 1.46/0.54    $false | (spl10_1 | ~spl10_12)),
% 1.46/0.54    inference(unit_resulting_resolution,[],[f62,f139,f25])).
% 1.46/0.54  fof(f139,plain,(
% 1.46/0.54    v1_xboole_0(sK0) | ~spl10_12),
% 1.46/0.54    inference(avatar_component_clause,[],[f138])).
% 1.46/0.54  fof(f138,plain,(
% 1.46/0.54    spl10_12 <=> v1_xboole_0(sK0)),
% 1.46/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).
% 1.46/0.54  fof(f62,plain,(
% 1.46/0.54    k1_xboole_0 != sK0 | spl10_1),
% 1.46/0.54    inference(avatar_component_clause,[],[f60])).
% 1.46/0.54  fof(f60,plain,(
% 1.46/0.54    spl10_1 <=> k1_xboole_0 = sK0),
% 1.46/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 1.46/0.54  fof(f154,plain,(
% 1.46/0.54    spl10_12 | ~spl10_8),
% 1.46/0.54    inference(avatar_split_clause,[],[f147,f106,f138])).
% 1.46/0.54  fof(f106,plain,(
% 1.46/0.54    spl10_8 <=> ! [X0] : ~r2_hidden(X0,sK0)),
% 1.46/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).
% 1.46/0.54  fof(f147,plain,(
% 1.46/0.54    v1_xboole_0(sK0) | ~spl10_8),
% 1.46/0.54    inference(resolution,[],[f107,f26])).
% 1.46/0.54  fof(f107,plain,(
% 1.46/0.54    ( ! [X0] : (~r2_hidden(X0,sK0)) ) | ~spl10_8),
% 1.46/0.54    inference(avatar_component_clause,[],[f106])).
% 1.46/0.54  fof(f145,plain,(
% 1.46/0.54    spl10_10 | ~spl10_11),
% 1.46/0.54    inference(avatar_split_clause,[],[f144,f131,f126])).
% 1.46/0.54  fof(f126,plain,(
% 1.46/0.54    spl10_10 <=> r1_tarski(sK1,sK0)),
% 1.46/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).
% 1.46/0.54  fof(f131,plain,(
% 1.46/0.54    spl10_11 <=> ! [X0] : (r2_hidden(X0,sK0) | ~r2_hidden(X0,sK1))),
% 1.46/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).
% 1.46/0.54  fof(f144,plain,(
% 1.46/0.54    r1_tarski(sK1,sK0) | ~spl10_11),
% 1.46/0.54    inference(duplicate_literal_removal,[],[f142])).
% 1.46/0.54  fof(f142,plain,(
% 1.46/0.54    r1_tarski(sK1,sK0) | r1_tarski(sK1,sK0) | ~spl10_11),
% 1.46/0.54    inference(resolution,[],[f136,f34])).
% 1.46/0.54  fof(f34,plain,(
% 1.46/0.54    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.46/0.54    inference(cnf_transformation,[],[f18])).
% 1.46/0.54  fof(f18,plain,(
% 1.46/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.46/0.54    inference(ennf_transformation,[],[f2])).
% 1.46/0.54  fof(f2,axiom,(
% 1.46/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.46/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.46/0.54  fof(f136,plain,(
% 1.46/0.54    ( ! [X2] : (~r2_hidden(sK4(X2,sK0),sK1) | r1_tarski(X2,sK0)) ) | ~spl10_11),
% 1.46/0.54    inference(resolution,[],[f132,f35])).
% 1.46/0.54  fof(f35,plain,(
% 1.46/0.54    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.46/0.54    inference(cnf_transformation,[],[f18])).
% 1.46/0.54  fof(f132,plain,(
% 1.46/0.54    ( ! [X0] : (r2_hidden(X0,sK0) | ~r2_hidden(X0,sK1)) ) | ~spl10_11),
% 1.46/0.54    inference(avatar_component_clause,[],[f131])).
% 1.46/0.54  fof(f133,plain,(
% 1.46/0.54    spl10_8 | spl10_11 | ~spl10_4),
% 1.46/0.54    inference(avatar_split_clause,[],[f88,f75,f131,f106])).
% 1.46/0.54  fof(f75,plain,(
% 1.46/0.54    spl10_4 <=> k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK1,sK0)),
% 1.46/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).
% 1.46/0.54  fof(f88,plain,(
% 1.46/0.54    ( ! [X0,X1] : (r2_hidden(X0,sK0) | ~r2_hidden(X0,sK1) | ~r2_hidden(X1,sK0)) ) | ~spl10_4),
% 1.46/0.54    inference(resolution,[],[f80,f49])).
% 1.46/0.54  fof(f49,plain,(
% 1.46/0.54    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 1.46/0.54    inference(cnf_transformation,[],[f9])).
% 1.46/0.54  fof(f9,axiom,(
% 1.46/0.54    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 1.46/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 1.46/0.54  fof(f80,plain,(
% 1.46/0.54    ( ! [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),k2_zfmisc_1(sK0,sK1)) | r2_hidden(X3,sK0)) ) | ~spl10_4),
% 1.46/0.54    inference(superposition,[],[f48,f77])).
% 1.46/0.54  fof(f77,plain,(
% 1.46/0.54    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK1,sK0) | ~spl10_4),
% 1.46/0.54    inference(avatar_component_clause,[],[f75])).
% 1.46/0.54  fof(f48,plain,(
% 1.46/0.54    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X1,X3)) )),
% 1.46/0.54    inference(cnf_transformation,[],[f9])).
% 1.46/0.54  fof(f129,plain,(
% 1.46/0.54    spl10_3 | ~spl10_10 | ~spl10_9),
% 1.46/0.54    inference(avatar_split_clause,[],[f117,f112,f126,f70])).
% 1.46/0.54  fof(f70,plain,(
% 1.46/0.54    spl10_3 <=> sK0 = sK1),
% 1.46/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).
% 1.46/0.54  fof(f112,plain,(
% 1.46/0.54    spl10_9 <=> r1_tarski(sK0,sK1)),
% 1.46/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).
% 1.46/0.54  fof(f117,plain,(
% 1.46/0.54    ~r1_tarski(sK1,sK0) | sK0 = sK1 | ~spl10_9),
% 1.46/0.54    inference(resolution,[],[f114,f32])).
% 1.46/0.54  fof(f32,plain,(
% 1.46/0.54    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 1.46/0.54    inference(cnf_transformation,[],[f5])).
% 1.46/0.54  fof(f5,axiom,(
% 1.46/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.46/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.46/0.54  fof(f114,plain,(
% 1.46/0.54    r1_tarski(sK0,sK1) | ~spl10_9),
% 1.46/0.54    inference(avatar_component_clause,[],[f112])).
% 1.46/0.54  fof(f115,plain,(
% 1.46/0.54    spl10_9 | ~spl10_6),
% 1.46/0.54    inference(avatar_split_clause,[],[f110,f96,f112])).
% 1.46/0.54  fof(f96,plain,(
% 1.46/0.54    spl10_6 <=> ! [X0] : (r2_hidden(X0,sK1) | ~r2_hidden(X0,sK0))),
% 1.46/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).
% 1.46/0.54  fof(f110,plain,(
% 1.46/0.54    r1_tarski(sK0,sK1) | ~spl10_6),
% 1.46/0.54    inference(duplicate_literal_removal,[],[f109])).
% 1.46/0.54  fof(f109,plain,(
% 1.46/0.54    r1_tarski(sK0,sK1) | r1_tarski(sK0,sK1) | ~spl10_6),
% 1.46/0.54    inference(resolution,[],[f100,f34])).
% 1.46/0.54  fof(f100,plain,(
% 1.46/0.54    ( ! [X1] : (~r2_hidden(sK4(X1,sK1),sK0) | r1_tarski(X1,sK1)) ) | ~spl10_6),
% 1.46/0.54    inference(resolution,[],[f97,f35])).
% 1.46/0.54  fof(f97,plain,(
% 1.46/0.54    ( ! [X0] : (r2_hidden(X0,sK1) | ~r2_hidden(X0,sK0)) ) | ~spl10_6),
% 1.46/0.54    inference(avatar_component_clause,[],[f96])).
% 1.46/0.54  fof(f98,plain,(
% 1.46/0.54    spl10_5 | spl10_6 | ~spl10_4),
% 1.46/0.54    inference(avatar_split_clause,[],[f84,f75,f96,f93])).
% 1.46/0.54  fof(f84,plain,(
% 1.46/0.54    ( ! [X0,X1] : (r2_hidden(X0,sK1) | ~r2_hidden(X1,sK1) | ~r2_hidden(X0,sK0)) ) | ~spl10_4),
% 1.46/0.54    inference(resolution,[],[f79,f49])).
% 1.46/0.54  fof(f79,plain,(
% 1.46/0.54    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK0,sK1)) | r2_hidden(X0,sK1)) ) | ~spl10_4),
% 1.46/0.54    inference(superposition,[],[f47,f77])).
% 1.46/0.54  fof(f47,plain,(
% 1.46/0.54    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X0,X2)) )),
% 1.46/0.54    inference(cnf_transformation,[],[f9])).
% 1.46/0.54  fof(f78,plain,(
% 1.46/0.54    spl10_4),
% 1.46/0.54    inference(avatar_split_clause,[],[f19,f75])).
% 1.46/0.54  fof(f19,plain,(
% 1.46/0.54    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK1,sK0)),
% 1.46/0.54    inference(cnf_transformation,[],[f15])).
% 1.46/0.54  fof(f15,plain,(
% 1.46/0.54    ? [X0,X1] : (X0 != X1 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0))),
% 1.46/0.54    inference(flattening,[],[f14])).
% 1.46/0.54  fof(f14,plain,(
% 1.46/0.54    ? [X0,X1] : ((X0 != X1 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0))),
% 1.46/0.54    inference(ennf_transformation,[],[f12])).
% 1.46/0.54  fof(f12,negated_conjecture,(
% 1.46/0.54    ~! [X0,X1] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) => (X0 = X1 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.46/0.54    inference(negated_conjecture,[],[f11])).
% 1.46/0.54  fof(f11,conjecture,(
% 1.46/0.54    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) => (X0 = X1 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.46/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t114_zfmisc_1)).
% 1.46/0.54  fof(f73,plain,(
% 1.46/0.54    ~spl10_3),
% 1.46/0.54    inference(avatar_split_clause,[],[f22,f70])).
% 1.46/0.54  fof(f22,plain,(
% 1.46/0.54    sK0 != sK1),
% 1.46/0.54    inference(cnf_transformation,[],[f15])).
% 1.46/0.54  fof(f68,plain,(
% 1.46/0.54    ~spl10_2),
% 1.46/0.54    inference(avatar_split_clause,[],[f21,f65])).
% 1.46/0.54  fof(f21,plain,(
% 1.46/0.54    k1_xboole_0 != sK1),
% 1.46/0.54    inference(cnf_transformation,[],[f15])).
% 1.46/0.54  fof(f63,plain,(
% 1.46/0.54    ~spl10_1),
% 1.46/0.54    inference(avatar_split_clause,[],[f20,f60])).
% 1.46/0.54  fof(f20,plain,(
% 1.46/0.54    k1_xboole_0 != sK0),
% 1.46/0.54    inference(cnf_transformation,[],[f15])).
% 1.46/0.54  % SZS output end Proof for theBenchmark
% 1.46/0.54  % (16089)------------------------------
% 1.46/0.54  % (16089)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.54  % (16089)Termination reason: Refutation
% 1.46/0.54  
% 1.46/0.54  % (16089)Memory used [KB]: 10746
% 1.46/0.54  % (16089)Time elapsed: 0.141 s
% 1.46/0.54  % (16089)------------------------------
% 1.46/0.54  % (16089)------------------------------
% 1.46/0.54  % (16094)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.46/0.55  % (16092)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.46/0.55  % (16081)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.46/0.55  % (16077)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.46/0.55  % (16070)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.46/0.55  % (16079)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.46/0.55  % (16074)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.46/0.55  % (16086)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.46/0.55  % (16068)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.46/0.55  % (16091)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.46/0.55  % (16096)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.46/0.55  % (16084)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.46/0.55  % (16078)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.46/0.55  % (16084)Refutation not found, incomplete strategy% (16084)------------------------------
% 1.46/0.55  % (16084)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.55  % (16084)Termination reason: Refutation not found, incomplete strategy
% 1.46/0.55  
% 1.46/0.55  % (16084)Memory used [KB]: 10618
% 1.46/0.55  % (16084)Time elapsed: 0.115 s
% 1.46/0.55  % (16084)------------------------------
% 1.46/0.55  % (16084)------------------------------
% 1.46/0.56  % (16083)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.46/0.56  % (16093)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.46/0.56  % (16066)Success in time 0.199 s
%------------------------------------------------------------------------------
