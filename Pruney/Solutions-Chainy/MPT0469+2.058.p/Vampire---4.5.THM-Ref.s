%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:42 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 1.30s
% Verified   : 
% Statistics : Number of formulae       :   46 (  63 expanded)
%              Number of leaves         :   14 (  28 expanded)
%              Depth                    :    5
%              Number of atoms          :  114 ( 154 expanded)
%              Number of equality atoms :   24 (  30 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f200,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f46,f50,f58,f62,f88,f165,f169,f190,f199])).

% (19239)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% (19226)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
fof(f199,plain,
    ( spl10_1
    | ~ spl10_12
    | ~ spl10_25 ),
    inference(avatar_contradiction_clause,[],[f191])).

fof(f191,plain,
    ( $false
    | spl10_1
    | ~ spl10_12
    | ~ spl10_25 ),
    inference(unit_resulting_resolution,[],[f42,f87,f87,f168])).

fof(f168,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK4(X0,X1),X1)
        | r2_hidden(k4_tarski(sK6(X0,X1),sK4(X0,X1)),X0)
        | k2_relat_1(X0) = X1 )
    | ~ spl10_25 ),
    inference(avatar_component_clause,[],[f167])).

fof(f167,plain,
    ( spl10_25
  <=> ! [X1,X0] :
        ( r2_hidden(k4_tarski(sK6(X0,X1),sK4(X0,X1)),X0)
        | r2_hidden(sK4(X0,X1),X1)
        | k2_relat_1(X0) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_25])])).

fof(f87,plain,
    ( ! [X1] : ~ r2_hidden(X1,k1_xboole_0)
    | ~ spl10_12 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl10_12
  <=> ! [X1] : ~ r2_hidden(X1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).

fof(f42,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | spl10_1 ),
    inference(avatar_component_clause,[],[f41])).

fof(f41,plain,
    ( spl10_1
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f190,plain,
    ( spl10_2
    | ~ spl10_12
    | ~ spl10_24 ),
    inference(avatar_contradiction_clause,[],[f182])).

fof(f182,plain,
    ( $false
    | spl10_2
    | ~ spl10_12
    | ~ spl10_24 ),
    inference(unit_resulting_resolution,[],[f45,f87,f87,f164])).

fof(f164,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK1(X0,X1),X1)
        | r2_hidden(k4_tarski(sK1(X0,X1),sK3(X0,X1)),X0)
        | k1_relat_1(X0) = X1 )
    | ~ spl10_24 ),
    inference(avatar_component_clause,[],[f163])).

fof(f163,plain,
    ( spl10_24
  <=> ! [X1,X0] :
        ( r2_hidden(k4_tarski(sK1(X0,X1),sK3(X0,X1)),X0)
        | r2_hidden(sK1(X0,X1),X1)
        | k1_relat_1(X0) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_24])])).

fof(f45,plain,
    ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | spl10_2 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl10_2
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f169,plain,(
    spl10_25 ),
    inference(avatar_split_clause,[],[f25,f167])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK6(X0,X1),sK4(X0,X1)),X0)
      | r2_hidden(sK4(X0,X1),X1)
      | k2_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(f165,plain,(
    spl10_24 ),
    inference(avatar_split_clause,[],[f21,f163])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK1(X0,X1),sK3(X0,X1)),X0)
      | r2_hidden(sK1(X0,X1),X1)
      | k1_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(f88,plain,
    ( spl10_12
    | ~ spl10_3
    | ~ spl10_5
    | ~ spl10_6 ),
    inference(avatar_split_clause,[],[f80,f60,f56,f48,f86])).

fof(f48,plain,
    ( spl10_3
  <=> ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f56,plain,
    ( spl10_5
  <=> ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f60,plain,
    ( spl10_6
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f80,plain,
    ( ! [X1] : ~ r2_hidden(X1,k1_xboole_0)
    | ~ spl10_3
    | ~ spl10_5
    | ~ spl10_6 ),
    inference(subsumption_resolution,[],[f79,f49])).

fof(f49,plain,
    ( ! [X0] : r1_xboole_0(X0,k1_xboole_0)
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f48])).

fof(f79,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,k1_xboole_0)
        | ~ r1_xboole_0(X0,k1_xboole_0) )
    | ~ spl10_5
    | ~ spl10_6 ),
    inference(superposition,[],[f61,f57])).

fof(f57,plain,
    ( ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)
    | ~ spl10_5 ),
    inference(avatar_component_clause,[],[f56])).

fof(f61,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl10_6 ),
    inference(avatar_component_clause,[],[f60])).

fof(f62,plain,(
    spl10_6 ),
    inference(avatar_split_clause,[],[f17,f60])).

% (19221)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
fof(f17,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f58,plain,(
    spl10_5 ),
    inference(avatar_split_clause,[],[f16,f56])).

fof(f16,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f50,plain,(
    spl10_3 ),
    inference(avatar_split_clause,[],[f15,f48])).

fof(f15,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f46,plain,
    ( ~ spl10_1
    | ~ spl10_2 ),
    inference(avatar_split_clause,[],[f13,f44,f41])).

fof(f13,plain,
    ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | k1_xboole_0 != k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
      & k1_xboole_0 = k1_relat_1(k1_xboole_0) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n009.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:30:11 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.47  % (19232)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.47  % (19232)Refutation not found, incomplete strategy% (19232)------------------------------
% 0.20/0.47  % (19232)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (19232)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (19232)Memory used [KB]: 10618
% 0.20/0.47  % (19232)Time elapsed: 0.036 s
% 0.20/0.47  % (19232)------------------------------
% 0.20/0.47  % (19232)------------------------------
% 0.20/0.47  % (19222)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.47  % (19222)Refutation not found, incomplete strategy% (19222)------------------------------
% 0.20/0.47  % (19222)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (19222)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (19222)Memory used [KB]: 10618
% 0.20/0.47  % (19222)Time elapsed: 0.051 s
% 0.20/0.47  % (19222)------------------------------
% 0.20/0.47  % (19222)------------------------------
% 0.20/0.48  % (19225)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.48  % (19236)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.48  % (19235)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.48  % (19236)Refutation not found, incomplete strategy% (19236)------------------------------
% 0.20/0.48  % (19236)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (19236)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (19236)Memory used [KB]: 6140
% 0.20/0.48  % (19236)Time elapsed: 0.003 s
% 0.20/0.48  % (19236)------------------------------
% 0.20/0.48  % (19236)------------------------------
% 0.20/0.49  % (19228)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.51  % (19230)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.51  % (19227)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.52  % (19230)Refutation found. Thanks to Tanya!
% 0.20/0.52  % SZS status Theorem for theBenchmark
% 0.20/0.52  % (19231)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.52  % (19223)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f200,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(avatar_sat_refutation,[],[f46,f50,f58,f62,f88,f165,f169,f190,f199])).
% 0.20/0.53  % (19239)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.53  % (19226)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.30/0.53  fof(f199,plain,(
% 1.30/0.53    spl10_1 | ~spl10_12 | ~spl10_25),
% 1.30/0.53    inference(avatar_contradiction_clause,[],[f191])).
% 1.30/0.54  fof(f191,plain,(
% 1.30/0.54    $false | (spl10_1 | ~spl10_12 | ~spl10_25)),
% 1.30/0.54    inference(unit_resulting_resolution,[],[f42,f87,f87,f168])).
% 1.30/0.54  fof(f168,plain,(
% 1.30/0.54    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X1) | r2_hidden(k4_tarski(sK6(X0,X1),sK4(X0,X1)),X0) | k2_relat_1(X0) = X1) ) | ~spl10_25),
% 1.30/0.54    inference(avatar_component_clause,[],[f167])).
% 1.30/0.54  fof(f167,plain,(
% 1.30/0.54    spl10_25 <=> ! [X1,X0] : (r2_hidden(k4_tarski(sK6(X0,X1),sK4(X0,X1)),X0) | r2_hidden(sK4(X0,X1),X1) | k2_relat_1(X0) = X1)),
% 1.30/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_25])])).
% 1.30/0.54  fof(f87,plain,(
% 1.30/0.54    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0)) ) | ~spl10_12),
% 1.30/0.54    inference(avatar_component_clause,[],[f86])).
% 1.30/0.54  fof(f86,plain,(
% 1.30/0.54    spl10_12 <=> ! [X1] : ~r2_hidden(X1,k1_xboole_0)),
% 1.30/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).
% 1.30/0.54  fof(f42,plain,(
% 1.30/0.54    k1_xboole_0 != k2_relat_1(k1_xboole_0) | spl10_1),
% 1.30/0.54    inference(avatar_component_clause,[],[f41])).
% 1.30/0.54  fof(f41,plain,(
% 1.30/0.54    spl10_1 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.30/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 1.30/0.54  fof(f190,plain,(
% 1.30/0.54    spl10_2 | ~spl10_12 | ~spl10_24),
% 1.30/0.54    inference(avatar_contradiction_clause,[],[f182])).
% 1.30/0.54  fof(f182,plain,(
% 1.30/0.54    $false | (spl10_2 | ~spl10_12 | ~spl10_24)),
% 1.30/0.54    inference(unit_resulting_resolution,[],[f45,f87,f87,f164])).
% 1.30/0.54  fof(f164,plain,(
% 1.30/0.54    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X1) | r2_hidden(k4_tarski(sK1(X0,X1),sK3(X0,X1)),X0) | k1_relat_1(X0) = X1) ) | ~spl10_24),
% 1.30/0.54    inference(avatar_component_clause,[],[f163])).
% 1.30/0.54  fof(f163,plain,(
% 1.30/0.54    spl10_24 <=> ! [X1,X0] : (r2_hidden(k4_tarski(sK1(X0,X1),sK3(X0,X1)),X0) | r2_hidden(sK1(X0,X1),X1) | k1_relat_1(X0) = X1)),
% 1.30/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_24])])).
% 1.30/0.54  fof(f45,plain,(
% 1.30/0.54    k1_xboole_0 != k1_relat_1(k1_xboole_0) | spl10_2),
% 1.30/0.54    inference(avatar_component_clause,[],[f44])).
% 1.30/0.54  fof(f44,plain,(
% 1.30/0.54    spl10_2 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.30/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 1.30/0.54  fof(f169,plain,(
% 1.30/0.54    spl10_25),
% 1.30/0.54    inference(avatar_split_clause,[],[f25,f167])).
% 1.30/0.54  fof(f25,plain,(
% 1.30/0.54    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK6(X0,X1),sK4(X0,X1)),X0) | r2_hidden(sK4(X0,X1),X1) | k2_relat_1(X0) = X1) )),
% 1.30/0.54    inference(cnf_transformation,[],[f7])).
% 1.30/0.54  fof(f7,axiom,(
% 1.30/0.54    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 1.30/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).
% 1.30/0.54  fof(f165,plain,(
% 1.30/0.54    spl10_24),
% 1.30/0.54    inference(avatar_split_clause,[],[f21,f163])).
% 1.30/0.54  fof(f21,plain,(
% 1.30/0.54    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK1(X0,X1),sK3(X0,X1)),X0) | r2_hidden(sK1(X0,X1),X1) | k1_relat_1(X0) = X1) )),
% 1.30/0.54    inference(cnf_transformation,[],[f6])).
% 1.30/0.54  fof(f6,axiom,(
% 1.30/0.54    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 1.30/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).
% 1.30/0.54  fof(f88,plain,(
% 1.30/0.54    spl10_12 | ~spl10_3 | ~spl10_5 | ~spl10_6),
% 1.30/0.54    inference(avatar_split_clause,[],[f80,f60,f56,f48,f86])).
% 1.30/0.54  fof(f48,plain,(
% 1.30/0.54    spl10_3 <=> ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.30/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).
% 1.30/0.54  fof(f56,plain,(
% 1.30/0.54    spl10_5 <=> ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.30/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).
% 1.30/0.54  fof(f60,plain,(
% 1.30/0.54    spl10_6 <=> ! [X1,X0,X2] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1))),
% 1.30/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).
% 1.30/0.54  fof(f80,plain,(
% 1.30/0.54    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0)) ) | (~spl10_3 | ~spl10_5 | ~spl10_6)),
% 1.30/0.54    inference(subsumption_resolution,[],[f79,f49])).
% 1.30/0.54  fof(f49,plain,(
% 1.30/0.54    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) ) | ~spl10_3),
% 1.30/0.54    inference(avatar_component_clause,[],[f48])).
% 1.30/0.54  fof(f79,plain,(
% 1.30/0.54    ( ! [X0,X1] : (~r2_hidden(X1,k1_xboole_0) | ~r1_xboole_0(X0,k1_xboole_0)) ) | (~spl10_5 | ~spl10_6)),
% 1.30/0.54    inference(superposition,[],[f61,f57])).
% 1.30/0.54  fof(f57,plain,(
% 1.30/0.54    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) ) | ~spl10_5),
% 1.30/0.54    inference(avatar_component_clause,[],[f56])).
% 1.30/0.54  fof(f61,plain,(
% 1.30/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) ) | ~spl10_6),
% 1.30/0.54    inference(avatar_component_clause,[],[f60])).
% 1.30/0.54  fof(f62,plain,(
% 1.30/0.54    spl10_6),
% 1.30/0.54    inference(avatar_split_clause,[],[f17,f60])).
% 1.30/0.54  % (19221)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 1.30/0.54  fof(f17,plain,(
% 1.30/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f12])).
% 1.30/0.54  fof(f12,plain,(
% 1.30/0.54    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.30/0.54    inference(ennf_transformation,[],[f10])).
% 1.30/0.54  fof(f10,plain,(
% 1.30/0.54    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.30/0.54    inference(rectify,[],[f1])).
% 1.30/0.54  fof(f1,axiom,(
% 1.30/0.54    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.30/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.30/0.54  fof(f58,plain,(
% 1.30/0.54    spl10_5),
% 1.30/0.54    inference(avatar_split_clause,[],[f16,f56])).
% 1.30/0.54  fof(f16,plain,(
% 1.30/0.54    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f2])).
% 1.30/0.54  fof(f2,axiom,(
% 1.30/0.54    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.30/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 1.30/0.54  fof(f50,plain,(
% 1.30/0.54    spl10_3),
% 1.30/0.54    inference(avatar_split_clause,[],[f15,f48])).
% 1.30/0.54  fof(f15,plain,(
% 1.30/0.54    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f3])).
% 1.30/0.54  fof(f3,axiom,(
% 1.30/0.54    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.30/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 1.30/0.54  fof(f46,plain,(
% 1.30/0.54    ~spl10_1 | ~spl10_2),
% 1.30/0.54    inference(avatar_split_clause,[],[f13,f44,f41])).
% 1.30/0.54  fof(f13,plain,(
% 1.30/0.54    k1_xboole_0 != k1_relat_1(k1_xboole_0) | k1_xboole_0 != k2_relat_1(k1_xboole_0)),
% 1.30/0.54    inference(cnf_transformation,[],[f11])).
% 1.30/0.54  fof(f11,plain,(
% 1.30/0.54    k1_xboole_0 != k2_relat_1(k1_xboole_0) | k1_xboole_0 != k1_relat_1(k1_xboole_0)),
% 1.30/0.54    inference(ennf_transformation,[],[f9])).
% 1.30/0.54  fof(f9,negated_conjecture,(
% 1.30/0.54    ~(k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0))),
% 1.30/0.54    inference(negated_conjecture,[],[f8])).
% 1.30/0.54  fof(f8,conjecture,(
% 1.30/0.54    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.30/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 1.30/0.54  % SZS output end Proof for theBenchmark
% 1.30/0.54  % (19230)------------------------------
% 1.30/0.54  % (19230)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.54  % (19230)Termination reason: Refutation
% 1.30/0.54  
% 1.30/0.54  % (19230)Memory used [KB]: 10746
% 1.30/0.54  % (19230)Time elapsed: 0.094 s
% 1.30/0.54  % (19230)------------------------------
% 1.30/0.54  % (19230)------------------------------
% 1.30/0.54  % (19221)Refutation not found, incomplete strategy% (19221)------------------------------
% 1.30/0.54  % (19221)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.54  % (19221)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.54  
% 1.30/0.54  % (19221)Memory used [KB]: 6140
% 1.30/0.54  % (19221)Time elapsed: 0.103 s
% 1.30/0.54  % (19221)------------------------------
% 1.30/0.54  % (19221)------------------------------
% 1.30/0.54  % (19220)Success in time 0.168 s
%------------------------------------------------------------------------------
