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
% DateTime   : Thu Dec  3 12:40:45 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   63 (  97 expanded)
%              Number of leaves         :   15 (  44 expanded)
%              Depth                    :    6
%              Number of atoms          :  173 ( 263 expanded)
%              Number of equality atoms :   28 (  48 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f166,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f30,f33,f37,f41,f49,f72,f76,f94,f98,f113,f143,f155,f165])).

fof(f165,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_contradiction_clause,[],[f164])).

fof(f164,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f159,f32])).

fof(f32,plain,
    ( r2_hidden(sK1,sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f28])).

fof(f28,plain,
    ( spl3_2
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f159,plain,
    ( ~ r2_hidden(sK1,sK0)
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(superposition,[],[f36,f26])).

fof(f26,plain,
    ( sK0 = k4_xboole_0(sK0,k1_tarski(sK1))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f25])).

fof(f25,plain,
    ( spl3_1
  <=> sK0 = k4_xboole_0(sK0,k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f36,plain,
    ( ! [X2,X1] : ~ r2_hidden(X2,k4_xboole_0(X1,k1_tarski(X2)))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f35])).

fof(f35,plain,
    ( spl3_3
  <=> ! [X1,X2] : ~ r2_hidden(X2,k4_xboole_0(X1,k1_tarski(X2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f155,plain,
    ( spl3_2
    | ~ spl3_12
    | ~ spl3_17
    | ~ spl3_19 ),
    inference(avatar_contradiction_clause,[],[f148])).

fof(f148,plain,
    ( $false
    | spl3_2
    | ~ spl3_12
    | ~ spl3_17
    | ~ spl3_19 ),
    inference(unit_resulting_resolution,[],[f29,f112,f142,f75])).

fof(f75,plain,
    ( ! [X6,X7,X5] :
        ( ~ r2_hidden(X7,k1_tarski(X5))
        | ~ r2_hidden(X7,X6)
        | r2_hidden(X5,X6) )
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl3_12
  <=> ! [X5,X7,X6] :
        ( ~ r2_hidden(X7,k1_tarski(X5))
        | ~ r2_hidden(X7,X6)
        | r2_hidden(X5,X6) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f142,plain,
    ( r2_hidden(sK2(sK0,k1_tarski(sK1),sK0),k1_tarski(sK1))
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f141])).

fof(f141,plain,
    ( spl3_19
  <=> r2_hidden(sK2(sK0,k1_tarski(sK1),sK0),k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f112,plain,
    ( r2_hidden(sK2(sK0,k1_tarski(sK1),sK0),sK0)
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl3_17
  <=> r2_hidden(sK2(sK0,k1_tarski(sK1),sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f29,plain,
    ( ~ r2_hidden(sK1,sK0)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f28])).

fof(f143,plain,
    ( spl3_19
    | spl3_1
    | ~ spl3_15
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f131,f111,f96,f25,f141])).

fof(f96,plain,
    ( spl3_15
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(sK2(X0,X1,X2),X0)
        | r2_hidden(sK2(X0,X1,X2),X1)
        | ~ r2_hidden(sK2(X0,X1,X2),X2)
        | k4_xboole_0(X0,X1) = X2 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f131,plain,
    ( r2_hidden(sK2(sK0,k1_tarski(sK1),sK0),k1_tarski(sK1))
    | spl3_1
    | ~ spl3_15
    | ~ spl3_17 ),
    inference(subsumption_resolution,[],[f130,f31])).

fof(f31,plain,
    ( sK0 != k4_xboole_0(sK0,k1_tarski(sK1))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f25])).

fof(f130,plain,
    ( r2_hidden(sK2(sK0,k1_tarski(sK1),sK0),k1_tarski(sK1))
    | sK0 = k4_xboole_0(sK0,k1_tarski(sK1))
    | ~ spl3_15
    | ~ spl3_17 ),
    inference(subsumption_resolution,[],[f126,f112])).

fof(f126,plain,
    ( r2_hidden(sK2(sK0,k1_tarski(sK1),sK0),k1_tarski(sK1))
    | ~ r2_hidden(sK2(sK0,k1_tarski(sK1),sK0),sK0)
    | sK0 = k4_xboole_0(sK0,k1_tarski(sK1))
    | ~ spl3_15
    | ~ spl3_17 ),
    inference(resolution,[],[f112,f97])).

fof(f97,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(sK2(X0,X1,X2),X2)
        | r2_hidden(sK2(X0,X1,X2),X1)
        | ~ r2_hidden(sK2(X0,X1,X2),X0)
        | k4_xboole_0(X0,X1) = X2 )
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f96])).

fof(f113,plain,
    ( spl3_17
    | spl3_1
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f103,f92,f25,f111])).

fof(f92,plain,
    ( spl3_14
  <=> ! [X1,X0] :
        ( r2_hidden(sK2(X0,X1,X0),X0)
        | k4_xboole_0(X0,X1) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f103,plain,
    ( r2_hidden(sK2(sK0,k1_tarski(sK1),sK0),sK0)
    | spl3_1
    | ~ spl3_14 ),
    inference(trivial_inequality_removal,[],[f99])).

fof(f99,plain,
    ( sK0 != sK0
    | r2_hidden(sK2(sK0,k1_tarski(sK1),sK0),sK0)
    | spl3_1
    | ~ spl3_14 ),
    inference(superposition,[],[f31,f93])).

fof(f93,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(X0,X1) = X0
        | r2_hidden(sK2(X0,X1,X0),X0) )
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f92])).

fof(f98,plain,(
    spl3_15 ),
    inference(avatar_split_clause,[],[f11,f96])).

fof(f11,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X1)
      | ~ r2_hidden(sK2(X0,X1,X2),X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f94,plain,
    ( spl3_14
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f88,f70,f92])).

fof(f70,plain,
    ( spl3_11
  <=> ! [X1,X0,X2] :
        ( r2_hidden(sK2(X0,X1,X2),X0)
        | r2_hidden(sK2(X0,X1,X2),X2)
        | k4_xboole_0(X0,X1) = X2 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f88,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK2(X0,X1,X0),X0)
        | k4_xboole_0(X0,X1) = X0 )
    | ~ spl3_11 ),
    inference(factoring,[],[f71])).

fof(f71,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(sK2(X0,X1,X2),X2)
        | r2_hidden(sK2(X0,X1,X2),X0)
        | k4_xboole_0(X0,X1) = X2 )
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f70])).

fof(f76,plain,
    ( spl3_12
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f60,f47,f39,f74])).

fof(f39,plain,
    ( spl3_4
  <=> ! [X1,X3,X0] :
        ( ~ r2_hidden(X3,X1)
        | ~ r2_hidden(X3,k4_xboole_0(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f47,plain,
    ( spl3_6
  <=> ! [X1,X0] :
        ( r2_hidden(X0,X1)
        | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f60,plain,
    ( ! [X6,X7,X5] :
        ( ~ r2_hidden(X7,k1_tarski(X5))
        | ~ r2_hidden(X7,X6)
        | r2_hidden(X5,X6) )
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(superposition,[],[f40,f48])).

fof(f48,plain,
    ( ! [X0,X1] :
        ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
        | r2_hidden(X0,X1) )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f47])).

fof(f40,plain,
    ( ! [X0,X3,X1] :
        ( ~ r2_hidden(X3,k4_xboole_0(X0,X1))
        | ~ r2_hidden(X3,X1) )
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f39])).

fof(f72,plain,(
    spl3_11 ),
    inference(avatar_split_clause,[],[f12,f70])).

fof(f12,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f49,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f9,f47])).

fof(f9,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
    <=> ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l33_zfmisc_1)).

fof(f41,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f21,f39])).

fof(f21,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f15])).

fof(f15,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f37,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f23,f35])).

fof(f23,plain,(
    ! [X2,X1] : ~ r2_hidden(X2,k4_xboole_0(X1,k1_tarski(X2))) ),
    inference(equality_resolution,[],[f18])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(f33,plain,
    ( ~ spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f8,f28,f25])).

fof(f8,plain,
    ( r2_hidden(sK1,sK0)
    | sK0 != k4_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <~> ~ r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      <=> ~ r2_hidden(X1,X0) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f30,plain,
    ( spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f7,f28,f25])).

fof(f7,plain,
    ( ~ r2_hidden(sK1,sK0)
    | sK0 = k4_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f6])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:53:49 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.49  % (14187)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.49  % (14186)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.50  % (14185)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.50  % (14188)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.50  % (14193)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.51  % (14195)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.51  % (14194)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.52  % (14196)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.52  % (14189)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.52  % (14181)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (14181)Refutation not found, incomplete strategy% (14181)------------------------------
% 0.21/0.53  % (14181)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (14181)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (14181)Memory used [KB]: 10490
% 0.21/0.53  % (14181)Time elapsed: 0.062 s
% 0.21/0.53  % (14181)------------------------------
% 0.21/0.53  % (14181)------------------------------
% 0.21/0.53  % (14182)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.53  % (14183)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.53  % (14189)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f166,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(avatar_sat_refutation,[],[f30,f33,f37,f41,f49,f72,f76,f94,f98,f113,f143,f155,f165])).
% 0.21/0.53  fof(f165,plain,(
% 0.21/0.53    ~spl3_1 | ~spl3_2 | ~spl3_3),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f164])).
% 0.21/0.53  fof(f164,plain,(
% 0.21/0.53    $false | (~spl3_1 | ~spl3_2 | ~spl3_3)),
% 0.21/0.53    inference(subsumption_resolution,[],[f159,f32])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    r2_hidden(sK1,sK0) | ~spl3_2),
% 0.21/0.53    inference(avatar_component_clause,[],[f28])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    spl3_2 <=> r2_hidden(sK1,sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.53  fof(f159,plain,(
% 0.21/0.53    ~r2_hidden(sK1,sK0) | (~spl3_1 | ~spl3_3)),
% 0.21/0.53    inference(superposition,[],[f36,f26])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    sK0 = k4_xboole_0(sK0,k1_tarski(sK1)) | ~spl3_1),
% 0.21/0.53    inference(avatar_component_clause,[],[f25])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    spl3_1 <=> sK0 = k4_xboole_0(sK0,k1_tarski(sK1))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    ( ! [X2,X1] : (~r2_hidden(X2,k4_xboole_0(X1,k1_tarski(X2)))) ) | ~spl3_3),
% 0.21/0.53    inference(avatar_component_clause,[],[f35])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    spl3_3 <=> ! [X1,X2] : ~r2_hidden(X2,k4_xboole_0(X1,k1_tarski(X2)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.53  fof(f155,plain,(
% 0.21/0.53    spl3_2 | ~spl3_12 | ~spl3_17 | ~spl3_19),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f148])).
% 0.21/0.53  fof(f148,plain,(
% 0.21/0.53    $false | (spl3_2 | ~spl3_12 | ~spl3_17 | ~spl3_19)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f29,f112,f142,f75])).
% 0.21/0.53  fof(f75,plain,(
% 0.21/0.53    ( ! [X6,X7,X5] : (~r2_hidden(X7,k1_tarski(X5)) | ~r2_hidden(X7,X6) | r2_hidden(X5,X6)) ) | ~spl3_12),
% 0.21/0.53    inference(avatar_component_clause,[],[f74])).
% 0.21/0.53  fof(f74,plain,(
% 0.21/0.53    spl3_12 <=> ! [X5,X7,X6] : (~r2_hidden(X7,k1_tarski(X5)) | ~r2_hidden(X7,X6) | r2_hidden(X5,X6))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.53  fof(f142,plain,(
% 0.21/0.53    r2_hidden(sK2(sK0,k1_tarski(sK1),sK0),k1_tarski(sK1)) | ~spl3_19),
% 0.21/0.53    inference(avatar_component_clause,[],[f141])).
% 0.21/0.53  fof(f141,plain,(
% 0.21/0.53    spl3_19 <=> r2_hidden(sK2(sK0,k1_tarski(sK1),sK0),k1_tarski(sK1))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.21/0.53  fof(f112,plain,(
% 0.21/0.53    r2_hidden(sK2(sK0,k1_tarski(sK1),sK0),sK0) | ~spl3_17),
% 0.21/0.53    inference(avatar_component_clause,[],[f111])).
% 0.21/0.53  fof(f111,plain,(
% 0.21/0.53    spl3_17 <=> r2_hidden(sK2(sK0,k1_tarski(sK1),sK0),sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ~r2_hidden(sK1,sK0) | spl3_2),
% 0.21/0.53    inference(avatar_component_clause,[],[f28])).
% 0.21/0.53  fof(f143,plain,(
% 0.21/0.53    spl3_19 | spl3_1 | ~spl3_15 | ~spl3_17),
% 0.21/0.53    inference(avatar_split_clause,[],[f131,f111,f96,f25,f141])).
% 0.21/0.53  fof(f96,plain,(
% 0.21/0.53    spl3_15 <=> ! [X1,X0,X2] : (~r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X2) | k4_xboole_0(X0,X1) = X2)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.21/0.53  fof(f131,plain,(
% 0.21/0.53    r2_hidden(sK2(sK0,k1_tarski(sK1),sK0),k1_tarski(sK1)) | (spl3_1 | ~spl3_15 | ~spl3_17)),
% 0.21/0.53    inference(subsumption_resolution,[],[f130,f31])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    sK0 != k4_xboole_0(sK0,k1_tarski(sK1)) | spl3_1),
% 0.21/0.53    inference(avatar_component_clause,[],[f25])).
% 0.21/0.53  fof(f130,plain,(
% 0.21/0.53    r2_hidden(sK2(sK0,k1_tarski(sK1),sK0),k1_tarski(sK1)) | sK0 = k4_xboole_0(sK0,k1_tarski(sK1)) | (~spl3_15 | ~spl3_17)),
% 0.21/0.53    inference(subsumption_resolution,[],[f126,f112])).
% 0.21/0.53  fof(f126,plain,(
% 0.21/0.53    r2_hidden(sK2(sK0,k1_tarski(sK1),sK0),k1_tarski(sK1)) | ~r2_hidden(sK2(sK0,k1_tarski(sK1),sK0),sK0) | sK0 = k4_xboole_0(sK0,k1_tarski(sK1)) | (~spl3_15 | ~spl3_17)),
% 0.21/0.53    inference(resolution,[],[f112,f97])).
% 0.21/0.53  fof(f97,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~r2_hidden(sK2(X0,X1,X2),X2) | r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | k4_xboole_0(X0,X1) = X2) ) | ~spl3_15),
% 0.21/0.53    inference(avatar_component_clause,[],[f96])).
% 0.21/0.53  fof(f113,plain,(
% 0.21/0.53    spl3_17 | spl3_1 | ~spl3_14),
% 0.21/0.53    inference(avatar_split_clause,[],[f103,f92,f25,f111])).
% 0.21/0.53  fof(f92,plain,(
% 0.21/0.53    spl3_14 <=> ! [X1,X0] : (r2_hidden(sK2(X0,X1,X0),X0) | k4_xboole_0(X0,X1) = X0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.21/0.53  fof(f103,plain,(
% 0.21/0.53    r2_hidden(sK2(sK0,k1_tarski(sK1),sK0),sK0) | (spl3_1 | ~spl3_14)),
% 0.21/0.53    inference(trivial_inequality_removal,[],[f99])).
% 0.21/0.53  fof(f99,plain,(
% 0.21/0.53    sK0 != sK0 | r2_hidden(sK2(sK0,k1_tarski(sK1),sK0),sK0) | (spl3_1 | ~spl3_14)),
% 0.21/0.53    inference(superposition,[],[f31,f93])).
% 0.21/0.53  fof(f93,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | r2_hidden(sK2(X0,X1,X0),X0)) ) | ~spl3_14),
% 0.21/0.53    inference(avatar_component_clause,[],[f92])).
% 0.21/0.53  fof(f98,plain,(
% 0.21/0.53    spl3_15),
% 0.21/0.53    inference(avatar_split_clause,[],[f11,f96])).
% 0.21/0.53  fof(f11,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X2) | k4_xboole_0(X0,X1) = X2) )),
% 0.21/0.53    inference(cnf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.21/0.53  fof(f94,plain,(
% 0.21/0.53    spl3_14 | ~spl3_11),
% 0.21/0.53    inference(avatar_split_clause,[],[f88,f70,f92])).
% 0.21/0.53  fof(f70,plain,(
% 0.21/0.53    spl3_11 <=> ! [X1,X0,X2] : (r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2) | k4_xboole_0(X0,X1) = X2)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.53  fof(f88,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1,X0),X0) | k4_xboole_0(X0,X1) = X0) ) | ~spl3_11),
% 0.21/0.53    inference(factoring,[],[f71])).
% 0.21/0.53  fof(f71,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,X1,X2),X2) | r2_hidden(sK2(X0,X1,X2),X0) | k4_xboole_0(X0,X1) = X2) ) | ~spl3_11),
% 0.21/0.53    inference(avatar_component_clause,[],[f70])).
% 0.21/0.53  fof(f76,plain,(
% 0.21/0.53    spl3_12 | ~spl3_4 | ~spl3_6),
% 0.21/0.53    inference(avatar_split_clause,[],[f60,f47,f39,f74])).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    spl3_4 <=> ! [X1,X3,X0] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,k4_xboole_0(X0,X1)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.53  fof(f47,plain,(
% 0.21/0.53    spl3_6 <=> ! [X1,X0] : (r2_hidden(X0,X1) | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.53  fof(f60,plain,(
% 0.21/0.53    ( ! [X6,X7,X5] : (~r2_hidden(X7,k1_tarski(X5)) | ~r2_hidden(X7,X6) | r2_hidden(X5,X6)) ) | (~spl3_4 | ~spl3_6)),
% 0.21/0.53    inference(superposition,[],[f40,f48])).
% 0.21/0.53  fof(f48,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) ) | ~spl3_6),
% 0.21/0.53    inference(avatar_component_clause,[],[f47])).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    ( ! [X0,X3,X1] : (~r2_hidden(X3,k4_xboole_0(X0,X1)) | ~r2_hidden(X3,X1)) ) | ~spl3_4),
% 0.21/0.53    inference(avatar_component_clause,[],[f39])).
% 0.21/0.53  fof(f72,plain,(
% 0.21/0.53    spl3_11),
% 0.21/0.53    inference(avatar_split_clause,[],[f12,f70])).
% 0.21/0.53  fof(f12,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2) | k4_xboole_0(X0,X1) = X2) )),
% 0.21/0.53    inference(cnf_transformation,[],[f1])).
% 0.21/0.53  fof(f49,plain,(
% 0.21/0.53    spl3_6),
% 0.21/0.53    inference(avatar_split_clause,[],[f9,f47])).
% 0.21/0.53  fof(f9,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r2_hidden(X0,X1) | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) <=> ~r2_hidden(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l33_zfmisc_1)).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    spl3_4),
% 0.21/0.53    inference(avatar_split_clause,[],[f21,f39])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ( ! [X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,k4_xboole_0(X0,X1))) )),
% 0.21/0.53    inference(equality_resolution,[],[f15])).
% 0.21/0.53  fof(f15,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.21/0.53    inference(cnf_transformation,[],[f1])).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    spl3_3),
% 0.21/0.53    inference(avatar_split_clause,[],[f23,f35])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ( ! [X2,X1] : (~r2_hidden(X2,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 0.21/0.53    inference(equality_resolution,[],[f18])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    ~spl3_1 | spl3_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f8,f28,f25])).
% 0.21/0.53  fof(f8,plain,(
% 0.21/0.53    r2_hidden(sK1,sK0) | sK0 != k4_xboole_0(sK0,k1_tarski(sK1))),
% 0.21/0.53    inference(cnf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,plain,(
% 0.21/0.53    ? [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <~> ~r2_hidden(X1,X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,negated_conjecture,(
% 0.21/0.53    ~! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 0.21/0.53    inference(negated_conjecture,[],[f4])).
% 0.21/0.53  fof(f4,conjecture,(
% 0.21/0.53    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    spl3_1 | ~spl3_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f7,f28,f25])).
% 0.21/0.53  fof(f7,plain,(
% 0.21/0.53    ~r2_hidden(sK1,sK0) | sK0 = k4_xboole_0(sK0,k1_tarski(sK1))),
% 0.21/0.53    inference(cnf_transformation,[],[f6])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (14189)------------------------------
% 0.21/0.53  % (14189)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (14189)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (14189)Memory used [KB]: 10618
% 0.21/0.53  % (14189)Time elapsed: 0.065 s
% 0.21/0.53  % (14189)------------------------------
% 0.21/0.53  % (14189)------------------------------
% 0.21/0.53  % (14198)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.53  % (14179)Success in time 0.174 s
%------------------------------------------------------------------------------
