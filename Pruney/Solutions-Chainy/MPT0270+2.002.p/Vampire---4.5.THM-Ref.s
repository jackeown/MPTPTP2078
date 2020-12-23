%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:40:56 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.36s
% Verified   : 
% Statistics : Number of formulae       :   38 (  50 expanded)
%              Number of leaves         :    8 (  17 expanded)
%              Depth                    :    7
%              Number of atoms          :   74 (  98 expanded)
%              Number of equality atoms :   15 (  21 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f112,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f75,f88,f97,f111])).

fof(f111,plain,
    ( ~ spl6_2
    | ~ spl6_3 ),
    inference(avatar_contradiction_clause,[],[f110])).

fof(f110,plain,
    ( $false
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f106,f86])).

fof(f86,plain,
    ( r1_xboole_0(k1_tarski(sK0),sK1)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl6_3
  <=> r1_xboole_0(k1_tarski(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f106,plain,
    ( ~ r1_xboole_0(k1_tarski(sK0),sK1)
    | ~ spl6_2 ),
    inference(superposition,[],[f100,f33])).

fof(f33,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f100,plain,
    ( ! [X0] : ~ r1_xboole_0(k2_tarski(sK0,X0),sK1)
    | ~ spl6_2 ),
    inference(resolution,[],[f68,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ~ ( r2_hidden(X0,X2)
        & r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).

fof(f68,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl6_2
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f97,plain,(
    spl6_3 ),
    inference(avatar_contradiction_clause,[],[f96])).

fof(f96,plain,
    ( $false
    | spl6_3 ),
    inference(global_subsumption,[],[f29,f90,f89])).

fof(f89,plain,
    ( r2_hidden(sK0,sK1)
    | spl6_3 ),
    inference(resolution,[],[f87,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f87,plain,
    ( ~ r1_xboole_0(k1_tarski(sK0),sK1)
    | spl6_3 ),
    inference(avatar_component_clause,[],[f85])).

fof(f90,plain,
    ( k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1)
    | spl6_3 ),
    inference(resolution,[],[f87,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f29,plain,
    ( ~ r2_hidden(sK0,sK1)
    | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
    <~> ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
      <=> ~ r2_hidden(X0,X1) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
    <=> ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_zfmisc_1)).

fof(f88,plain,
    ( ~ spl6_3
    | spl6_1 ),
    inference(avatar_split_clause,[],[f80,f63,f85])).

fof(f63,plain,
    ( spl6_1
  <=> k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f80,plain,
    ( ~ r1_xboole_0(k1_tarski(sK0),sK1)
    | spl6_1 ),
    inference(trivial_inequality_removal,[],[f79])).

fof(f79,plain,
    ( k1_tarski(sK0) != k1_tarski(sK0)
    | ~ r1_xboole_0(k1_tarski(sK0),sK1)
    | spl6_1 ),
    inference(superposition,[],[f64,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f64,plain,
    ( k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f63])).

fof(f75,plain,
    ( ~ spl6_1
    | spl6_2 ),
    inference(avatar_split_clause,[],[f71,f67,f63])).

fof(f71,plain,
    ( k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1)
    | spl6_2 ),
    inference(subsumption_resolution,[],[f30,f69])).

fof(f69,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl6_2 ),
    inference(avatar_component_clause,[],[f67])).

fof(f30,plain,
    ( r2_hidden(sK0,sK1)
    | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:09:44 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.22/0.50  % (14365)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.50  % (14362)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.51  % (14379)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.51  % (14371)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.51  % (14379)Refutation not found, incomplete strategy% (14379)------------------------------
% 0.22/0.51  % (14379)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (14361)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.51  % (14379)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (14379)Memory used [KB]: 10746
% 0.22/0.51  % (14379)Time elapsed: 0.069 s
% 0.22/0.51  % (14379)------------------------------
% 0.22/0.51  % (14379)------------------------------
% 0.22/0.51  % (14359)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.51  % (14374)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.51  % (14363)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.52  % (14358)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.52  % (14366)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.52  % (14370)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.52  % (14360)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.52  % (14377)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.53  % (14385)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.53  % (14364)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.53  % (14384)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.53  % (14367)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.53  % (14367)Refutation not found, incomplete strategy% (14367)------------------------------
% 0.22/0.53  % (14367)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (14367)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (14367)Memory used [KB]: 10618
% 0.22/0.53  % (14367)Time elapsed: 0.113 s
% 0.22/0.53  % (14367)------------------------------
% 0.22/0.53  % (14367)------------------------------
% 0.22/0.53  % (14369)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (14377)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % (14386)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.36/0.53  % (14365)Refutation not found, incomplete strategy% (14365)------------------------------
% 1.36/0.53  % (14365)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.53  % (14365)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.53  
% 1.36/0.53  % (14365)Memory used [KB]: 10618
% 1.36/0.53  % (14365)Time elapsed: 0.124 s
% 1.36/0.53  % (14365)------------------------------
% 1.36/0.53  % (14365)------------------------------
% 1.36/0.54  % (14373)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.36/0.54  % (14359)Refutation not found, incomplete strategy% (14359)------------------------------
% 1.36/0.54  % (14359)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.54  % (14374)Refutation not found, incomplete strategy% (14374)------------------------------
% 1.36/0.54  % (14374)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.54  % (14382)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.36/0.54  % (14378)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.36/0.54  % (14376)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.36/0.54  % (14357)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.36/0.54  % (14374)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.54  
% 1.36/0.54  % (14374)Memory used [KB]: 10618
% 1.36/0.54  % (14374)Time elapsed: 0.130 s
% 1.36/0.54  % (14374)------------------------------
% 1.36/0.54  % (14374)------------------------------
% 1.36/0.54  % (14359)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.54  
% 1.36/0.54  % (14359)Memory used [KB]: 10618
% 1.36/0.54  % (14359)Time elapsed: 0.125 s
% 1.36/0.54  % (14359)------------------------------
% 1.36/0.54  % (14359)------------------------------
% 1.36/0.54  % (14383)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.36/0.54  % (14368)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.36/0.54  % (14381)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.36/0.54  % (14368)Refutation not found, incomplete strategy% (14368)------------------------------
% 1.36/0.54  % (14368)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.55  % (14375)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.36/0.55  % SZS output start Proof for theBenchmark
% 1.36/0.55  fof(f112,plain,(
% 1.36/0.55    $false),
% 1.36/0.55    inference(avatar_sat_refutation,[],[f75,f88,f97,f111])).
% 1.36/0.55  fof(f111,plain,(
% 1.36/0.55    ~spl6_2 | ~spl6_3),
% 1.36/0.55    inference(avatar_contradiction_clause,[],[f110])).
% 1.36/0.55  fof(f110,plain,(
% 1.36/0.55    $false | (~spl6_2 | ~spl6_3)),
% 1.36/0.55    inference(subsumption_resolution,[],[f106,f86])).
% 1.36/0.55  fof(f86,plain,(
% 1.36/0.55    r1_xboole_0(k1_tarski(sK0),sK1) | ~spl6_3),
% 1.36/0.55    inference(avatar_component_clause,[],[f85])).
% 1.36/0.55  fof(f85,plain,(
% 1.36/0.55    spl6_3 <=> r1_xboole_0(k1_tarski(sK0),sK1)),
% 1.36/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 1.36/0.55  fof(f106,plain,(
% 1.36/0.55    ~r1_xboole_0(k1_tarski(sK0),sK1) | ~spl6_2),
% 1.36/0.55    inference(superposition,[],[f100,f33])).
% 1.36/0.55  fof(f33,plain,(
% 1.36/0.55    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.36/0.55    inference(cnf_transformation,[],[f13])).
% 1.36/0.55  fof(f13,axiom,(
% 1.36/0.55    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.36/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.36/0.55  fof(f100,plain,(
% 1.36/0.55    ( ! [X0] : (~r1_xboole_0(k2_tarski(sK0,X0),sK1)) ) | ~spl6_2),
% 1.36/0.55    inference(resolution,[],[f68,f58])).
% 1.36/0.55  fof(f58,plain,(
% 1.36/0.55    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k2_tarski(X0,X1),X2)) )),
% 1.36/0.55    inference(cnf_transformation,[],[f28])).
% 1.36/0.55  fof(f28,plain,(
% 1.36/0.55    ! [X0,X1,X2] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k2_tarski(X0,X1),X2))),
% 1.36/0.55    inference(ennf_transformation,[],[f18])).
% 1.36/0.55  fof(f18,axiom,(
% 1.36/0.55    ! [X0,X1,X2] : ~(r2_hidden(X0,X2) & r1_xboole_0(k2_tarski(X0,X1),X2))),
% 1.36/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).
% 1.36/0.55  fof(f68,plain,(
% 1.36/0.55    r2_hidden(sK0,sK1) | ~spl6_2),
% 1.36/0.55    inference(avatar_component_clause,[],[f67])).
% 1.36/0.55  fof(f67,plain,(
% 1.36/0.55    spl6_2 <=> r2_hidden(sK0,sK1)),
% 1.36/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.36/0.55  fof(f97,plain,(
% 1.36/0.55    spl6_3),
% 1.36/0.55    inference(avatar_contradiction_clause,[],[f96])).
% 1.36/0.55  fof(f96,plain,(
% 1.36/0.55    $false | spl6_3),
% 1.36/0.55    inference(global_subsumption,[],[f29,f90,f89])).
% 1.36/0.55  fof(f89,plain,(
% 1.36/0.55    r2_hidden(sK0,sK1) | spl6_3),
% 1.36/0.55    inference(resolution,[],[f87,f42])).
% 1.36/0.55  fof(f42,plain,(
% 1.36/0.55    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 1.36/0.55    inference(cnf_transformation,[],[f25])).
% 1.36/0.55  fof(f25,plain,(
% 1.36/0.55    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 1.36/0.55    inference(ennf_transformation,[],[f17])).
% 1.36/0.55  fof(f17,axiom,(
% 1.36/0.55    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 1.36/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 1.36/0.55  fof(f87,plain,(
% 1.36/0.55    ~r1_xboole_0(k1_tarski(sK0),sK1) | spl6_3),
% 1.36/0.55    inference(avatar_component_clause,[],[f85])).
% 1.36/0.55  fof(f90,plain,(
% 1.36/0.55    k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1) | spl6_3),
% 1.36/0.55    inference(resolution,[],[f87,f44])).
% 1.36/0.55  fof(f44,plain,(
% 1.36/0.55    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 1.36/0.55    inference(cnf_transformation,[],[f11])).
% 1.36/0.55  fof(f11,axiom,(
% 1.36/0.55    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 1.36/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 1.36/0.55  fof(f29,plain,(
% 1.36/0.55    ~r2_hidden(sK0,sK1) | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1)),
% 1.36/0.55    inference(cnf_transformation,[],[f22])).
% 1.36/0.55  fof(f22,plain,(
% 1.36/0.55    ? [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) <~> ~r2_hidden(X0,X1))),
% 1.36/0.55    inference(ennf_transformation,[],[f20])).
% 1.36/0.55  fof(f20,negated_conjecture,(
% 1.36/0.55    ~! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) <=> ~r2_hidden(X0,X1))),
% 1.36/0.55    inference(negated_conjecture,[],[f19])).
% 1.36/0.55  fof(f19,conjecture,(
% 1.36/0.55    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) <=> ~r2_hidden(X0,X1))),
% 1.36/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_zfmisc_1)).
% 1.36/0.55  fof(f88,plain,(
% 1.36/0.55    ~spl6_3 | spl6_1),
% 1.36/0.55    inference(avatar_split_clause,[],[f80,f63,f85])).
% 1.36/0.55  fof(f63,plain,(
% 1.36/0.55    spl6_1 <=> k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1)),
% 1.36/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.36/0.55  fof(f80,plain,(
% 1.36/0.55    ~r1_xboole_0(k1_tarski(sK0),sK1) | spl6_1),
% 1.36/0.55    inference(trivial_inequality_removal,[],[f79])).
% 1.36/0.55  fof(f79,plain,(
% 1.36/0.55    k1_tarski(sK0) != k1_tarski(sK0) | ~r1_xboole_0(k1_tarski(sK0),sK1) | spl6_1),
% 1.36/0.55    inference(superposition,[],[f64,f45])).
% 1.36/0.55  fof(f45,plain,(
% 1.36/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 1.36/0.55    inference(cnf_transformation,[],[f11])).
% 1.36/0.55  fof(f64,plain,(
% 1.36/0.55    k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1) | spl6_1),
% 1.36/0.55    inference(avatar_component_clause,[],[f63])).
% 1.36/0.55  fof(f75,plain,(
% 1.36/0.55    ~spl6_1 | spl6_2),
% 1.36/0.55    inference(avatar_split_clause,[],[f71,f67,f63])).
% 1.36/0.55  fof(f71,plain,(
% 1.36/0.55    k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1) | spl6_2),
% 1.36/0.55    inference(subsumption_resolution,[],[f30,f69])).
% 1.36/0.55  fof(f69,plain,(
% 1.36/0.55    ~r2_hidden(sK0,sK1) | spl6_2),
% 1.36/0.55    inference(avatar_component_clause,[],[f67])).
% 1.36/0.55  fof(f30,plain,(
% 1.36/0.55    r2_hidden(sK0,sK1) | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1)),
% 1.36/0.55    inference(cnf_transformation,[],[f22])).
% 1.36/0.55  % SZS output end Proof for theBenchmark
% 1.36/0.55  % (14377)------------------------------
% 1.36/0.55  % (14377)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.55  % (14377)Termination reason: Refutation
% 1.36/0.55  
% 1.36/0.55  % (14377)Memory used [KB]: 10746
% 1.36/0.55  % (14377)Time elapsed: 0.129 s
% 1.36/0.55  % (14377)------------------------------
% 1.36/0.55  % (14377)------------------------------
% 1.36/0.55  % (14356)Success in time 0.188 s
%------------------------------------------------------------------------------
