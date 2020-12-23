%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:38:27 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   71 (  99 expanded)
%              Number of leaves         :   21 (  46 expanded)
%              Depth                    :    6
%              Number of atoms          :  156 ( 220 expanded)
%              Number of equality atoms :   16 (  23 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f354,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f50,f55,f59,f63,f67,f79,f83,f87,f135,f190,f200,f220,f281,f353])).

fof(f353,plain,
    ( spl2_24
    | ~ spl2_27
    | ~ spl2_33 ),
    inference(avatar_contradiction_clause,[],[f352])).

fof(f352,plain,
    ( $false
    | spl2_24
    | ~ spl2_27
    | ~ spl2_33 ),
    inference(subsumption_resolution,[],[f199,f347])).

fof(f347,plain,
    ( r1_tarski(k1_tarski(sK0),sK1)
    | ~ spl2_27
    | ~ spl2_33 ),
    inference(superposition,[],[f280,f219])).

fof(f219,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0
    | ~ spl2_27 ),
    inference(avatar_component_clause,[],[f218])).

fof(f218,plain,
    ( spl2_27
  <=> ! [X1,X0] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).

fof(f280,plain,
    ( ! [X1] : r1_tarski(k3_xboole_0(X1,k2_xboole_0(k1_tarski(sK0),sK1)),sK1)
    | ~ spl2_33 ),
    inference(avatar_component_clause,[],[f279])).

fof(f279,plain,
    ( spl2_33
  <=> ! [X1] : r1_tarski(k3_xboole_0(X1,k2_xboole_0(k1_tarski(sK0),sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_33])])).

fof(f199,plain,
    ( ~ r1_tarski(k1_tarski(sK0),sK1)
    | spl2_24 ),
    inference(avatar_component_clause,[],[f197])).

fof(f197,plain,
    ( spl2_24
  <=> r1_tarski(k1_tarski(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).

fof(f281,plain,
    ( spl2_33
    | ~ spl2_5
    | ~ spl2_23 ),
    inference(avatar_split_clause,[],[f194,f188,f65,f279])).

fof(f65,plain,
    ( spl2_5
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f188,plain,
    ( spl2_23
  <=> ! [X0] : r1_tarski(k3_xboole_0(k2_xboole_0(k1_tarski(sK0),sK1),X0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).

fof(f194,plain,
    ( ! [X1] : r1_tarski(k3_xboole_0(X1,k2_xboole_0(k1_tarski(sK0),sK1)),sK1)
    | ~ spl2_5
    | ~ spl2_23 ),
    inference(superposition,[],[f189,f66])).

fof(f66,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f65])).

fof(f189,plain,
    ( ! [X0] : r1_tarski(k3_xboole_0(k2_xboole_0(k1_tarski(sK0),sK1),X0),sK1)
    | ~ spl2_23 ),
    inference(avatar_component_clause,[],[f188])).

fof(f220,plain,
    ( spl2_27
    | ~ spl2_3
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f98,f77,f57,f218])).

fof(f57,plain,
    ( spl2_3
  <=> ! [X1,X0] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f77,plain,
    ( spl2_8
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f98,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0
    | ~ spl2_3
    | ~ spl2_8 ),
    inference(unit_resulting_resolution,[],[f58,f78])).

fof(f78,plain,
    ( ! [X0,X1] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r1_tarski(X0,X1) )
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f77])).

fof(f58,plain,
    ( ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f57])).

fof(f200,plain,
    ( ~ spl2_24
    | ~ spl2_4
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f161,f133,f61,f197])).

fof(f61,plain,
    ( spl2_4
  <=> ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f133,plain,
    ( spl2_16
  <=> ! [X0] : ~ r1_tarski(k2_tarski(sK0,X0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f161,plain,
    ( ~ r1_tarski(k1_tarski(sK0),sK1)
    | ~ spl2_4
    | ~ spl2_16 ),
    inference(superposition,[],[f134,f62])).

fof(f62,plain,
    ( ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f61])).

fof(f134,plain,
    ( ! [X0] : ~ r1_tarski(k2_tarski(sK0,X0),sK1)
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f133])).

fof(f190,plain,
    ( spl2_23
    | ~ spl2_2
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f103,f81,f52,f188])).

fof(f52,plain,
    ( spl2_2
  <=> r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f81,plain,
    ( spl2_9
  <=> ! [X1,X0,X2] :
        ( r1_tarski(k3_xboole_0(X0,X2),X1)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f103,plain,
    ( ! [X0] : r1_tarski(k3_xboole_0(k2_xboole_0(k1_tarski(sK0),sK1),X0),sK1)
    | ~ spl2_2
    | ~ spl2_9 ),
    inference(unit_resulting_resolution,[],[f54,f82])).

fof(f82,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(k3_xboole_0(X0,X2),X1)
        | ~ r1_tarski(X0,X1) )
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f81])).

fof(f54,plain,
    ( r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f52])).

fof(f135,plain,
    ( spl2_16
    | spl2_1
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f108,f85,f47,f133])).

fof(f47,plain,
    ( spl2_1
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f85,plain,
    ( spl2_10
  <=> ! [X1,X0,X2] :
        ( r2_hidden(X0,X2)
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f108,plain,
    ( ! [X0] : ~ r1_tarski(k2_tarski(sK0,X0),sK1)
    | spl2_1
    | ~ spl2_10 ),
    inference(unit_resulting_resolution,[],[f49,f86])).

fof(f86,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(k2_tarski(X0,X1),X2)
        | r2_hidden(X0,X2) )
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f85])).

fof(f49,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f47])).

fof(f87,plain,(
    spl2_10 ),
    inference(avatar_split_clause,[],[f37,f85])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f83,plain,(
    spl2_9 ),
    inference(avatar_split_clause,[],[f36,f81])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k3_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_xboole_1)).

fof(f79,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f33,f77])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f67,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f30,f65])).

fof(f30,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f63,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f28,f61])).

fof(f28,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f59,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f29,f57])).

fof(f29,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f55,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f26,f52])).

fof(f26,plain,(
    r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ~ r2_hidden(sK0,sK1)
    & r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f22])).

fof(f22,plain,
    ( ? [X0,X1] :
        ( ~ r2_hidden(X0,X1)
        & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) )
   => ( ~ r2_hidden(sK0,sK1)
      & r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1)
       => r2_hidden(X0,X1) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1)
     => r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_zfmisc_1)).

fof(f50,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f27,f47])).

fof(f27,plain,(
    ~ r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:40:45 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.48  % (22443)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.48  % (22431)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.48  % (22433)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.48  % (22438)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.49  % (22440)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.49  % (22436)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.49  % (22439)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.49  % (22444)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.49  % (22436)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % (22435)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.50  % (22437)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.50  % (22432)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.50  % (22448)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.50  % (22434)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.50  % (22445)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.50  % (22442)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.50  % (22442)Refutation not found, incomplete strategy% (22442)------------------------------
% 0.22/0.50  % (22442)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (22442)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (22442)Memory used [KB]: 10618
% 0.22/0.50  % (22442)Time elapsed: 0.085 s
% 0.22/0.50  % (22442)------------------------------
% 0.22/0.50  % (22442)------------------------------
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f354,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(avatar_sat_refutation,[],[f50,f55,f59,f63,f67,f79,f83,f87,f135,f190,f200,f220,f281,f353])).
% 0.22/0.51  fof(f353,plain,(
% 0.22/0.51    spl2_24 | ~spl2_27 | ~spl2_33),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f352])).
% 0.22/0.51  fof(f352,plain,(
% 0.22/0.51    $false | (spl2_24 | ~spl2_27 | ~spl2_33)),
% 0.22/0.51    inference(subsumption_resolution,[],[f199,f347])).
% 0.22/0.51  fof(f347,plain,(
% 0.22/0.51    r1_tarski(k1_tarski(sK0),sK1) | (~spl2_27 | ~spl2_33)),
% 0.22/0.51    inference(superposition,[],[f280,f219])).
% 0.22/0.51  fof(f219,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) ) | ~spl2_27),
% 0.22/0.51    inference(avatar_component_clause,[],[f218])).
% 0.22/0.51  fof(f218,plain,(
% 0.22/0.51    spl2_27 <=> ! [X1,X0] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).
% 0.22/0.51  fof(f280,plain,(
% 0.22/0.51    ( ! [X1] : (r1_tarski(k3_xboole_0(X1,k2_xboole_0(k1_tarski(sK0),sK1)),sK1)) ) | ~spl2_33),
% 0.22/0.51    inference(avatar_component_clause,[],[f279])).
% 0.22/0.51  fof(f279,plain,(
% 0.22/0.51    spl2_33 <=> ! [X1] : r1_tarski(k3_xboole_0(X1,k2_xboole_0(k1_tarski(sK0),sK1)),sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_33])])).
% 0.22/0.51  fof(f199,plain,(
% 0.22/0.51    ~r1_tarski(k1_tarski(sK0),sK1) | spl2_24),
% 0.22/0.51    inference(avatar_component_clause,[],[f197])).
% 0.22/0.51  fof(f197,plain,(
% 0.22/0.51    spl2_24 <=> r1_tarski(k1_tarski(sK0),sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).
% 0.22/0.51  fof(f281,plain,(
% 0.22/0.51    spl2_33 | ~spl2_5 | ~spl2_23),
% 0.22/0.51    inference(avatar_split_clause,[],[f194,f188,f65,f279])).
% 0.22/0.51  fof(f65,plain,(
% 0.22/0.51    spl2_5 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.22/0.51  fof(f188,plain,(
% 0.22/0.51    spl2_23 <=> ! [X0] : r1_tarski(k3_xboole_0(k2_xboole_0(k1_tarski(sK0),sK1),X0),sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).
% 0.22/0.51  fof(f194,plain,(
% 0.22/0.51    ( ! [X1] : (r1_tarski(k3_xboole_0(X1,k2_xboole_0(k1_tarski(sK0),sK1)),sK1)) ) | (~spl2_5 | ~spl2_23)),
% 0.22/0.51    inference(superposition,[],[f189,f66])).
% 0.22/0.51  fof(f66,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) ) | ~spl2_5),
% 0.22/0.51    inference(avatar_component_clause,[],[f65])).
% 0.22/0.51  fof(f189,plain,(
% 0.22/0.51    ( ! [X0] : (r1_tarski(k3_xboole_0(k2_xboole_0(k1_tarski(sK0),sK1),X0),sK1)) ) | ~spl2_23),
% 0.22/0.51    inference(avatar_component_clause,[],[f188])).
% 0.22/0.51  fof(f220,plain,(
% 0.22/0.51    spl2_27 | ~spl2_3 | ~spl2_8),
% 0.22/0.51    inference(avatar_split_clause,[],[f98,f77,f57,f218])).
% 0.22/0.51  fof(f57,plain,(
% 0.22/0.51    spl2_3 <=> ! [X1,X0] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.22/0.51  fof(f77,plain,(
% 0.22/0.51    spl2_8 <=> ! [X1,X0] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.22/0.51  fof(f98,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) ) | (~spl2_3 | ~spl2_8)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f58,f78])).
% 0.22/0.51  fof(f78,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) ) | ~spl2_8),
% 0.22/0.51    inference(avatar_component_clause,[],[f77])).
% 0.22/0.51  fof(f58,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) ) | ~spl2_3),
% 0.22/0.51    inference(avatar_component_clause,[],[f57])).
% 0.22/0.51  fof(f200,plain,(
% 0.22/0.51    ~spl2_24 | ~spl2_4 | ~spl2_16),
% 0.22/0.51    inference(avatar_split_clause,[],[f161,f133,f61,f197])).
% 0.22/0.51  fof(f61,plain,(
% 0.22/0.51    spl2_4 <=> ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.22/0.51  fof(f133,plain,(
% 0.22/0.51    spl2_16 <=> ! [X0] : ~r1_tarski(k2_tarski(sK0,X0),sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.22/0.51  fof(f161,plain,(
% 0.22/0.51    ~r1_tarski(k1_tarski(sK0),sK1) | (~spl2_4 | ~spl2_16)),
% 0.22/0.51    inference(superposition,[],[f134,f62])).
% 0.22/0.51  fof(f62,plain,(
% 0.22/0.51    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) ) | ~spl2_4),
% 0.22/0.51    inference(avatar_component_clause,[],[f61])).
% 0.22/0.51  fof(f134,plain,(
% 0.22/0.51    ( ! [X0] : (~r1_tarski(k2_tarski(sK0,X0),sK1)) ) | ~spl2_16),
% 0.22/0.51    inference(avatar_component_clause,[],[f133])).
% 0.22/0.51  fof(f190,plain,(
% 0.22/0.51    spl2_23 | ~spl2_2 | ~spl2_9),
% 0.22/0.51    inference(avatar_split_clause,[],[f103,f81,f52,f188])).
% 0.22/0.51  fof(f52,plain,(
% 0.22/0.51    spl2_2 <=> r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.51  fof(f81,plain,(
% 0.22/0.51    spl2_9 <=> ! [X1,X0,X2] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.22/0.51  fof(f103,plain,(
% 0.22/0.51    ( ! [X0] : (r1_tarski(k3_xboole_0(k2_xboole_0(k1_tarski(sK0),sK1),X0),sK1)) ) | (~spl2_2 | ~spl2_9)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f54,f82])).
% 0.22/0.51  fof(f82,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1)) ) | ~spl2_9),
% 0.22/0.51    inference(avatar_component_clause,[],[f81])).
% 0.22/0.51  fof(f54,plain,(
% 0.22/0.51    r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1) | ~spl2_2),
% 0.22/0.51    inference(avatar_component_clause,[],[f52])).
% 0.22/0.51  fof(f135,plain,(
% 0.22/0.51    spl2_16 | spl2_1 | ~spl2_10),
% 0.22/0.51    inference(avatar_split_clause,[],[f108,f85,f47,f133])).
% 0.22/0.51  fof(f47,plain,(
% 0.22/0.51    spl2_1 <=> r2_hidden(sK0,sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.51  fof(f85,plain,(
% 0.22/0.51    spl2_10 <=> ! [X1,X0,X2] : (r2_hidden(X0,X2) | ~r1_tarski(k2_tarski(X0,X1),X2))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.22/0.51  fof(f108,plain,(
% 0.22/0.51    ( ! [X0] : (~r1_tarski(k2_tarski(sK0,X0),sK1)) ) | (spl2_1 | ~spl2_10)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f49,f86])).
% 0.22/0.51  fof(f86,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~r1_tarski(k2_tarski(X0,X1),X2) | r2_hidden(X0,X2)) ) | ~spl2_10),
% 0.22/0.51    inference(avatar_component_clause,[],[f85])).
% 0.22/0.51  fof(f49,plain,(
% 0.22/0.51    ~r2_hidden(sK0,sK1) | spl2_1),
% 0.22/0.51    inference(avatar_component_clause,[],[f47])).
% 0.22/0.51  fof(f87,plain,(
% 0.22/0.51    spl2_10),
% 0.22/0.51    inference(avatar_split_clause,[],[f37,f85])).
% 0.22/0.51  fof(f37,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f25])).
% 0.22/0.51  fof(f25,plain,(
% 0.22/0.51    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.22/0.51    inference(flattening,[],[f24])).
% 0.22/0.51  fof(f24,plain,(
% 0.22/0.51    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.22/0.51    inference(nnf_transformation,[],[f16])).
% 0.22/0.51  fof(f16,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 0.22/0.51  fof(f83,plain,(
% 0.22/0.51    spl2_9),
% 0.22/0.51    inference(avatar_split_clause,[],[f36,f81])).
% 0.22/0.51  fof(f36,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f21])).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1))),
% 0.22/0.51    inference(ennf_transformation,[],[f2])).
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k3_xboole_0(X0,X2),X1))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_xboole_1)).
% 0.22/0.51  fof(f79,plain,(
% 0.22/0.51    spl2_8),
% 0.22/0.51    inference(avatar_split_clause,[],[f33,f77])).
% 0.22/0.51  fof(f33,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f20])).
% 0.22/0.51  fof(f20,plain,(
% 0.22/0.51    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.22/0.51    inference(ennf_transformation,[],[f3])).
% 0.22/0.51  fof(f3,axiom,(
% 0.22/0.51    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.22/0.51  fof(f67,plain,(
% 0.22/0.51    spl2_5),
% 0.22/0.51    inference(avatar_split_clause,[],[f30,f65])).
% 0.22/0.51  fof(f30,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.22/0.51  fof(f63,plain,(
% 0.22/0.51    spl2_4),
% 0.22/0.51    inference(avatar_split_clause,[],[f28,f61])).
% 0.22/0.51  fof(f28,plain,(
% 0.22/0.51    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f9])).
% 0.22/0.51  fof(f9,axiom,(
% 0.22/0.51    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.51  fof(f59,plain,(
% 0.22/0.51    spl2_3),
% 0.22/0.51    inference(avatar_split_clause,[],[f29,f57])).
% 0.22/0.51  fof(f29,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f4])).
% 0.22/0.51  fof(f4,axiom,(
% 0.22/0.51    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.22/0.51  fof(f55,plain,(
% 0.22/0.51    spl2_2),
% 0.22/0.51    inference(avatar_split_clause,[],[f26,f52])).
% 0.22/0.51  fof(f26,plain,(
% 0.22/0.51    r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1)),
% 0.22/0.51    inference(cnf_transformation,[],[f23])).
% 0.22/0.51  fof(f23,plain,(
% 0.22/0.51    ~r2_hidden(sK0,sK1) & r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1)),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f22])).
% 0.22/0.51  fof(f22,plain,(
% 0.22/0.51    ? [X0,X1] : (~r2_hidden(X0,X1) & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1)) => (~r2_hidden(sK0,sK1) & r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f19,plain,(
% 0.22/0.51    ? [X0,X1] : (~r2_hidden(X0,X1) & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1))),
% 0.22/0.51    inference(ennf_transformation,[],[f18])).
% 0.22/0.51  fof(f18,negated_conjecture,(
% 0.22/0.51    ~! [X0,X1] : (r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) => r2_hidden(X0,X1))),
% 0.22/0.51    inference(negated_conjecture,[],[f17])).
% 0.22/0.51  fof(f17,conjecture,(
% 0.22/0.51    ! [X0,X1] : (r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) => r2_hidden(X0,X1))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_zfmisc_1)).
% 0.22/0.51  fof(f50,plain,(
% 0.22/0.51    ~spl2_1),
% 0.22/0.51    inference(avatar_split_clause,[],[f27,f47])).
% 0.22/0.51  fof(f27,plain,(
% 0.22/0.51    ~r2_hidden(sK0,sK1)),
% 0.22/0.51    inference(cnf_transformation,[],[f23])).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (22436)------------------------------
% 0.22/0.51  % (22436)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (22436)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (22436)Memory used [KB]: 6268
% 0.22/0.51  % (22436)Time elapsed: 0.069 s
% 0.22/0.51  % (22436)------------------------------
% 0.22/0.51  % (22436)------------------------------
% 0.22/0.51  % (22428)Success in time 0.148 s
%------------------------------------------------------------------------------
