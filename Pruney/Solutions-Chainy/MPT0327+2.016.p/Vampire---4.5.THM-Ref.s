%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:50 EST 2020

% Result     : Theorem 3.33s
% Output     : Refutation 3.33s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 156 expanded)
%              Number of leaves         :   17 (  55 expanded)
%              Depth                    :   11
%              Number of atoms          :  127 ( 253 expanded)
%              Number of equality atoms :   38 ( 111 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f477,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f71,f76,f92,f125,f390,f397,f425,f476])).

fof(f476,plain,
    ( spl4_6
    | ~ spl4_7 ),
    inference(avatar_contradiction_clause,[],[f475])).

fof(f475,plain,
    ( $false
    | spl4_6
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f474,f65])).

fof(f65,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f474,plain,
    ( ~ r1_tarski(sK1,sK1)
    | spl4_6
    | ~ spl4_7 ),
    inference(backward_demodulation,[],[f396,f460])).

fof(f460,plain,
    ( sK1 = k2_xboole_0(sK1,k1_tarski(sK0))
    | ~ spl4_7 ),
    inference(superposition,[],[f424,f53])).

fof(f53,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f424,plain,
    ( sK1 = k2_xboole_0(k1_tarski(sK0),sK1)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f422])).

fof(f422,plain,
    ( spl4_7
  <=> sK1 = k2_xboole_0(k1_tarski(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f396,plain,
    ( ~ r1_tarski(k2_xboole_0(sK1,k1_tarski(sK0)),sK1)
    | spl4_6 ),
    inference(avatar_component_clause,[],[f394])).

fof(f394,plain,
    ( spl4_6
  <=> r1_tarski(k2_xboole_0(sK1,k1_tarski(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f425,plain,
    ( spl4_7
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f279,f68,f422])).

fof(f68,plain,
    ( spl4_1
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f279,plain,
    ( sK1 = k2_xboole_0(k1_tarski(sK0),sK1)
    | ~ spl4_1 ),
    inference(resolution,[],[f87,f70])).

fof(f70,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f68])).

fof(f87,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(X3,X4)
      | k2_xboole_0(k1_tarski(X3),X4) = X4 ) ),
    inference(resolution,[],[f46,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f397,plain,
    ( ~ spl4_6
    | spl4_4 ),
    inference(avatar_split_clause,[],[f388,f118,f394])).

fof(f118,plain,
    ( spl4_4
  <=> r1_tarski(k2_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(sK0))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f388,plain,
    ( ~ r1_tarski(k2_xboole_0(sK1,k1_tarski(sK0)),sK1)
    | spl4_4 ),
    inference(forward_demodulation,[],[f384,f53])).

fof(f384,plain,
    ( ~ r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1)
    | spl4_4 ),
    inference(backward_demodulation,[],[f120,f383])).

fof(f383,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) = k2_xboole_0(k1_tarski(X0),k4_xboole_0(X1,k1_tarski(X0))) ),
    inference(forward_demodulation,[],[f382,f336])).

fof(f336,plain,(
    ! [X2,X3] : k2_xboole_0(k1_tarski(X2),X3) = k2_xboole_0(k1_tarski(X2),k4_xboole_0(k4_xboole_0(X3,k1_tarski(X2)),k1_tarski(X2))) ),
    inference(forward_demodulation,[],[f324,f50])).

fof(f50,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f324,plain,(
    ! [X2,X3] : k5_xboole_0(k1_tarski(X2),k4_xboole_0(X3,k1_tarski(X2))) = k2_xboole_0(k1_tarski(X2),k4_xboole_0(k4_xboole_0(X3,k1_tarski(X2)),k1_tarski(X2))) ),
    inference(superposition,[],[f48,f129])).

fof(f129,plain,(
    ! [X0,X1] : k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k4_xboole_0(X1,k1_tarski(X0))) ),
    inference(resolution,[],[f41,f61])).

fof(f61,plain,(
    ! [X2,X1] : ~ r2_hidden(X2,k4_xboole_0(X1,k1_tarski(X2))) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
    <=> ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l33_zfmisc_1)).

fof(f48,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

fof(f382,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k4_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0))) = k2_xboole_0(k1_tarski(X0),k4_xboole_0(X1,k1_tarski(X0))) ),
    inference(forward_demodulation,[],[f365,f337])).

fof(f337,plain,(
    ! [X8,X9] : k5_xboole_0(k4_xboole_0(X9,k1_tarski(X8)),k1_tarski(X8)) = k2_xboole_0(k1_tarski(X8),k4_xboole_0(X9,k1_tarski(X8))) ),
    inference(forward_demodulation,[],[f327,f53])).

fof(f327,plain,(
    ! [X8,X9] : k2_xboole_0(k4_xboole_0(X9,k1_tarski(X8)),k1_tarski(X8)) = k5_xboole_0(k4_xboole_0(X9,k1_tarski(X8)),k1_tarski(X8)) ),
    inference(superposition,[],[f50,f129])).

fof(f365,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k4_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0))) = k5_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) ),
    inference(superposition,[],[f142,f129])).

fof(f142,plain,(
    ! [X2,X3] : k2_xboole_0(k4_xboole_0(X3,X2),k4_xboole_0(X2,X3)) = k5_xboole_0(X2,X3) ),
    inference(superposition,[],[f48,f53])).

fof(f120,plain,
    ( ~ r1_tarski(k2_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(sK0))),sK1)
    | spl4_4 ),
    inference(avatar_component_clause,[],[f118])).

fof(f390,plain,(
    spl4_5 ),
    inference(avatar_contradiction_clause,[],[f389])).

fof(f389,plain,
    ( $false
    | spl4_5 ),
    inference(subsumption_resolution,[],[f385,f79])).

fof(f79,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X1,X0)) ),
    inference(superposition,[],[f54,f53])).

fof(f54,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f385,plain,
    ( ~ r1_tarski(sK1,k2_xboole_0(k1_tarski(sK0),sK1))
    | spl4_5 ),
    inference(backward_demodulation,[],[f124,f383])).

fof(f124,plain,
    ( ~ r1_tarski(sK1,k2_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(sK0))))
    | spl4_5 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl4_5
  <=> r1_tarski(sK1,k2_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f125,plain,
    ( ~ spl4_4
    | ~ spl4_5
    | spl4_2 ),
    inference(avatar_split_clause,[],[f109,f73,f122,f118])).

fof(f73,plain,
    ( spl4_2
  <=> sK1 = k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f109,plain,
    ( ~ r1_tarski(sK1,k2_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(sK0))))
    | ~ r1_tarski(k2_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(sK0))),sK1)
    | spl4_2 ),
    inference(forward_demodulation,[],[f108,f53])).

fof(f108,plain,
    ( ~ r1_tarski(k2_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(sK0))),sK1)
    | ~ r1_tarski(sK1,k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)))
    | spl4_2 ),
    inference(forward_demodulation,[],[f101,f53])).

fof(f101,plain,
    ( ~ r1_tarski(k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)),sK1)
    | ~ r1_tarski(sK1,k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)))
    | spl4_2 ),
    inference(extensionality_resolution,[],[f45,f75])).

fof(f75,plain,
    ( sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))
    | spl4_2 ),
    inference(avatar_component_clause,[],[f73])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f92,plain,
    ( ~ spl4_3
    | spl4_2 ),
    inference(avatar_split_clause,[],[f78,f73,f89])).

fof(f89,plain,
    ( spl4_3
  <=> sK1 = k2_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f78,plain,
    ( sK1 != k2_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(sK0)))
    | spl4_2 ),
    inference(superposition,[],[f75,f53])).

fof(f76,plain,(
    ~ spl4_2 ),
    inference(avatar_split_clause,[],[f30,f73])).

fof(f30,plain,(
    sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ? [X0,X1] :
      ( k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    inference(negated_conjecture,[],[f23])).

fof(f23,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t140_zfmisc_1)).

fof(f71,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f29,f68])).

fof(f29,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:31:39 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.54  % (6405)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  % (6386)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.54  % (6391)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (6397)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.55  % (6387)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.55  % (6388)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.56  % (6379)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.57  % (6380)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.58  % (6399)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.58  % (6408)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.58  % (6400)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.58  % (6384)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.58  % (6382)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.58  % (6399)Refutation not found, incomplete strategy% (6399)------------------------------
% 0.21/0.58  % (6399)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.58  % (6400)Refutation not found, incomplete strategy% (6400)------------------------------
% 1.59/0.58  % (6400)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.58  % (6400)Termination reason: Refutation not found, incomplete strategy
% 1.59/0.58  
% 1.59/0.58  % (6400)Memory used [KB]: 1791
% 1.59/0.58  % (6400)Time elapsed: 0.180 s
% 1.59/0.58  % (6400)------------------------------
% 1.59/0.58  % (6400)------------------------------
% 1.59/0.59  % (6390)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.59/0.59  % (6401)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.59/0.59  % (6393)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.59/0.59  % (6399)Termination reason: Refutation not found, incomplete strategy
% 1.59/0.59  
% 1.59/0.59  % (6399)Memory used [KB]: 10746
% 1.59/0.59  % (6399)Time elapsed: 0.156 s
% 1.59/0.59  % (6399)------------------------------
% 1.59/0.59  % (6399)------------------------------
% 1.59/0.59  % (6383)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.59/0.59  % (6381)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.59/0.59  % (6403)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.59/0.60  % (6398)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.59/0.60  % (6395)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.59/0.60  % (6402)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.90/0.61  % (6385)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.90/0.61  % (6392)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.90/0.61  % (6389)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.90/0.61  % (6396)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.90/0.61  % (6404)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.90/0.61  % (6394)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.90/0.62  % (6406)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.90/0.62  % (6407)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 3.33/0.81  % (6434)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 3.33/0.82  % (6433)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 3.33/0.83  % (6380)Refutation found. Thanks to Tanya!
% 3.33/0.83  % SZS status Theorem for theBenchmark
% 3.33/0.83  % SZS output start Proof for theBenchmark
% 3.33/0.83  fof(f477,plain,(
% 3.33/0.83    $false),
% 3.33/0.83    inference(avatar_sat_refutation,[],[f71,f76,f92,f125,f390,f397,f425,f476])).
% 3.33/0.83  fof(f476,plain,(
% 3.33/0.83    spl4_6 | ~spl4_7),
% 3.33/0.83    inference(avatar_contradiction_clause,[],[f475])).
% 3.33/0.83  fof(f475,plain,(
% 3.33/0.83    $false | (spl4_6 | ~spl4_7)),
% 3.33/0.83    inference(subsumption_resolution,[],[f474,f65])).
% 3.33/0.83  fof(f65,plain,(
% 3.33/0.83    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.33/0.83    inference(equality_resolution,[],[f44])).
% 3.33/0.83  fof(f44,plain,(
% 3.33/0.83    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.33/0.83    inference(cnf_transformation,[],[f5])).
% 3.33/0.83  fof(f5,axiom,(
% 3.33/0.83    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.33/0.83    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 3.33/0.83  fof(f474,plain,(
% 3.33/0.83    ~r1_tarski(sK1,sK1) | (spl4_6 | ~spl4_7)),
% 3.33/0.83    inference(backward_demodulation,[],[f396,f460])).
% 3.33/0.83  fof(f460,plain,(
% 3.33/0.83    sK1 = k2_xboole_0(sK1,k1_tarski(sK0)) | ~spl4_7),
% 3.33/0.83    inference(superposition,[],[f424,f53])).
% 3.33/0.83  fof(f53,plain,(
% 3.33/0.83    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 3.33/0.83    inference(cnf_transformation,[],[f1])).
% 3.33/0.83  fof(f1,axiom,(
% 3.33/0.83    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 3.33/0.83    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 3.33/0.83  fof(f424,plain,(
% 3.33/0.83    sK1 = k2_xboole_0(k1_tarski(sK0),sK1) | ~spl4_7),
% 3.33/0.83    inference(avatar_component_clause,[],[f422])).
% 3.33/0.83  fof(f422,plain,(
% 3.33/0.83    spl4_7 <=> sK1 = k2_xboole_0(k1_tarski(sK0),sK1)),
% 3.33/0.83    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 3.33/0.83  fof(f396,plain,(
% 3.33/0.83    ~r1_tarski(k2_xboole_0(sK1,k1_tarski(sK0)),sK1) | spl4_6),
% 3.33/0.83    inference(avatar_component_clause,[],[f394])).
% 3.33/0.83  fof(f394,plain,(
% 3.33/0.83    spl4_6 <=> r1_tarski(k2_xboole_0(sK1,k1_tarski(sK0)),sK1)),
% 3.33/0.83    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 3.33/0.83  fof(f425,plain,(
% 3.33/0.83    spl4_7 | ~spl4_1),
% 3.33/0.83    inference(avatar_split_clause,[],[f279,f68,f422])).
% 3.33/0.83  fof(f68,plain,(
% 3.33/0.83    spl4_1 <=> r2_hidden(sK0,sK1)),
% 3.33/0.83    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 3.33/0.83  fof(f279,plain,(
% 3.33/0.83    sK1 = k2_xboole_0(k1_tarski(sK0),sK1) | ~spl4_1),
% 3.33/0.83    inference(resolution,[],[f87,f70])).
% 3.33/0.83  fof(f70,plain,(
% 3.33/0.83    r2_hidden(sK0,sK1) | ~spl4_1),
% 3.33/0.83    inference(avatar_component_clause,[],[f68])).
% 3.33/0.83  fof(f87,plain,(
% 3.33/0.83    ( ! [X4,X3] : (~r2_hidden(X3,X4) | k2_xboole_0(k1_tarski(X3),X4) = X4) )),
% 3.33/0.83    inference(resolution,[],[f46,f55])).
% 3.33/0.83  fof(f55,plain,(
% 3.33/0.83    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 3.33/0.83    inference(cnf_transformation,[],[f19])).
% 3.33/0.83  fof(f19,axiom,(
% 3.33/0.83    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 3.33/0.83    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 3.33/0.83  fof(f46,plain,(
% 3.33/0.83    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 3.33/0.83    inference(cnf_transformation,[],[f26])).
% 3.33/0.83  fof(f26,plain,(
% 3.33/0.83    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 3.33/0.83    inference(ennf_transformation,[],[f7])).
% 3.33/0.83  fof(f7,axiom,(
% 3.33/0.83    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 3.33/0.83    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 3.33/0.83  fof(f397,plain,(
% 3.33/0.83    ~spl4_6 | spl4_4),
% 3.33/0.83    inference(avatar_split_clause,[],[f388,f118,f394])).
% 3.33/0.83  fof(f118,plain,(
% 3.33/0.83    spl4_4 <=> r1_tarski(k2_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(sK0))),sK1)),
% 3.33/0.83    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 3.33/0.83  fof(f388,plain,(
% 3.33/0.83    ~r1_tarski(k2_xboole_0(sK1,k1_tarski(sK0)),sK1) | spl4_4),
% 3.33/0.83    inference(forward_demodulation,[],[f384,f53])).
% 3.33/0.83  fof(f384,plain,(
% 3.33/0.83    ~r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1) | spl4_4),
% 3.33/0.83    inference(backward_demodulation,[],[f120,f383])).
% 3.33/0.83  fof(f383,plain,(
% 3.33/0.83    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) = k2_xboole_0(k1_tarski(X0),k4_xboole_0(X1,k1_tarski(X0)))) )),
% 3.33/0.83    inference(forward_demodulation,[],[f382,f336])).
% 3.33/0.83  fof(f336,plain,(
% 3.33/0.83    ( ! [X2,X3] : (k2_xboole_0(k1_tarski(X2),X3) = k2_xboole_0(k1_tarski(X2),k4_xboole_0(k4_xboole_0(X3,k1_tarski(X2)),k1_tarski(X2)))) )),
% 3.33/0.83    inference(forward_demodulation,[],[f324,f50])).
% 3.33/0.83  fof(f50,plain,(
% 3.33/0.83    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 3.33/0.83    inference(cnf_transformation,[],[f13])).
% 3.33/0.83  fof(f13,axiom,(
% 3.33/0.83    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 3.33/0.83    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 3.33/0.83  fof(f324,plain,(
% 3.33/0.83    ( ! [X2,X3] : (k5_xboole_0(k1_tarski(X2),k4_xboole_0(X3,k1_tarski(X2))) = k2_xboole_0(k1_tarski(X2),k4_xboole_0(k4_xboole_0(X3,k1_tarski(X2)),k1_tarski(X2)))) )),
% 3.33/0.83    inference(superposition,[],[f48,f129])).
% 3.33/0.83  fof(f129,plain,(
% 3.33/0.83    ( ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k4_xboole_0(X1,k1_tarski(X0)))) )),
% 3.33/0.83    inference(resolution,[],[f41,f61])).
% 3.33/0.83  fof(f61,plain,(
% 3.33/0.83    ( ! [X2,X1] : (~r2_hidden(X2,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 3.33/0.83    inference(equality_resolution,[],[f32])).
% 3.33/0.83  fof(f32,plain,(
% 3.33/0.83    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 3.33/0.83    inference(cnf_transformation,[],[f22])).
% 3.33/0.83  fof(f22,axiom,(
% 3.33/0.83    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 3.33/0.83    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).
% 3.33/0.83  fof(f41,plain,(
% 3.33/0.83    ( ! [X0,X1] : (r2_hidden(X0,X1) | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)) )),
% 3.33/0.83    inference(cnf_transformation,[],[f20])).
% 3.33/0.83  fof(f20,axiom,(
% 3.33/0.83    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) <=> ~r2_hidden(X0,X1))),
% 3.33/0.83    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l33_zfmisc_1)).
% 3.33/0.83  fof(f48,plain,(
% 3.33/0.83    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 3.33/0.83    inference(cnf_transformation,[],[f4])).
% 3.33/0.83  fof(f4,axiom,(
% 3.33/0.83    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 3.33/0.83    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).
% 3.33/0.83  fof(f382,plain,(
% 3.33/0.83    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),k4_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0))) = k2_xboole_0(k1_tarski(X0),k4_xboole_0(X1,k1_tarski(X0)))) )),
% 3.33/0.83    inference(forward_demodulation,[],[f365,f337])).
% 3.33/0.83  fof(f337,plain,(
% 3.33/0.83    ( ! [X8,X9] : (k5_xboole_0(k4_xboole_0(X9,k1_tarski(X8)),k1_tarski(X8)) = k2_xboole_0(k1_tarski(X8),k4_xboole_0(X9,k1_tarski(X8)))) )),
% 3.33/0.83    inference(forward_demodulation,[],[f327,f53])).
% 3.33/0.83  fof(f327,plain,(
% 3.33/0.83    ( ! [X8,X9] : (k2_xboole_0(k4_xboole_0(X9,k1_tarski(X8)),k1_tarski(X8)) = k5_xboole_0(k4_xboole_0(X9,k1_tarski(X8)),k1_tarski(X8))) )),
% 3.33/0.83    inference(superposition,[],[f50,f129])).
% 3.33/0.83  fof(f365,plain,(
% 3.33/0.83    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),k4_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0))) = k5_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0))) )),
% 3.33/0.83    inference(superposition,[],[f142,f129])).
% 3.33/0.83  fof(f142,plain,(
% 3.33/0.83    ( ! [X2,X3] : (k2_xboole_0(k4_xboole_0(X3,X2),k4_xboole_0(X2,X3)) = k5_xboole_0(X2,X3)) )),
% 3.33/0.83    inference(superposition,[],[f48,f53])).
% 3.33/0.83  fof(f120,plain,(
% 3.33/0.83    ~r1_tarski(k2_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(sK0))),sK1) | spl4_4),
% 3.33/0.83    inference(avatar_component_clause,[],[f118])).
% 3.33/0.83  fof(f390,plain,(
% 3.33/0.83    spl4_5),
% 3.33/0.83    inference(avatar_contradiction_clause,[],[f389])).
% 3.33/0.83  fof(f389,plain,(
% 3.33/0.83    $false | spl4_5),
% 3.33/0.83    inference(subsumption_resolution,[],[f385,f79])).
% 3.33/0.83  fof(f79,plain,(
% 3.33/0.83    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X0))) )),
% 3.33/0.83    inference(superposition,[],[f54,f53])).
% 3.33/0.83  fof(f54,plain,(
% 3.33/0.83    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 3.33/0.83    inference(cnf_transformation,[],[f12])).
% 3.33/0.83  fof(f12,axiom,(
% 3.33/0.83    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 3.33/0.83    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 3.33/0.83  fof(f385,plain,(
% 3.33/0.83    ~r1_tarski(sK1,k2_xboole_0(k1_tarski(sK0),sK1)) | spl4_5),
% 3.33/0.83    inference(backward_demodulation,[],[f124,f383])).
% 3.33/0.83  fof(f124,plain,(
% 3.33/0.83    ~r1_tarski(sK1,k2_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(sK0)))) | spl4_5),
% 3.33/0.83    inference(avatar_component_clause,[],[f122])).
% 3.33/0.83  fof(f122,plain,(
% 3.33/0.83    spl4_5 <=> r1_tarski(sK1,k2_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(sK0))))),
% 3.33/0.83    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 3.33/0.83  fof(f125,plain,(
% 3.33/0.83    ~spl4_4 | ~spl4_5 | spl4_2),
% 3.33/0.83    inference(avatar_split_clause,[],[f109,f73,f122,f118])).
% 3.33/0.83  fof(f73,plain,(
% 3.33/0.83    spl4_2 <=> sK1 = k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))),
% 3.33/0.83    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 3.33/0.83  fof(f109,plain,(
% 3.33/0.83    ~r1_tarski(sK1,k2_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(sK0)))) | ~r1_tarski(k2_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(sK0))),sK1) | spl4_2),
% 3.33/0.83    inference(forward_demodulation,[],[f108,f53])).
% 3.33/0.83  fof(f108,plain,(
% 3.33/0.83    ~r1_tarski(k2_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(sK0))),sK1) | ~r1_tarski(sK1,k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))) | spl4_2),
% 3.33/0.83    inference(forward_demodulation,[],[f101,f53])).
% 3.33/0.83  fof(f101,plain,(
% 3.33/0.83    ~r1_tarski(k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)),sK1) | ~r1_tarski(sK1,k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))) | spl4_2),
% 3.33/0.83    inference(extensionality_resolution,[],[f45,f75])).
% 3.33/0.83  fof(f75,plain,(
% 3.33/0.83    sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) | spl4_2),
% 3.33/0.83    inference(avatar_component_clause,[],[f73])).
% 3.33/0.83  fof(f45,plain,(
% 3.33/0.83    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 3.33/0.83    inference(cnf_transformation,[],[f5])).
% 3.33/0.83  fof(f92,plain,(
% 3.33/0.83    ~spl4_3 | spl4_2),
% 3.33/0.83    inference(avatar_split_clause,[],[f78,f73,f89])).
% 3.33/0.83  fof(f89,plain,(
% 3.33/0.83    spl4_3 <=> sK1 = k2_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(sK0)))),
% 3.33/0.83    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 3.33/0.83  fof(f78,plain,(
% 3.33/0.83    sK1 != k2_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(sK0))) | spl4_2),
% 3.33/0.83    inference(superposition,[],[f75,f53])).
% 3.33/0.83  fof(f76,plain,(
% 3.33/0.83    ~spl4_2),
% 3.33/0.83    inference(avatar_split_clause,[],[f30,f73])).
% 3.33/0.83  fof(f30,plain,(
% 3.33/0.83    sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))),
% 3.33/0.83    inference(cnf_transformation,[],[f25])).
% 3.33/0.83  fof(f25,plain,(
% 3.33/0.83    ? [X0,X1] : (k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1 & r2_hidden(X0,X1))),
% 3.33/0.83    inference(ennf_transformation,[],[f24])).
% 3.33/0.83  fof(f24,negated_conjecture,(
% 3.33/0.83    ~! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1)),
% 3.33/0.83    inference(negated_conjecture,[],[f23])).
% 3.33/0.83  fof(f23,conjecture,(
% 3.33/0.83    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1)),
% 3.33/0.83    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t140_zfmisc_1)).
% 3.33/0.83  fof(f71,plain,(
% 3.33/0.83    spl4_1),
% 3.33/0.83    inference(avatar_split_clause,[],[f29,f68])).
% 3.33/0.83  fof(f29,plain,(
% 3.33/0.83    r2_hidden(sK0,sK1)),
% 3.33/0.83    inference(cnf_transformation,[],[f25])).
% 3.33/0.83  % SZS output end Proof for theBenchmark
% 3.33/0.83  % (6380)------------------------------
% 3.33/0.83  % (6380)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.33/0.83  % (6380)Termination reason: Refutation
% 3.33/0.83  
% 3.33/0.83  % (6380)Memory used [KB]: 6780
% 3.33/0.83  % (6380)Time elapsed: 0.400 s
% 3.33/0.83  % (6380)------------------------------
% 3.33/0.83  % (6380)------------------------------
% 3.33/0.83  % (6378)Success in time 0.471 s
%------------------------------------------------------------------------------
