%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:11 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   51 (  62 expanded)
%              Number of leaves         :   16 (  27 expanded)
%              Depth                    :    5
%              Number of atoms          :  108 ( 135 expanded)
%              Number of equality atoms :   15 (  19 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f83,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f26,f30,f34,f42,f50,f58,f62,f72,f77,f80])).

fof(f80,plain,
    ( spl1_1
    | ~ spl1_3
    | ~ spl1_10
    | ~ spl1_12 ),
    inference(avatar_contradiction_clause,[],[f78])).

fof(f78,plain,
    ( $false
    | spl1_1
    | ~ spl1_3
    | ~ spl1_10
    | ~ spl1_12 ),
    inference(unit_resulting_resolution,[],[f33,f25,f71,f61])).

fof(f61,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | X0 = X1
        | r2_xboole_0(X0,X1) )
    | ~ spl1_10 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl1_10
  <=> ! [X1,X0] :
        ( ~ r1_tarski(X0,X1)
        | X0 = X1
        | r2_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).

fof(f71,plain,
    ( ! [X0] : r1_tarski(k10_relat_1(k1_xboole_0,X0),k1_xboole_0)
    | ~ spl1_12 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl1_12
  <=> ! [X0] : r1_tarski(k10_relat_1(k1_xboole_0,X0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_12])])).

fof(f25,plain,
    ( k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0)
    | spl1_1 ),
    inference(avatar_component_clause,[],[f24])).

fof(f24,plain,
    ( spl1_1
  <=> k1_xboole_0 = k10_relat_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f33,plain,
    ( ! [X0] : ~ r2_xboole_0(X0,k1_xboole_0)
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f32])).

fof(f32,plain,
    ( spl1_3
  <=> ! [X0] : ~ r2_xboole_0(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f77,plain,
    ( ~ spl1_2
    | ~ spl1_7
    | spl1_11 ),
    inference(avatar_contradiction_clause,[],[f76])).

fof(f76,plain,
    ( $false
    | ~ spl1_2
    | ~ spl1_7
    | spl1_11 ),
    inference(subsumption_resolution,[],[f74,f29])).

fof(f29,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl1_2 ),
    inference(avatar_component_clause,[],[f28])).

fof(f28,plain,
    ( spl1_2
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f74,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl1_7
    | spl1_11 ),
    inference(resolution,[],[f68,f49])).

fof(f49,plain,
    ( ! [X0] :
        ( v1_relat_1(X0)
        | ~ v1_xboole_0(X0) )
    | ~ spl1_7 ),
    inference(avatar_component_clause,[],[f48])).

fof(f48,plain,
    ( spl1_7
  <=> ! [X0] :
        ( ~ v1_xboole_0(X0)
        | v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).

fof(f68,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl1_11 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl1_11
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).

fof(f72,plain,
    ( ~ spl1_11
    | spl1_12
    | ~ spl1_5
    | ~ spl1_9 ),
    inference(avatar_split_clause,[],[f63,f56,f40,f70,f67])).

fof(f40,plain,
    ( spl1_5
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f56,plain,
    ( spl1_9
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X1)
        | r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).

fof(f63,plain,
    ( ! [X0] :
        ( r1_tarski(k10_relat_1(k1_xboole_0,X0),k1_xboole_0)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl1_5
    | ~ spl1_9 ),
    inference(superposition,[],[f57,f41])).

fof(f41,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl1_5 ),
    inference(avatar_component_clause,[],[f40])).

fof(f57,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
        | ~ v1_relat_1(X1) )
    | ~ spl1_9 ),
    inference(avatar_component_clause,[],[f56])).

fof(f62,plain,(
    spl1_10 ),
    inference(avatar_split_clause,[],[f21,f60])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f58,plain,(
    spl1_9 ),
    inference(avatar_split_clause,[],[f18,f56])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

fof(f50,plain,(
    spl1_7 ),
    inference(avatar_split_clause,[],[f17,f48])).

fof(f17,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f42,plain,(
    spl1_5 ),
    inference(avatar_split_clause,[],[f14,f40])).

fof(f14,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f34,plain,(
    spl1_3 ),
    inference(avatar_split_clause,[],[f16,f32])).

fof(f16,plain,(
    ! [X0] : ~ r2_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : ~ r2_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t115_xboole_1)).

fof(f30,plain,(
    spl1_2 ),
    inference(avatar_split_clause,[],[f13,f28])).

fof(f13,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f26,plain,(
    ~ spl1_1 ),
    inference(avatar_split_clause,[],[f12,f24])).

fof(f12,plain,(
    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:19:41 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.22/0.46  % (25491)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.46  % (25493)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.46  % (25485)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.46  % (25496)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.46  % (25488)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.46  % (25485)Refutation not found, incomplete strategy% (25485)------------------------------
% 0.22/0.46  % (25485)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.46  % (25485)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.46  % (25488)Refutation not found, incomplete strategy% (25488)------------------------------
% 0.22/0.46  % (25488)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.46  % (25488)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.46  
% 0.22/0.46  % (25488)Memory used [KB]: 1535
% 0.22/0.46  % (25488)Time elapsed: 0.062 s
% 0.22/0.46  % (25488)------------------------------
% 0.22/0.46  % (25488)------------------------------
% 0.22/0.46  
% 0.22/0.46  % (25485)Memory used [KB]: 10490
% 0.22/0.46  % (25485)Time elapsed: 0.062 s
% 0.22/0.46  % (25485)------------------------------
% 0.22/0.46  % (25485)------------------------------
% 0.22/0.47  % (25496)Refutation not found, incomplete strategy% (25496)------------------------------
% 0.22/0.47  % (25496)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (25496)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.47  
% 0.22/0.47  % (25496)Memory used [KB]: 6012
% 0.22/0.47  % (25496)Time elapsed: 0.064 s
% 0.22/0.47  % (25496)------------------------------
% 0.22/0.47  % (25496)------------------------------
% 0.22/0.47  % (25493)Refutation found. Thanks to Tanya!
% 0.22/0.47  % SZS status Theorem for theBenchmark
% 0.22/0.47  % SZS output start Proof for theBenchmark
% 0.22/0.47  fof(f83,plain,(
% 0.22/0.47    $false),
% 0.22/0.47    inference(avatar_sat_refutation,[],[f26,f30,f34,f42,f50,f58,f62,f72,f77,f80])).
% 0.22/0.47  fof(f80,plain,(
% 0.22/0.47    spl1_1 | ~spl1_3 | ~spl1_10 | ~spl1_12),
% 0.22/0.47    inference(avatar_contradiction_clause,[],[f78])).
% 0.22/0.47  fof(f78,plain,(
% 0.22/0.47    $false | (spl1_1 | ~spl1_3 | ~spl1_10 | ~spl1_12)),
% 0.22/0.47    inference(unit_resulting_resolution,[],[f33,f25,f71,f61])).
% 0.22/0.47  fof(f61,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1)) ) | ~spl1_10),
% 0.22/0.47    inference(avatar_component_clause,[],[f60])).
% 0.22/0.47  fof(f60,plain,(
% 0.22/0.47    spl1_10 <=> ! [X1,X0] : (~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).
% 0.22/0.47  fof(f71,plain,(
% 0.22/0.47    ( ! [X0] : (r1_tarski(k10_relat_1(k1_xboole_0,X0),k1_xboole_0)) ) | ~spl1_12),
% 0.22/0.47    inference(avatar_component_clause,[],[f70])).
% 0.22/0.47  fof(f70,plain,(
% 0.22/0.47    spl1_12 <=> ! [X0] : r1_tarski(k10_relat_1(k1_xboole_0,X0),k1_xboole_0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_12])])).
% 0.22/0.47  fof(f25,plain,(
% 0.22/0.47    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0) | spl1_1),
% 0.22/0.47    inference(avatar_component_clause,[],[f24])).
% 0.22/0.47  fof(f24,plain,(
% 0.22/0.47    spl1_1 <=> k1_xboole_0 = k10_relat_1(k1_xboole_0,sK0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.22/0.47  fof(f33,plain,(
% 0.22/0.47    ( ! [X0] : (~r2_xboole_0(X0,k1_xboole_0)) ) | ~spl1_3),
% 0.22/0.47    inference(avatar_component_clause,[],[f32])).
% 0.22/0.47  fof(f32,plain,(
% 0.22/0.47    spl1_3 <=> ! [X0] : ~r2_xboole_0(X0,k1_xboole_0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.22/0.47  fof(f77,plain,(
% 0.22/0.47    ~spl1_2 | ~spl1_7 | spl1_11),
% 0.22/0.47    inference(avatar_contradiction_clause,[],[f76])).
% 0.22/0.47  fof(f76,plain,(
% 0.22/0.47    $false | (~spl1_2 | ~spl1_7 | spl1_11)),
% 0.22/0.47    inference(subsumption_resolution,[],[f74,f29])).
% 0.22/0.47  fof(f29,plain,(
% 0.22/0.47    v1_xboole_0(k1_xboole_0) | ~spl1_2),
% 0.22/0.47    inference(avatar_component_clause,[],[f28])).
% 0.22/0.47  fof(f28,plain,(
% 0.22/0.47    spl1_2 <=> v1_xboole_0(k1_xboole_0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.22/0.47  fof(f74,plain,(
% 0.22/0.47    ~v1_xboole_0(k1_xboole_0) | (~spl1_7 | spl1_11)),
% 0.22/0.47    inference(resolution,[],[f68,f49])).
% 0.22/0.47  fof(f49,plain,(
% 0.22/0.47    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) ) | ~spl1_7),
% 0.22/0.47    inference(avatar_component_clause,[],[f48])).
% 0.22/0.47  fof(f48,plain,(
% 0.22/0.47    spl1_7 <=> ! [X0] : (~v1_xboole_0(X0) | v1_relat_1(X0))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).
% 0.22/0.47  fof(f68,plain,(
% 0.22/0.47    ~v1_relat_1(k1_xboole_0) | spl1_11),
% 0.22/0.47    inference(avatar_component_clause,[],[f67])).
% 0.22/0.47  fof(f67,plain,(
% 0.22/0.47    spl1_11 <=> v1_relat_1(k1_xboole_0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).
% 0.22/0.47  fof(f72,plain,(
% 0.22/0.47    ~spl1_11 | spl1_12 | ~spl1_5 | ~spl1_9),
% 0.22/0.47    inference(avatar_split_clause,[],[f63,f56,f40,f70,f67])).
% 0.22/0.47  fof(f40,plain,(
% 0.22/0.47    spl1_5 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.22/0.47  fof(f56,plain,(
% 0.22/0.47    spl1_9 <=> ! [X1,X0] : (~v1_relat_1(X1) | r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).
% 0.22/0.47  fof(f63,plain,(
% 0.22/0.47    ( ! [X0] : (r1_tarski(k10_relat_1(k1_xboole_0,X0),k1_xboole_0) | ~v1_relat_1(k1_xboole_0)) ) | (~spl1_5 | ~spl1_9)),
% 0.22/0.47    inference(superposition,[],[f57,f41])).
% 0.22/0.47  fof(f41,plain,(
% 0.22/0.47    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl1_5),
% 0.22/0.47    inference(avatar_component_clause,[],[f40])).
% 0.22/0.47  fof(f57,plain,(
% 0.22/0.47    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) ) | ~spl1_9),
% 0.22/0.47    inference(avatar_component_clause,[],[f56])).
% 0.22/0.47  fof(f62,plain,(
% 0.22/0.47    spl1_10),
% 0.22/0.47    inference(avatar_split_clause,[],[f21,f60])).
% 0.22/0.47  fof(f21,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f1])).
% 0.22/0.47  fof(f1,axiom,(
% 0.22/0.47    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).
% 0.22/0.47  fof(f58,plain,(
% 0.22/0.47    spl1_9),
% 0.22/0.47    inference(avatar_split_clause,[],[f18,f56])).
% 0.22/0.47  fof(f18,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f11])).
% 0.22/0.47  fof(f11,plain,(
% 0.22/0.47    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.22/0.47    inference(ennf_transformation,[],[f5])).
% 0.22/0.47  fof(f5,axiom,(
% 0.22/0.47    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).
% 0.22/0.47  fof(f50,plain,(
% 0.22/0.47    spl1_7),
% 0.22/0.47    inference(avatar_split_clause,[],[f17,f48])).
% 0.22/0.47  fof(f17,plain,(
% 0.22/0.47    ( ! [X0] : (~v1_xboole_0(X0) | v1_relat_1(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f10])).
% 0.22/0.47  fof(f10,plain,(
% 0.22/0.47    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 0.22/0.47    inference(ennf_transformation,[],[f4])).
% 0.22/0.47  fof(f4,axiom,(
% 0.22/0.47    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).
% 0.22/0.47  fof(f42,plain,(
% 0.22/0.47    spl1_5),
% 0.22/0.47    inference(avatar_split_clause,[],[f14,f40])).
% 0.22/0.47  fof(f14,plain,(
% 0.22/0.47    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.47    inference(cnf_transformation,[],[f6])).
% 0.22/0.47  fof(f6,axiom,(
% 0.22/0.47    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.22/0.47  fof(f34,plain,(
% 0.22/0.47    spl1_3),
% 0.22/0.47    inference(avatar_split_clause,[],[f16,f32])).
% 0.22/0.47  fof(f16,plain,(
% 0.22/0.47    ( ! [X0] : (~r2_xboole_0(X0,k1_xboole_0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f3])).
% 0.22/0.47  fof(f3,axiom,(
% 0.22/0.47    ! [X0] : ~r2_xboole_0(X0,k1_xboole_0)),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t115_xboole_1)).
% 0.22/0.47  fof(f30,plain,(
% 0.22/0.47    spl1_2),
% 0.22/0.47    inference(avatar_split_clause,[],[f13,f28])).
% 0.22/0.47  fof(f13,plain,(
% 0.22/0.47    v1_xboole_0(k1_xboole_0)),
% 0.22/0.47    inference(cnf_transformation,[],[f2])).
% 0.22/0.47  fof(f2,axiom,(
% 0.22/0.47    v1_xboole_0(k1_xboole_0)),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.47  fof(f26,plain,(
% 0.22/0.47    ~spl1_1),
% 0.22/0.47    inference(avatar_split_clause,[],[f12,f24])).
% 0.22/0.47  fof(f12,plain,(
% 0.22/0.47    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0)),
% 0.22/0.47    inference(cnf_transformation,[],[f9])).
% 0.22/0.47  fof(f9,plain,(
% 0.22/0.47    ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0)),
% 0.22/0.47    inference(ennf_transformation,[],[f8])).
% 0.22/0.47  fof(f8,negated_conjecture,(
% 0.22/0.47    ~! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)),
% 0.22/0.47    inference(negated_conjecture,[],[f7])).
% 0.22/0.47  fof(f7,conjecture,(
% 0.22/0.47    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).
% 0.22/0.47  % SZS output end Proof for theBenchmark
% 0.22/0.47  % (25493)------------------------------
% 0.22/0.47  % (25493)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (25493)Termination reason: Refutation
% 0.22/0.47  
% 0.22/0.47  % (25493)Memory used [KB]: 10618
% 0.22/0.47  % (25493)Time elapsed: 0.066 s
% 0.22/0.47  % (25493)------------------------------
% 0.22/0.47  % (25493)------------------------------
% 0.22/0.47  % (25500)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.47  % (25483)Success in time 0.107 s
%------------------------------------------------------------------------------
