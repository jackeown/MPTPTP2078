%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:11 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   48 (  62 expanded)
%              Number of leaves         :   14 (  28 expanded)
%              Depth                    :    6
%              Number of atoms          :  100 ( 136 expanded)
%              Number of equality atoms :   18 (  22 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f59,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f22,f27,f31,f35,f39,f44,f49,f54,f58])).

fof(f58,plain,
    ( spl1_1
    | ~ spl1_8 ),
    inference(avatar_contradiction_clause,[],[f57])).

fof(f57,plain,
    ( $false
    | spl1_1
    | ~ spl1_8 ),
    inference(trivial_inequality_removal,[],[f55])).

fof(f55,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl1_1
    | ~ spl1_8 ),
    inference(superposition,[],[f21,f53])).

fof(f53,plain,
    ( ! [X0] : k1_xboole_0 = k8_relat_1(X0,k1_xboole_0)
    | ~ spl1_8 ),
    inference(avatar_component_clause,[],[f52])).

fof(f52,plain,
    ( spl1_8
  <=> ! [X0] : k1_xboole_0 = k8_relat_1(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).

fof(f21,plain,
    ( k1_xboole_0 != k8_relat_1(sK0,k1_xboole_0)
    | spl1_1 ),
    inference(avatar_component_clause,[],[f19])).

fof(f19,plain,
    ( spl1_1
  <=> k1_xboole_0 = k8_relat_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f54,plain,
    ( spl1_8
    | ~ spl1_4
    | ~ spl1_7 ),
    inference(avatar_split_clause,[],[f50,f47,f33,f52])).

fof(f33,plain,
    ( spl1_4
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_xboole_0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f47,plain,
    ( spl1_7
  <=> ! [X0] : r1_tarski(k8_relat_1(X0,k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).

fof(f50,plain,
    ( ! [X0] : k1_xboole_0 = k8_relat_1(X0,k1_xboole_0)
    | ~ spl1_4
    | ~ spl1_7 ),
    inference(resolution,[],[f48,f34])).

fof(f34,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_xboole_0)
        | k1_xboole_0 = X0 )
    | ~ spl1_4 ),
    inference(avatar_component_clause,[],[f33])).

fof(f48,plain,
    ( ! [X0] : r1_tarski(k8_relat_1(X0,k1_xboole_0),k1_xboole_0)
    | ~ spl1_7 ),
    inference(avatar_component_clause,[],[f47])).

fof(f49,plain,
    ( spl1_7
    | ~ spl1_2
    | ~ spl1_6 ),
    inference(avatar_split_clause,[],[f45,f42,f24,f47])).

fof(f24,plain,
    ( spl1_2
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f42,plain,
    ( spl1_6
  <=> ! [X1,X0] :
        ( r1_tarski(k8_relat_1(X0,X1),X1)
        | ~ v1_xboole_0(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f45,plain,
    ( ! [X0] : r1_tarski(k8_relat_1(X0,k1_xboole_0),k1_xboole_0)
    | ~ spl1_2
    | ~ spl1_6 ),
    inference(resolution,[],[f43,f26])).

fof(f26,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl1_2 ),
    inference(avatar_component_clause,[],[f24])).

fof(f43,plain,
    ( ! [X0,X1] :
        ( ~ v1_xboole_0(X1)
        | r1_tarski(k8_relat_1(X0,X1),X1) )
    | ~ spl1_6 ),
    inference(avatar_component_clause,[],[f42])).

fof(f44,plain,
    ( spl1_6
    | ~ spl1_3
    | ~ spl1_5 ),
    inference(avatar_split_clause,[],[f40,f37,f29,f42])).

fof(f29,plain,
    ( spl1_3
  <=> ! [X0] :
        ( v1_relat_1(X0)
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f37,plain,
    ( spl1_5
  <=> ! [X1,X0] :
        ( r1_tarski(k8_relat_1(X0,X1),X1)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f40,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k8_relat_1(X0,X1),X1)
        | ~ v1_xboole_0(X1) )
    | ~ spl1_3
    | ~ spl1_5 ),
    inference(resolution,[],[f38,f30])).

fof(f30,plain,
    ( ! [X0] :
        ( v1_relat_1(X0)
        | ~ v1_xboole_0(X0) )
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f29])).

fof(f38,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | r1_tarski(k8_relat_1(X0,X1),X1) )
    | ~ spl1_5 ),
    inference(avatar_component_clause,[],[f37])).

fof(f39,plain,(
    spl1_5 ),
    inference(avatar_split_clause,[],[f17,f37])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(k8_relat_1(X0,X1),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_tarski(k8_relat_1(X0,X1),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k8_relat_1(X0,X1),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_relat_1)).

fof(f35,plain,(
    spl1_4 ),
    inference(avatar_split_clause,[],[f16,f33])).

fof(f16,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f31,plain,(
    spl1_3 ),
    inference(avatar_split_clause,[],[f15,f29])).

fof(f15,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f27,plain,(
    spl1_2 ),
    inference(avatar_split_clause,[],[f14,f24])).

fof(f14,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f22,plain,(
    ~ spl1_1 ),
    inference(avatar_split_clause,[],[f13,f19])).

fof(f13,plain,(
    k1_xboole_0 != k8_relat_1(sK0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    k1_xboole_0 != k8_relat_1(sK0,k1_xboole_0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f7,f11])).

fof(f11,plain,
    ( ? [X0] : k1_xboole_0 != k8_relat_1(X0,k1_xboole_0)
   => k1_xboole_0 != k8_relat_1(sK0,k1_xboole_0) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0] : k1_xboole_0 != k8_relat_1(X0,k1_xboole_0) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k8_relat_1(X0,k1_xboole_0) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] : k1_xboole_0 = k8_relat_1(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:37:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.42  % (27790)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.22/0.43  % (27787)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.22/0.43  % (27788)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.22/0.43  % (27787)Refutation found. Thanks to Tanya!
% 0.22/0.43  % SZS status Theorem for theBenchmark
% 0.22/0.43  % SZS output start Proof for theBenchmark
% 0.22/0.43  fof(f59,plain,(
% 0.22/0.43    $false),
% 0.22/0.43    inference(avatar_sat_refutation,[],[f22,f27,f31,f35,f39,f44,f49,f54,f58])).
% 0.22/0.43  fof(f58,plain,(
% 0.22/0.43    spl1_1 | ~spl1_8),
% 0.22/0.43    inference(avatar_contradiction_clause,[],[f57])).
% 0.22/0.43  fof(f57,plain,(
% 0.22/0.43    $false | (spl1_1 | ~spl1_8)),
% 0.22/0.43    inference(trivial_inequality_removal,[],[f55])).
% 0.22/0.43  fof(f55,plain,(
% 0.22/0.43    k1_xboole_0 != k1_xboole_0 | (spl1_1 | ~spl1_8)),
% 0.22/0.43    inference(superposition,[],[f21,f53])).
% 0.22/0.43  fof(f53,plain,(
% 0.22/0.43    ( ! [X0] : (k1_xboole_0 = k8_relat_1(X0,k1_xboole_0)) ) | ~spl1_8),
% 0.22/0.43    inference(avatar_component_clause,[],[f52])).
% 0.22/0.43  fof(f52,plain,(
% 0.22/0.43    spl1_8 <=> ! [X0] : k1_xboole_0 = k8_relat_1(X0,k1_xboole_0)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).
% 0.22/0.43  fof(f21,plain,(
% 0.22/0.43    k1_xboole_0 != k8_relat_1(sK0,k1_xboole_0) | spl1_1),
% 0.22/0.43    inference(avatar_component_clause,[],[f19])).
% 0.22/0.43  fof(f19,plain,(
% 0.22/0.43    spl1_1 <=> k1_xboole_0 = k8_relat_1(sK0,k1_xboole_0)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.22/0.43  fof(f54,plain,(
% 0.22/0.43    spl1_8 | ~spl1_4 | ~spl1_7),
% 0.22/0.43    inference(avatar_split_clause,[],[f50,f47,f33,f52])).
% 0.22/0.43  fof(f33,plain,(
% 0.22/0.43    spl1_4 <=> ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.22/0.43  fof(f47,plain,(
% 0.22/0.43    spl1_7 <=> ! [X0] : r1_tarski(k8_relat_1(X0,k1_xboole_0),k1_xboole_0)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).
% 0.22/0.43  fof(f50,plain,(
% 0.22/0.43    ( ! [X0] : (k1_xboole_0 = k8_relat_1(X0,k1_xboole_0)) ) | (~spl1_4 | ~spl1_7)),
% 0.22/0.43    inference(resolution,[],[f48,f34])).
% 0.22/0.43  fof(f34,plain,(
% 0.22/0.43    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) ) | ~spl1_4),
% 0.22/0.43    inference(avatar_component_clause,[],[f33])).
% 0.22/0.43  fof(f48,plain,(
% 0.22/0.43    ( ! [X0] : (r1_tarski(k8_relat_1(X0,k1_xboole_0),k1_xboole_0)) ) | ~spl1_7),
% 0.22/0.43    inference(avatar_component_clause,[],[f47])).
% 0.22/0.43  fof(f49,plain,(
% 0.22/0.43    spl1_7 | ~spl1_2 | ~spl1_6),
% 0.22/0.43    inference(avatar_split_clause,[],[f45,f42,f24,f47])).
% 0.22/0.43  fof(f24,plain,(
% 0.22/0.43    spl1_2 <=> v1_xboole_0(k1_xboole_0)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.22/0.43  fof(f42,plain,(
% 0.22/0.43    spl1_6 <=> ! [X1,X0] : (r1_tarski(k8_relat_1(X0,X1),X1) | ~v1_xboole_0(X1))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 0.22/0.43  fof(f45,plain,(
% 0.22/0.43    ( ! [X0] : (r1_tarski(k8_relat_1(X0,k1_xboole_0),k1_xboole_0)) ) | (~spl1_2 | ~spl1_6)),
% 0.22/0.43    inference(resolution,[],[f43,f26])).
% 0.22/0.43  fof(f26,plain,(
% 0.22/0.43    v1_xboole_0(k1_xboole_0) | ~spl1_2),
% 0.22/0.43    inference(avatar_component_clause,[],[f24])).
% 0.22/0.43  fof(f43,plain,(
% 0.22/0.43    ( ! [X0,X1] : (~v1_xboole_0(X1) | r1_tarski(k8_relat_1(X0,X1),X1)) ) | ~spl1_6),
% 0.22/0.43    inference(avatar_component_clause,[],[f42])).
% 0.22/0.43  fof(f44,plain,(
% 0.22/0.43    spl1_6 | ~spl1_3 | ~spl1_5),
% 0.22/0.43    inference(avatar_split_clause,[],[f40,f37,f29,f42])).
% 0.22/0.43  fof(f29,plain,(
% 0.22/0.43    spl1_3 <=> ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.22/0.43  fof(f37,plain,(
% 0.22/0.43    spl1_5 <=> ! [X1,X0] : (r1_tarski(k8_relat_1(X0,X1),X1) | ~v1_relat_1(X1))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.22/0.43  fof(f40,plain,(
% 0.22/0.43    ( ! [X0,X1] : (r1_tarski(k8_relat_1(X0,X1),X1) | ~v1_xboole_0(X1)) ) | (~spl1_3 | ~spl1_5)),
% 0.22/0.43    inference(resolution,[],[f38,f30])).
% 0.22/0.43  fof(f30,plain,(
% 0.22/0.43    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) ) | ~spl1_3),
% 0.22/0.43    inference(avatar_component_clause,[],[f29])).
% 0.22/0.43  fof(f38,plain,(
% 0.22/0.43    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k8_relat_1(X0,X1),X1)) ) | ~spl1_5),
% 0.22/0.43    inference(avatar_component_clause,[],[f37])).
% 0.22/0.43  fof(f39,plain,(
% 0.22/0.43    spl1_5),
% 0.22/0.43    inference(avatar_split_clause,[],[f17,f37])).
% 0.22/0.43  fof(f17,plain,(
% 0.22/0.43    ( ! [X0,X1] : (r1_tarski(k8_relat_1(X0,X1),X1) | ~v1_relat_1(X1)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f10])).
% 0.22/0.43  fof(f10,plain,(
% 0.22/0.43    ! [X0,X1] : (r1_tarski(k8_relat_1(X0,X1),X1) | ~v1_relat_1(X1))),
% 0.22/0.43    inference(ennf_transformation,[],[f4])).
% 0.22/0.43  fof(f4,axiom,(
% 0.22/0.43    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k8_relat_1(X0,X1),X1))),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_relat_1)).
% 0.22/0.43  fof(f35,plain,(
% 0.22/0.43    spl1_4),
% 0.22/0.43    inference(avatar_split_clause,[],[f16,f33])).
% 0.22/0.43  fof(f16,plain,(
% 0.22/0.43    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f9])).
% 0.22/0.43  fof(f9,plain,(
% 0.22/0.43    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.22/0.43    inference(ennf_transformation,[],[f2])).
% 0.22/0.43  fof(f2,axiom,(
% 0.22/0.43    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.22/0.43  fof(f31,plain,(
% 0.22/0.43    spl1_3),
% 0.22/0.43    inference(avatar_split_clause,[],[f15,f29])).
% 0.22/0.43  fof(f15,plain,(
% 0.22/0.43    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f8])).
% 0.22/0.43  fof(f8,plain,(
% 0.22/0.43    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 0.22/0.43    inference(ennf_transformation,[],[f3])).
% 0.22/0.43  fof(f3,axiom,(
% 0.22/0.43    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).
% 0.22/0.43  fof(f27,plain,(
% 0.22/0.43    spl1_2),
% 0.22/0.43    inference(avatar_split_clause,[],[f14,f24])).
% 0.22/0.43  fof(f14,plain,(
% 0.22/0.43    v1_xboole_0(k1_xboole_0)),
% 0.22/0.43    inference(cnf_transformation,[],[f1])).
% 0.22/0.43  fof(f1,axiom,(
% 0.22/0.43    v1_xboole_0(k1_xboole_0)),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.43  fof(f22,plain,(
% 0.22/0.43    ~spl1_1),
% 0.22/0.43    inference(avatar_split_clause,[],[f13,f19])).
% 0.22/0.43  fof(f13,plain,(
% 0.22/0.43    k1_xboole_0 != k8_relat_1(sK0,k1_xboole_0)),
% 0.22/0.43    inference(cnf_transformation,[],[f12])).
% 0.22/0.43  fof(f12,plain,(
% 0.22/0.43    k1_xboole_0 != k8_relat_1(sK0,k1_xboole_0)),
% 0.22/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f7,f11])).
% 0.22/0.43  fof(f11,plain,(
% 0.22/0.43    ? [X0] : k1_xboole_0 != k8_relat_1(X0,k1_xboole_0) => k1_xboole_0 != k8_relat_1(sK0,k1_xboole_0)),
% 0.22/0.43    introduced(choice_axiom,[])).
% 0.22/0.43  fof(f7,plain,(
% 0.22/0.43    ? [X0] : k1_xboole_0 != k8_relat_1(X0,k1_xboole_0)),
% 0.22/0.43    inference(ennf_transformation,[],[f6])).
% 0.22/0.43  fof(f6,negated_conjecture,(
% 0.22/0.43    ~! [X0] : k1_xboole_0 = k8_relat_1(X0,k1_xboole_0)),
% 0.22/0.43    inference(negated_conjecture,[],[f5])).
% 0.22/0.43  fof(f5,conjecture,(
% 0.22/0.43    ! [X0] : k1_xboole_0 = k8_relat_1(X0,k1_xboole_0)),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_relat_1)).
% 0.22/0.43  % SZS output end Proof for theBenchmark
% 0.22/0.43  % (27787)------------------------------
% 0.22/0.43  % (27787)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.43  % (27787)Termination reason: Refutation
% 0.22/0.43  
% 0.22/0.43  % (27787)Memory used [KB]: 10490
% 0.22/0.43  % (27787)Time elapsed: 0.005 s
% 0.22/0.43  % (27787)------------------------------
% 0.22/0.43  % (27787)------------------------------
% 0.22/0.43  % (27781)Success in time 0.076 s
%------------------------------------------------------------------------------
