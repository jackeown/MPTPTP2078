%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:13 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   54 (  67 expanded)
%              Number of leaves         :   16 (  29 expanded)
%              Depth                    :    6
%              Number of atoms          :  111 ( 142 expanded)
%              Number of equality atoms :   23 (  29 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f77,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f25,f30,f40,f44,f48,f52,f61,f64,f69,f74])).

fof(f74,plain,
    ( spl1_1
    | ~ spl1_10 ),
    inference(avatar_contradiction_clause,[],[f73])).

fof(f73,plain,
    ( $false
    | spl1_1
    | ~ spl1_10 ),
    inference(trivial_inequality_removal,[],[f70])).

fof(f70,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl1_1
    | ~ spl1_10 ),
    inference(superposition,[],[f24,f68])).

fof(f68,plain,
    ( ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)
    | ~ spl1_10 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl1_10
  <=> ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).

fof(f24,plain,
    ( k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0)
    | spl1_1 ),
    inference(avatar_component_clause,[],[f22])).

fof(f22,plain,
    ( spl1_1
  <=> k1_xboole_0 = k10_relat_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f69,plain,
    ( spl1_10
    | ~ spl1_6
    | ~ spl1_9 ),
    inference(avatar_split_clause,[],[f65,f59,f46,f67])).

fof(f46,plain,
    ( spl1_6
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_xboole_0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f59,plain,
    ( spl1_9
  <=> ! [X0] : r1_tarski(k10_relat_1(k1_xboole_0,X0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).

fof(f65,plain,
    ( ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)
    | ~ spl1_6
    | ~ spl1_9 ),
    inference(resolution,[],[f60,f47])).

fof(f47,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_xboole_0)
        | k1_xboole_0 = X0 )
    | ~ spl1_6 ),
    inference(avatar_component_clause,[],[f46])).

fof(f60,plain,
    ( ! [X0] : r1_tarski(k10_relat_1(k1_xboole_0,X0),k1_xboole_0)
    | ~ spl1_9 ),
    inference(avatar_component_clause,[],[f59])).

fof(f64,plain,
    ( ~ spl1_2
    | ~ spl1_5
    | spl1_8 ),
    inference(avatar_contradiction_clause,[],[f63])).

fof(f63,plain,
    ( $false
    | ~ spl1_2
    | ~ spl1_5
    | spl1_8 ),
    inference(subsumption_resolution,[],[f62,f29])).

fof(f29,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl1_2 ),
    inference(avatar_component_clause,[],[f27])).

fof(f27,plain,
    ( spl1_2
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f62,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl1_5
    | spl1_8 ),
    inference(resolution,[],[f57,f43])).

fof(f43,plain,
    ( ! [X0] :
        ( v1_relat_1(X0)
        | ~ v1_xboole_0(X0) )
    | ~ spl1_5 ),
    inference(avatar_component_clause,[],[f42])).

fof(f42,plain,
    ( spl1_5
  <=> ! [X0] :
        ( v1_relat_1(X0)
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f57,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl1_8 ),
    inference(avatar_component_clause,[],[f55])).

fof(f55,plain,
    ( spl1_8
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).

fof(f61,plain,
    ( ~ spl1_8
    | spl1_9
    | ~ spl1_4
    | ~ spl1_7 ),
    inference(avatar_split_clause,[],[f53,f50,f37,f59,f55])).

fof(f37,plain,
    ( spl1_4
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f50,plain,
    ( spl1_7
  <=> ! [X1,X0] :
        ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).

fof(f53,plain,
    ( ! [X0] :
        ( r1_tarski(k10_relat_1(k1_xboole_0,X0),k1_xboole_0)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl1_4
    | ~ spl1_7 ),
    inference(superposition,[],[f51,f39])).

fof(f39,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl1_4 ),
    inference(avatar_component_clause,[],[f37])).

fof(f51,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
        | ~ v1_relat_1(X1) )
    | ~ spl1_7 ),
    inference(avatar_component_clause,[],[f50])).

fof(f52,plain,(
    spl1_7 ),
    inference(avatar_split_clause,[],[f20,f50])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

fof(f48,plain,(
    spl1_6 ),
    inference(avatar_split_clause,[],[f19,f46])).

fof(f19,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f44,plain,(
    spl1_5 ),
    inference(avatar_split_clause,[],[f18,f42])).

fof(f18,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f40,plain,(
    spl1_4 ),
    inference(avatar_split_clause,[],[f16,f37])).

fof(f16,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f30,plain,(
    spl1_2 ),
    inference(avatar_split_clause,[],[f15,f27])).

fof(f15,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f25,plain,(
    ~ spl1_1 ),
    inference(avatar_split_clause,[],[f14,f22])).

fof(f14,plain,(
    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f8,f12])).

fof(f12,plain,
    ( ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0)
   => k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n020.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:35:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.41  % (26862)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.22/0.41  % (26864)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.22/0.41  % (26863)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.22/0.42  % (26865)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.22/0.42  % (26860)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.22/0.42  % (26860)Refutation found. Thanks to Tanya!
% 0.22/0.42  % SZS status Theorem for theBenchmark
% 0.22/0.42  % SZS output start Proof for theBenchmark
% 0.22/0.42  fof(f77,plain,(
% 0.22/0.42    $false),
% 0.22/0.42    inference(avatar_sat_refutation,[],[f25,f30,f40,f44,f48,f52,f61,f64,f69,f74])).
% 0.22/0.42  fof(f74,plain,(
% 0.22/0.42    spl1_1 | ~spl1_10),
% 0.22/0.42    inference(avatar_contradiction_clause,[],[f73])).
% 0.22/0.42  fof(f73,plain,(
% 0.22/0.42    $false | (spl1_1 | ~spl1_10)),
% 0.22/0.42    inference(trivial_inequality_removal,[],[f70])).
% 0.22/0.42  fof(f70,plain,(
% 0.22/0.42    k1_xboole_0 != k1_xboole_0 | (spl1_1 | ~spl1_10)),
% 0.22/0.42    inference(superposition,[],[f24,f68])).
% 0.22/0.42  fof(f68,plain,(
% 0.22/0.42    ( ! [X0] : (k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)) ) | ~spl1_10),
% 0.22/0.42    inference(avatar_component_clause,[],[f67])).
% 0.22/0.42  fof(f67,plain,(
% 0.22/0.42    spl1_10 <=> ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).
% 0.22/0.42  fof(f24,plain,(
% 0.22/0.42    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0) | spl1_1),
% 0.22/0.42    inference(avatar_component_clause,[],[f22])).
% 0.22/0.42  fof(f22,plain,(
% 0.22/0.42    spl1_1 <=> k1_xboole_0 = k10_relat_1(k1_xboole_0,sK0)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.22/0.42  fof(f69,plain,(
% 0.22/0.42    spl1_10 | ~spl1_6 | ~spl1_9),
% 0.22/0.42    inference(avatar_split_clause,[],[f65,f59,f46,f67])).
% 0.22/0.42  fof(f46,plain,(
% 0.22/0.42    spl1_6 <=> ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 0.22/0.42  fof(f59,plain,(
% 0.22/0.42    spl1_9 <=> ! [X0] : r1_tarski(k10_relat_1(k1_xboole_0,X0),k1_xboole_0)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).
% 0.22/0.42  fof(f65,plain,(
% 0.22/0.42    ( ! [X0] : (k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)) ) | (~spl1_6 | ~spl1_9)),
% 0.22/0.42    inference(resolution,[],[f60,f47])).
% 0.22/0.42  fof(f47,plain,(
% 0.22/0.42    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) ) | ~spl1_6),
% 0.22/0.42    inference(avatar_component_clause,[],[f46])).
% 0.22/0.42  fof(f60,plain,(
% 0.22/0.42    ( ! [X0] : (r1_tarski(k10_relat_1(k1_xboole_0,X0),k1_xboole_0)) ) | ~spl1_9),
% 0.22/0.42    inference(avatar_component_clause,[],[f59])).
% 0.22/0.42  fof(f64,plain,(
% 0.22/0.42    ~spl1_2 | ~spl1_5 | spl1_8),
% 0.22/0.42    inference(avatar_contradiction_clause,[],[f63])).
% 0.22/0.42  fof(f63,plain,(
% 0.22/0.42    $false | (~spl1_2 | ~spl1_5 | spl1_8)),
% 0.22/0.42    inference(subsumption_resolution,[],[f62,f29])).
% 0.22/0.42  fof(f29,plain,(
% 0.22/0.42    v1_xboole_0(k1_xboole_0) | ~spl1_2),
% 0.22/0.42    inference(avatar_component_clause,[],[f27])).
% 0.22/0.42  fof(f27,plain,(
% 0.22/0.42    spl1_2 <=> v1_xboole_0(k1_xboole_0)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.22/0.42  fof(f62,plain,(
% 0.22/0.42    ~v1_xboole_0(k1_xboole_0) | (~spl1_5 | spl1_8)),
% 0.22/0.42    inference(resolution,[],[f57,f43])).
% 0.22/0.42  fof(f43,plain,(
% 0.22/0.42    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) ) | ~spl1_5),
% 0.22/0.42    inference(avatar_component_clause,[],[f42])).
% 0.22/0.42  fof(f42,plain,(
% 0.22/0.42    spl1_5 <=> ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.22/0.42  fof(f57,plain,(
% 0.22/0.42    ~v1_relat_1(k1_xboole_0) | spl1_8),
% 0.22/0.42    inference(avatar_component_clause,[],[f55])).
% 0.22/0.42  fof(f55,plain,(
% 0.22/0.42    spl1_8 <=> v1_relat_1(k1_xboole_0)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).
% 0.22/0.42  fof(f61,plain,(
% 0.22/0.42    ~spl1_8 | spl1_9 | ~spl1_4 | ~spl1_7),
% 0.22/0.42    inference(avatar_split_clause,[],[f53,f50,f37,f59,f55])).
% 0.22/0.42  fof(f37,plain,(
% 0.22/0.42    spl1_4 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.22/0.42  fof(f50,plain,(
% 0.22/0.42    spl1_7 <=> ! [X1,X0] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).
% 0.22/0.42  fof(f53,plain,(
% 0.22/0.42    ( ! [X0] : (r1_tarski(k10_relat_1(k1_xboole_0,X0),k1_xboole_0) | ~v1_relat_1(k1_xboole_0)) ) | (~spl1_4 | ~spl1_7)),
% 0.22/0.42    inference(superposition,[],[f51,f39])).
% 0.22/0.42  fof(f39,plain,(
% 0.22/0.42    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl1_4),
% 0.22/0.42    inference(avatar_component_clause,[],[f37])).
% 0.22/0.42  fof(f51,plain,(
% 0.22/0.42    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) ) | ~spl1_7),
% 0.22/0.42    inference(avatar_component_clause,[],[f50])).
% 0.22/0.42  fof(f52,plain,(
% 0.22/0.42    spl1_7),
% 0.22/0.42    inference(avatar_split_clause,[],[f20,f50])).
% 0.22/0.42  fof(f20,plain,(
% 0.22/0.42    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.22/0.42    inference(cnf_transformation,[],[f11])).
% 0.22/0.42  fof(f11,plain,(
% 0.22/0.42    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.22/0.42    inference(ennf_transformation,[],[f4])).
% 0.22/0.42  fof(f4,axiom,(
% 0.22/0.42    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).
% 0.22/0.42  fof(f48,plain,(
% 0.22/0.42    spl1_6),
% 0.22/0.42    inference(avatar_split_clause,[],[f19,f46])).
% 0.22/0.42  fof(f19,plain,(
% 0.22/0.42    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 0.22/0.42    inference(cnf_transformation,[],[f10])).
% 0.22/0.42  fof(f10,plain,(
% 0.22/0.42    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.22/0.42    inference(ennf_transformation,[],[f2])).
% 0.22/0.42  fof(f2,axiom,(
% 0.22/0.42    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.22/0.42  fof(f44,plain,(
% 0.22/0.42    spl1_5),
% 0.22/0.42    inference(avatar_split_clause,[],[f18,f42])).
% 0.22/0.42  fof(f18,plain,(
% 0.22/0.42    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 0.22/0.42    inference(cnf_transformation,[],[f9])).
% 0.22/0.42  fof(f9,plain,(
% 0.22/0.42    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 0.22/0.42    inference(ennf_transformation,[],[f3])).
% 0.22/0.42  fof(f3,axiom,(
% 0.22/0.42    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).
% 0.22/0.42  fof(f40,plain,(
% 0.22/0.42    spl1_4),
% 0.22/0.42    inference(avatar_split_clause,[],[f16,f37])).
% 0.22/0.42  fof(f16,plain,(
% 0.22/0.42    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.42    inference(cnf_transformation,[],[f5])).
% 0.22/0.42  fof(f5,axiom,(
% 0.22/0.42    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.22/0.42  fof(f30,plain,(
% 0.22/0.42    spl1_2),
% 0.22/0.42    inference(avatar_split_clause,[],[f15,f27])).
% 0.22/0.42  fof(f15,plain,(
% 0.22/0.42    v1_xboole_0(k1_xboole_0)),
% 0.22/0.42    inference(cnf_transformation,[],[f1])).
% 0.22/0.42  fof(f1,axiom,(
% 0.22/0.42    v1_xboole_0(k1_xboole_0)),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.42  fof(f25,plain,(
% 0.22/0.42    ~spl1_1),
% 0.22/0.42    inference(avatar_split_clause,[],[f14,f22])).
% 0.22/0.42  fof(f14,plain,(
% 0.22/0.42    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0)),
% 0.22/0.42    inference(cnf_transformation,[],[f13])).
% 0.22/0.42  fof(f13,plain,(
% 0.22/0.42    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0)),
% 0.22/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f8,f12])).
% 0.22/0.42  fof(f12,plain,(
% 0.22/0.42    ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0) => k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0)),
% 0.22/0.42    introduced(choice_axiom,[])).
% 0.22/0.42  fof(f8,plain,(
% 0.22/0.42    ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0)),
% 0.22/0.42    inference(ennf_transformation,[],[f7])).
% 0.22/0.42  fof(f7,negated_conjecture,(
% 0.22/0.42    ~! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)),
% 0.22/0.42    inference(negated_conjecture,[],[f6])).
% 0.22/0.42  fof(f6,conjecture,(
% 0.22/0.42    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).
% 0.22/0.42  % SZS output end Proof for theBenchmark
% 0.22/0.42  % (26860)------------------------------
% 0.22/0.42  % (26860)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.42  % (26860)Termination reason: Refutation
% 0.22/0.42  
% 0.22/0.42  % (26860)Memory used [KB]: 10490
% 0.22/0.42  % (26860)Time elapsed: 0.004 s
% 0.22/0.42  % (26860)------------------------------
% 0.22/0.42  % (26860)------------------------------
% 0.22/0.42  % (26859)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.22/0.42  % (26854)Success in time 0.055 s
%------------------------------------------------------------------------------
