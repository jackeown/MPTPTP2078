%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:24 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   59 (  77 expanded)
%              Number of leaves         :   18 (  36 expanded)
%              Depth                    :    6
%              Number of atoms          :  117 ( 157 expanded)
%              Number of equality atoms :   32 (  42 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f88,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f26,f31,f41,f45,f49,f53,f57,f63,f69,f80,f85])).

fof(f85,plain,
    ( spl1_1
    | ~ spl1_12 ),
    inference(avatar_contradiction_clause,[],[f84])).

fof(f84,plain,
    ( $false
    | spl1_1
    | ~ spl1_12 ),
    inference(trivial_inequality_removal,[],[f81])).

fof(f81,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl1_1
    | ~ spl1_12 ),
    inference(superposition,[],[f25,f79])).

fof(f79,plain,
    ( ! [X2] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X2)
    | ~ spl1_12 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl1_12
  <=> ! [X2] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_12])])).

fof(f25,plain,
    ( k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0)
    | spl1_1 ),
    inference(avatar_component_clause,[],[f23])).

fof(f23,plain,
    ( spl1_1
  <=> k1_xboole_0 = k10_relat_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f80,plain,
    ( spl1_12
    | ~ spl1_6
    | ~ spl1_8
    | ~ spl1_10 ),
    inference(avatar_split_clause,[],[f76,f67,f55,f47,f78])).

fof(f47,plain,
    ( spl1_6
  <=> ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f55,plain,
    ( spl1_8
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).

fof(f67,plain,
    ( spl1_10
  <=> ! [X0] : r1_tarski(k10_relat_1(k1_xboole_0,X0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).

fof(f76,plain,
    ( ! [X2] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X2)
    | ~ spl1_6
    | ~ spl1_8
    | ~ spl1_10 ),
    inference(forward_demodulation,[],[f71,f48])).

fof(f48,plain,
    ( ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)
    | ~ spl1_6 ),
    inference(avatar_component_clause,[],[f47])).

fof(f71,plain,
    ( ! [X2] : k10_relat_1(k1_xboole_0,X2) = k3_xboole_0(k10_relat_1(k1_xboole_0,X2),k1_xboole_0)
    | ~ spl1_8
    | ~ spl1_10 ),
    inference(resolution,[],[f56,f68])).

fof(f68,plain,
    ( ! [X0] : r1_tarski(k10_relat_1(k1_xboole_0,X0),k1_xboole_0)
    | ~ spl1_10 ),
    inference(avatar_component_clause,[],[f67])).

fof(f56,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k3_xboole_0(X0,X1) = X0 )
    | ~ spl1_8 ),
    inference(avatar_component_clause,[],[f55])).

fof(f69,plain,
    ( spl1_10
    | ~ spl1_4
    | ~ spl1_7
    | ~ spl1_9 ),
    inference(avatar_split_clause,[],[f65,f60,f51,f38,f67])).

fof(f38,plain,
    ( spl1_4
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f51,plain,
    ( spl1_7
  <=> ! [X1,X0] :
        ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).

fof(f60,plain,
    ( spl1_9
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).

fof(f65,plain,
    ( ! [X0] : r1_tarski(k10_relat_1(k1_xboole_0,X0),k1_xboole_0)
    | ~ spl1_4
    | ~ spl1_7
    | ~ spl1_9 ),
    inference(subsumption_resolution,[],[f64,f62])).

fof(f62,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl1_9 ),
    inference(avatar_component_clause,[],[f60])).

fof(f64,plain,
    ( ! [X0] :
        ( r1_tarski(k10_relat_1(k1_xboole_0,X0),k1_xboole_0)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl1_4
    | ~ spl1_7 ),
    inference(superposition,[],[f52,f40])).

fof(f40,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl1_4 ),
    inference(avatar_component_clause,[],[f38])).

fof(f52,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
        | ~ v1_relat_1(X1) )
    | ~ spl1_7 ),
    inference(avatar_component_clause,[],[f51])).

fof(f63,plain,
    ( spl1_9
    | ~ spl1_2
    | ~ spl1_5 ),
    inference(avatar_split_clause,[],[f58,f43,f28,f60])).

fof(f28,plain,
    ( spl1_2
  <=> k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f43,plain,
    ( spl1_5
  <=> ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f58,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl1_2
    | ~ spl1_5 ),
    inference(superposition,[],[f44,f30])).

fof(f30,plain,
    ( k1_xboole_0 = k6_relat_1(k1_xboole_0)
    | ~ spl1_2 ),
    inference(avatar_component_clause,[],[f28])).

fof(f44,plain,
    ( ! [X0] : v1_relat_1(k6_relat_1(X0))
    | ~ spl1_5 ),
    inference(avatar_component_clause,[],[f43])).

fof(f57,plain,(
    spl1_8 ),
    inference(avatar_split_clause,[],[f21,f55])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f53,plain,(
    spl1_7 ),
    inference(avatar_split_clause,[],[f20,f51])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

fof(f49,plain,(
    spl1_6 ),
    inference(avatar_split_clause,[],[f19,f47])).

fof(f19,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f45,plain,(
    spl1_5 ),
    inference(avatar_split_clause,[],[f18,f43])).

fof(f18,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f41,plain,(
    spl1_4 ),
    inference(avatar_split_clause,[],[f16,f38])).

fof(f16,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f31,plain,(
    spl1_2 ),
    inference(avatar_split_clause,[],[f15,f28])).

fof(f15,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

fof(f26,plain,(
    ~ spl1_1 ),
    inference(avatar_split_clause,[],[f14,f23])).

fof(f14,plain,(
    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f12])).

fof(f12,plain,
    ( ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0)
   => k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0) ),
    introduced(choice_axiom,[])).

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
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:43:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.41  % (22652)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.20/0.41  % (22649)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.20/0.41  % (22650)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.20/0.41  % (22649)Refutation found. Thanks to Tanya!
% 0.20/0.41  % SZS status Theorem for theBenchmark
% 0.20/0.41  % SZS output start Proof for theBenchmark
% 0.20/0.41  fof(f88,plain,(
% 0.20/0.41    $false),
% 0.20/0.41    inference(avatar_sat_refutation,[],[f26,f31,f41,f45,f49,f53,f57,f63,f69,f80,f85])).
% 0.20/0.41  fof(f85,plain,(
% 0.20/0.41    spl1_1 | ~spl1_12),
% 0.20/0.41    inference(avatar_contradiction_clause,[],[f84])).
% 0.20/0.41  fof(f84,plain,(
% 0.20/0.41    $false | (spl1_1 | ~spl1_12)),
% 0.20/0.41    inference(trivial_inequality_removal,[],[f81])).
% 0.20/0.41  fof(f81,plain,(
% 0.20/0.41    k1_xboole_0 != k1_xboole_0 | (spl1_1 | ~spl1_12)),
% 0.20/0.41    inference(superposition,[],[f25,f79])).
% 0.20/0.41  fof(f79,plain,(
% 0.20/0.41    ( ! [X2] : (k1_xboole_0 = k10_relat_1(k1_xboole_0,X2)) ) | ~spl1_12),
% 0.20/0.41    inference(avatar_component_clause,[],[f78])).
% 0.20/0.41  fof(f78,plain,(
% 0.20/0.41    spl1_12 <=> ! [X2] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X2)),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl1_12])])).
% 0.20/0.41  fof(f25,plain,(
% 0.20/0.41    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0) | spl1_1),
% 0.20/0.41    inference(avatar_component_clause,[],[f23])).
% 0.20/0.41  fof(f23,plain,(
% 0.20/0.41    spl1_1 <=> k1_xboole_0 = k10_relat_1(k1_xboole_0,sK0)),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.20/0.41  fof(f80,plain,(
% 0.20/0.41    spl1_12 | ~spl1_6 | ~spl1_8 | ~spl1_10),
% 0.20/0.41    inference(avatar_split_clause,[],[f76,f67,f55,f47,f78])).
% 0.20/0.41  fof(f47,plain,(
% 0.20/0.41    spl1_6 <=> ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 0.20/0.41  fof(f55,plain,(
% 0.20/0.41    spl1_8 <=> ! [X1,X0] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).
% 0.20/0.41  fof(f67,plain,(
% 0.20/0.41    spl1_10 <=> ! [X0] : r1_tarski(k10_relat_1(k1_xboole_0,X0),k1_xboole_0)),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).
% 0.20/0.41  fof(f76,plain,(
% 0.20/0.41    ( ! [X2] : (k1_xboole_0 = k10_relat_1(k1_xboole_0,X2)) ) | (~spl1_6 | ~spl1_8 | ~spl1_10)),
% 0.20/0.41    inference(forward_demodulation,[],[f71,f48])).
% 0.20/0.41  fof(f48,plain,(
% 0.20/0.41    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) ) | ~spl1_6),
% 0.20/0.41    inference(avatar_component_clause,[],[f47])).
% 0.20/0.41  fof(f71,plain,(
% 0.20/0.41    ( ! [X2] : (k10_relat_1(k1_xboole_0,X2) = k3_xboole_0(k10_relat_1(k1_xboole_0,X2),k1_xboole_0)) ) | (~spl1_8 | ~spl1_10)),
% 0.20/0.41    inference(resolution,[],[f56,f68])).
% 0.20/0.41  fof(f68,plain,(
% 0.20/0.41    ( ! [X0] : (r1_tarski(k10_relat_1(k1_xboole_0,X0),k1_xboole_0)) ) | ~spl1_10),
% 0.20/0.41    inference(avatar_component_clause,[],[f67])).
% 0.20/0.41  fof(f56,plain,(
% 0.20/0.41    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) ) | ~spl1_8),
% 0.20/0.41    inference(avatar_component_clause,[],[f55])).
% 0.20/0.41  fof(f69,plain,(
% 0.20/0.41    spl1_10 | ~spl1_4 | ~spl1_7 | ~spl1_9),
% 0.20/0.41    inference(avatar_split_clause,[],[f65,f60,f51,f38,f67])).
% 0.20/0.41  fof(f38,plain,(
% 0.20/0.41    spl1_4 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.20/0.41  fof(f51,plain,(
% 0.20/0.41    spl1_7 <=> ! [X1,X0] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).
% 0.20/0.41  fof(f60,plain,(
% 0.20/0.41    spl1_9 <=> v1_relat_1(k1_xboole_0)),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).
% 0.20/0.41  fof(f65,plain,(
% 0.20/0.41    ( ! [X0] : (r1_tarski(k10_relat_1(k1_xboole_0,X0),k1_xboole_0)) ) | (~spl1_4 | ~spl1_7 | ~spl1_9)),
% 0.20/0.41    inference(subsumption_resolution,[],[f64,f62])).
% 0.20/0.41  fof(f62,plain,(
% 0.20/0.41    v1_relat_1(k1_xboole_0) | ~spl1_9),
% 0.20/0.41    inference(avatar_component_clause,[],[f60])).
% 0.20/0.41  fof(f64,plain,(
% 0.20/0.41    ( ! [X0] : (r1_tarski(k10_relat_1(k1_xboole_0,X0),k1_xboole_0) | ~v1_relat_1(k1_xboole_0)) ) | (~spl1_4 | ~spl1_7)),
% 0.20/0.41    inference(superposition,[],[f52,f40])).
% 0.20/0.41  fof(f40,plain,(
% 0.20/0.41    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl1_4),
% 0.20/0.41    inference(avatar_component_clause,[],[f38])).
% 0.20/0.41  fof(f52,plain,(
% 0.20/0.41    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) ) | ~spl1_7),
% 0.20/0.41    inference(avatar_component_clause,[],[f51])).
% 0.20/0.41  fof(f63,plain,(
% 0.20/0.41    spl1_9 | ~spl1_2 | ~spl1_5),
% 0.20/0.41    inference(avatar_split_clause,[],[f58,f43,f28,f60])).
% 0.20/0.41  fof(f28,plain,(
% 0.20/0.41    spl1_2 <=> k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.20/0.41  fof(f43,plain,(
% 0.20/0.41    spl1_5 <=> ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.20/0.41  fof(f58,plain,(
% 0.20/0.41    v1_relat_1(k1_xboole_0) | (~spl1_2 | ~spl1_5)),
% 0.20/0.41    inference(superposition,[],[f44,f30])).
% 0.20/0.41  fof(f30,plain,(
% 0.20/0.41    k1_xboole_0 = k6_relat_1(k1_xboole_0) | ~spl1_2),
% 0.20/0.41    inference(avatar_component_clause,[],[f28])).
% 0.20/0.41  fof(f44,plain,(
% 0.20/0.41    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) ) | ~spl1_5),
% 0.20/0.41    inference(avatar_component_clause,[],[f43])).
% 0.20/0.41  fof(f57,plain,(
% 0.20/0.41    spl1_8),
% 0.20/0.41    inference(avatar_split_clause,[],[f21,f55])).
% 0.20/0.41  fof(f21,plain,(
% 0.20/0.41    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.20/0.41    inference(cnf_transformation,[],[f11])).
% 0.20/0.41  fof(f11,plain,(
% 0.20/0.41    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.20/0.41    inference(ennf_transformation,[],[f1])).
% 0.20/0.41  fof(f1,axiom,(
% 0.20/0.41    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.20/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.20/0.41  fof(f53,plain,(
% 0.20/0.41    spl1_7),
% 0.20/0.41    inference(avatar_split_clause,[],[f20,f51])).
% 0.20/0.41  fof(f20,plain,(
% 0.20/0.41    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.20/0.41    inference(cnf_transformation,[],[f10])).
% 0.20/0.41  fof(f10,plain,(
% 0.20/0.41    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.20/0.41    inference(ennf_transformation,[],[f4])).
% 0.20/0.41  fof(f4,axiom,(
% 0.20/0.41    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 0.20/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).
% 0.20/0.41  fof(f49,plain,(
% 0.20/0.41    spl1_6),
% 0.20/0.41    inference(avatar_split_clause,[],[f19,f47])).
% 0.20/0.41  fof(f19,plain,(
% 0.20/0.41    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.20/0.41    inference(cnf_transformation,[],[f2])).
% 0.20/0.41  fof(f2,axiom,(
% 0.20/0.41    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.20/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 0.20/0.41  fof(f45,plain,(
% 0.20/0.41    spl1_5),
% 0.20/0.41    inference(avatar_split_clause,[],[f18,f43])).
% 0.20/0.41  fof(f18,plain,(
% 0.20/0.41    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.20/0.41    inference(cnf_transformation,[],[f3])).
% 0.20/0.41  fof(f3,axiom,(
% 0.20/0.41    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.20/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.20/0.41  fof(f41,plain,(
% 0.20/0.41    spl1_4),
% 0.20/0.41    inference(avatar_split_clause,[],[f16,f38])).
% 0.20/0.41  fof(f16,plain,(
% 0.20/0.41    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.41    inference(cnf_transformation,[],[f5])).
% 0.20/0.41  fof(f5,axiom,(
% 0.20/0.41    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.20/0.41  fof(f31,plain,(
% 0.20/0.41    spl1_2),
% 0.20/0.41    inference(avatar_split_clause,[],[f15,f28])).
% 0.20/0.41  fof(f15,plain,(
% 0.20/0.41    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.20/0.41    inference(cnf_transformation,[],[f6])).
% 0.20/0.41  fof(f6,axiom,(
% 0.20/0.41    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.20/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).
% 0.20/0.41  fof(f26,plain,(
% 0.20/0.41    ~spl1_1),
% 0.20/0.41    inference(avatar_split_clause,[],[f14,f23])).
% 0.20/0.41  fof(f14,plain,(
% 0.20/0.41    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0)),
% 0.20/0.41    inference(cnf_transformation,[],[f13])).
% 0.20/0.41  fof(f13,plain,(
% 0.20/0.41    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0)),
% 0.20/0.41    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f12])).
% 0.20/0.41  fof(f12,plain,(
% 0.20/0.41    ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0) => k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0)),
% 0.20/0.41    introduced(choice_axiom,[])).
% 0.20/0.41  fof(f9,plain,(
% 0.20/0.41    ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0)),
% 0.20/0.41    inference(ennf_transformation,[],[f8])).
% 0.20/0.41  fof(f8,negated_conjecture,(
% 0.20/0.41    ~! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)),
% 0.20/0.41    inference(negated_conjecture,[],[f7])).
% 0.20/0.41  fof(f7,conjecture,(
% 0.20/0.41    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)),
% 0.20/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).
% 0.20/0.41  % SZS output end Proof for theBenchmark
% 0.20/0.41  % (22649)------------------------------
% 0.20/0.41  % (22649)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.41  % (22649)Termination reason: Refutation
% 0.20/0.41  
% 0.20/0.41  % (22649)Memory used [KB]: 10490
% 0.20/0.41  % (22649)Time elapsed: 0.005 s
% 0.20/0.41  % (22649)------------------------------
% 0.20/0.41  % (22649)------------------------------
% 0.20/0.41  % (22643)Success in time 0.062 s
%------------------------------------------------------------------------------
