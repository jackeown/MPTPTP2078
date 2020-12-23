%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:16 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   53 (  69 expanded)
%              Number of leaves         :   16 (  32 expanded)
%              Depth                    :    6
%              Number of atoms          :  103 ( 139 expanded)
%              Number of equality atoms :   31 (  41 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
% (10569)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
fof(f70,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f23,f28,f32,f36,f40,f44,f50,f55,f66,f69])).

fof(f69,plain,
    ( spl1_1
    | ~ spl1_10 ),
    inference(avatar_contradiction_clause,[],[f68])).

fof(f68,plain,
    ( $false
    | spl1_1
    | ~ spl1_10 ),
    inference(trivial_inequality_removal,[],[f67])).

fof(f67,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl1_1
    | ~ spl1_10 ),
    inference(superposition,[],[f22,f65])).

fof(f65,plain,
    ( ! [X2] : k1_xboole_0 = k8_relat_1(X2,k1_xboole_0)
    | ~ spl1_10 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl1_10
  <=> ! [X2] : k1_xboole_0 = k8_relat_1(X2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).

fof(f22,plain,
    ( k1_xboole_0 != k8_relat_1(sK0,k1_xboole_0)
    | spl1_1 ),
    inference(avatar_component_clause,[],[f20])).

fof(f20,plain,
    ( spl1_1
  <=> k1_xboole_0 = k8_relat_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f66,plain,
    ( spl1_10
    | ~ spl1_5
    | ~ spl1_7
    | ~ spl1_8 ),
    inference(avatar_split_clause,[],[f62,f53,f47,f38,f64])).

fof(f38,plain,
    ( spl1_5
  <=> ! [X1,X0] :
        ( k8_relat_1(X0,X1) = k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0))
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f47,plain,
    ( spl1_7
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).

fof(f53,plain,
    ( spl1_8
  <=> ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).

fof(f62,plain,
    ( ! [X2] : k1_xboole_0 = k8_relat_1(X2,k1_xboole_0)
    | ~ spl1_5
    | ~ spl1_7
    | ~ spl1_8 ),
    inference(forward_demodulation,[],[f57,f54])).

fof(f54,plain,
    ( ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)
    | ~ spl1_8 ),
    inference(avatar_component_clause,[],[f53])).

fof(f57,plain,
    ( ! [X2] : k8_relat_1(X2,k1_xboole_0) = k3_xboole_0(k1_xboole_0,k2_zfmisc_1(k1_relat_1(k1_xboole_0),X2))
    | ~ spl1_5
    | ~ spl1_7 ),
    inference(resolution,[],[f39,f49])).

fof(f49,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl1_7 ),
    inference(avatar_component_clause,[],[f47])).

fof(f39,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k8_relat_1(X0,X1) = k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0)) )
    | ~ spl1_5 ),
    inference(avatar_component_clause,[],[f38])).

fof(f55,plain,
    ( spl1_8
    | ~ spl1_4
    | ~ spl1_6 ),
    inference(avatar_split_clause,[],[f51,f42,f34,f53])).

fof(f34,plain,
    ( spl1_4
  <=> ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f42,plain,
    ( spl1_6
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f51,plain,
    ( ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)
    | ~ spl1_4
    | ~ spl1_6 ),
    inference(resolution,[],[f43,f35])).

fof(f35,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl1_4 ),
    inference(avatar_component_clause,[],[f34])).

fof(f43,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k3_xboole_0(X0,X1) = X0 )
    | ~ spl1_6 ),
    inference(avatar_component_clause,[],[f42])).

fof(f50,plain,
    ( spl1_7
    | ~ spl1_2
    | ~ spl1_3 ),
    inference(avatar_split_clause,[],[f45,f30,f25,f47])).

fof(f25,plain,
    ( spl1_2
  <=> k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f30,plain,
    ( spl1_3
  <=> ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f45,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl1_2
    | ~ spl1_3 ),
    inference(superposition,[],[f31,f27])).

fof(f27,plain,
    ( k1_xboole_0 = k6_relat_1(k1_xboole_0)
    | ~ spl1_2 ),
    inference(avatar_component_clause,[],[f25])).

fof(f31,plain,
    ( ! [X0] : v1_relat_1(k6_relat_1(X0))
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f30])).

fof(f44,plain,(
    spl1_6 ),
    inference(avatar_split_clause,[],[f18,f42])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f40,plain,(
    spl1_5 ),
    inference(avatar_split_clause,[],[f17,f38])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t124_relat_1)).

fof(f36,plain,(
    spl1_4 ),
    inference(avatar_split_clause,[],[f16,f34])).

fof(f16,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f32,plain,(
    spl1_3 ),
    inference(avatar_split_clause,[],[f15,f30])).

fof(f15,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f28,plain,(
    spl1_2 ),
    inference(avatar_split_clause,[],[f14,f25])).

fof(f14,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

fof(f23,plain,(
    ~ spl1_1 ),
    inference(avatar_split_clause,[],[f13,f20])).

fof(f13,plain,(
    k1_xboole_0 != k8_relat_1(sK0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    k1_xboole_0 != k8_relat_1(sK0,k1_xboole_0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f8,f11])).

fof(f11,plain,
    ( ? [X0] : k1_xboole_0 != k8_relat_1(X0,k1_xboole_0)
   => k1_xboole_0 != k8_relat_1(sK0,k1_xboole_0) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] : k1_xboole_0 != k8_relat_1(X0,k1_xboole_0) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k8_relat_1(X0,k1_xboole_0) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] : k1_xboole_0 = k8_relat_1(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:19:00 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.42  % (10570)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.22/0.42  % (10568)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.22/0.42  % (10568)Refutation found. Thanks to Tanya!
% 0.22/0.42  % SZS status Theorem for theBenchmark
% 0.22/0.42  % SZS output start Proof for theBenchmark
% 0.22/0.43  % (10569)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.22/0.43  fof(f70,plain,(
% 0.22/0.43    $false),
% 0.22/0.43    inference(avatar_sat_refutation,[],[f23,f28,f32,f36,f40,f44,f50,f55,f66,f69])).
% 0.22/0.43  fof(f69,plain,(
% 0.22/0.43    spl1_1 | ~spl1_10),
% 0.22/0.43    inference(avatar_contradiction_clause,[],[f68])).
% 0.22/0.43  fof(f68,plain,(
% 0.22/0.43    $false | (spl1_1 | ~spl1_10)),
% 0.22/0.43    inference(trivial_inequality_removal,[],[f67])).
% 0.22/0.43  fof(f67,plain,(
% 0.22/0.43    k1_xboole_0 != k1_xboole_0 | (spl1_1 | ~spl1_10)),
% 0.22/0.43    inference(superposition,[],[f22,f65])).
% 0.22/0.43  fof(f65,plain,(
% 0.22/0.43    ( ! [X2] : (k1_xboole_0 = k8_relat_1(X2,k1_xboole_0)) ) | ~spl1_10),
% 0.22/0.43    inference(avatar_component_clause,[],[f64])).
% 0.22/0.43  fof(f64,plain,(
% 0.22/0.43    spl1_10 <=> ! [X2] : k1_xboole_0 = k8_relat_1(X2,k1_xboole_0)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).
% 0.22/0.43  fof(f22,plain,(
% 0.22/0.43    k1_xboole_0 != k8_relat_1(sK0,k1_xboole_0) | spl1_1),
% 0.22/0.43    inference(avatar_component_clause,[],[f20])).
% 0.22/0.43  fof(f20,plain,(
% 0.22/0.43    spl1_1 <=> k1_xboole_0 = k8_relat_1(sK0,k1_xboole_0)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.22/0.43  fof(f66,plain,(
% 0.22/0.43    spl1_10 | ~spl1_5 | ~spl1_7 | ~spl1_8),
% 0.22/0.43    inference(avatar_split_clause,[],[f62,f53,f47,f38,f64])).
% 0.22/0.43  fof(f38,plain,(
% 0.22/0.43    spl1_5 <=> ! [X1,X0] : (k8_relat_1(X0,X1) = k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.22/0.43  fof(f47,plain,(
% 0.22/0.43    spl1_7 <=> v1_relat_1(k1_xboole_0)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).
% 0.22/0.43  fof(f53,plain,(
% 0.22/0.43    spl1_8 <=> ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).
% 0.22/0.43  fof(f62,plain,(
% 0.22/0.43    ( ! [X2] : (k1_xboole_0 = k8_relat_1(X2,k1_xboole_0)) ) | (~spl1_5 | ~spl1_7 | ~spl1_8)),
% 0.22/0.43    inference(forward_demodulation,[],[f57,f54])).
% 0.22/0.43  fof(f54,plain,(
% 0.22/0.43    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) ) | ~spl1_8),
% 0.22/0.43    inference(avatar_component_clause,[],[f53])).
% 0.22/0.43  fof(f57,plain,(
% 0.22/0.43    ( ! [X2] : (k8_relat_1(X2,k1_xboole_0) = k3_xboole_0(k1_xboole_0,k2_zfmisc_1(k1_relat_1(k1_xboole_0),X2))) ) | (~spl1_5 | ~spl1_7)),
% 0.22/0.43    inference(resolution,[],[f39,f49])).
% 0.22/0.43  fof(f49,plain,(
% 0.22/0.43    v1_relat_1(k1_xboole_0) | ~spl1_7),
% 0.22/0.43    inference(avatar_component_clause,[],[f47])).
% 0.22/0.43  fof(f39,plain,(
% 0.22/0.43    ( ! [X0,X1] : (~v1_relat_1(X1) | k8_relat_1(X0,X1) = k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0))) ) | ~spl1_5),
% 0.22/0.43    inference(avatar_component_clause,[],[f38])).
% 0.22/0.43  fof(f55,plain,(
% 0.22/0.43    spl1_8 | ~spl1_4 | ~spl1_6),
% 0.22/0.43    inference(avatar_split_clause,[],[f51,f42,f34,f53])).
% 0.22/0.43  fof(f34,plain,(
% 0.22/0.43    spl1_4 <=> ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.22/0.43  fof(f42,plain,(
% 0.22/0.43    spl1_6 <=> ! [X1,X0] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 0.22/0.43  fof(f51,plain,(
% 0.22/0.43    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) ) | (~spl1_4 | ~spl1_6)),
% 0.22/0.43    inference(resolution,[],[f43,f35])).
% 0.22/0.43  fof(f35,plain,(
% 0.22/0.43    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | ~spl1_4),
% 0.22/0.43    inference(avatar_component_clause,[],[f34])).
% 0.22/0.43  fof(f43,plain,(
% 0.22/0.43    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) ) | ~spl1_6),
% 0.22/0.43    inference(avatar_component_clause,[],[f42])).
% 0.22/0.43  fof(f50,plain,(
% 0.22/0.43    spl1_7 | ~spl1_2 | ~spl1_3),
% 0.22/0.43    inference(avatar_split_clause,[],[f45,f30,f25,f47])).
% 0.22/0.43  fof(f25,plain,(
% 0.22/0.43    spl1_2 <=> k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.22/0.43  fof(f30,plain,(
% 0.22/0.43    spl1_3 <=> ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.22/0.43  fof(f45,plain,(
% 0.22/0.43    v1_relat_1(k1_xboole_0) | (~spl1_2 | ~spl1_3)),
% 0.22/0.43    inference(superposition,[],[f31,f27])).
% 0.22/0.43  fof(f27,plain,(
% 0.22/0.43    k1_xboole_0 = k6_relat_1(k1_xboole_0) | ~spl1_2),
% 0.22/0.43    inference(avatar_component_clause,[],[f25])).
% 0.22/0.43  fof(f31,plain,(
% 0.22/0.43    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) ) | ~spl1_3),
% 0.22/0.43    inference(avatar_component_clause,[],[f30])).
% 0.22/0.43  fof(f44,plain,(
% 0.22/0.43    spl1_6),
% 0.22/0.43    inference(avatar_split_clause,[],[f18,f42])).
% 0.22/0.43  fof(f18,plain,(
% 0.22/0.43    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f10])).
% 0.22/0.43  fof(f10,plain,(
% 0.22/0.43    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.22/0.43    inference(ennf_transformation,[],[f1])).
% 0.22/0.43  fof(f1,axiom,(
% 0.22/0.43    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.22/0.43  fof(f40,plain,(
% 0.22/0.43    spl1_5),
% 0.22/0.43    inference(avatar_split_clause,[],[f17,f38])).
% 0.22/0.43  fof(f17,plain,(
% 0.22/0.43    ( ! [X0,X1] : (k8_relat_1(X0,X1) = k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f9])).
% 0.22/0.43  fof(f9,plain,(
% 0.22/0.43    ! [X0,X1] : (k8_relat_1(X0,X1) = k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.43    inference(ennf_transformation,[],[f4])).
% 0.22/0.43  fof(f4,axiom,(
% 0.22/0.43    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0)))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t124_relat_1)).
% 0.22/0.43  fof(f36,plain,(
% 0.22/0.43    spl1_4),
% 0.22/0.43    inference(avatar_split_clause,[],[f16,f34])).
% 0.22/0.43  fof(f16,plain,(
% 0.22/0.43    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f2])).
% 0.22/0.43  fof(f2,axiom,(
% 0.22/0.43    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.43  fof(f32,plain,(
% 0.22/0.43    spl1_3),
% 0.22/0.43    inference(avatar_split_clause,[],[f15,f30])).
% 0.22/0.43  fof(f15,plain,(
% 0.22/0.43    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.22/0.43    inference(cnf_transformation,[],[f3])).
% 0.22/0.43  fof(f3,axiom,(
% 0.22/0.43    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.22/0.43  fof(f28,plain,(
% 0.22/0.43    spl1_2),
% 0.22/0.43    inference(avatar_split_clause,[],[f14,f25])).
% 0.22/0.43  fof(f14,plain,(
% 0.22/0.43    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.22/0.43    inference(cnf_transformation,[],[f5])).
% 0.22/0.43  fof(f5,axiom,(
% 0.22/0.43    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).
% 0.22/0.43  fof(f23,plain,(
% 0.22/0.43    ~spl1_1),
% 0.22/0.43    inference(avatar_split_clause,[],[f13,f20])).
% 0.22/0.43  fof(f13,plain,(
% 0.22/0.43    k1_xboole_0 != k8_relat_1(sK0,k1_xboole_0)),
% 0.22/0.43    inference(cnf_transformation,[],[f12])).
% 0.22/0.43  fof(f12,plain,(
% 0.22/0.43    k1_xboole_0 != k8_relat_1(sK0,k1_xboole_0)),
% 0.22/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f8,f11])).
% 0.22/0.43  fof(f11,plain,(
% 0.22/0.43    ? [X0] : k1_xboole_0 != k8_relat_1(X0,k1_xboole_0) => k1_xboole_0 != k8_relat_1(sK0,k1_xboole_0)),
% 0.22/0.43    introduced(choice_axiom,[])).
% 0.22/0.43  fof(f8,plain,(
% 0.22/0.43    ? [X0] : k1_xboole_0 != k8_relat_1(X0,k1_xboole_0)),
% 0.22/0.43    inference(ennf_transformation,[],[f7])).
% 0.22/0.43  fof(f7,negated_conjecture,(
% 0.22/0.43    ~! [X0] : k1_xboole_0 = k8_relat_1(X0,k1_xboole_0)),
% 0.22/0.43    inference(negated_conjecture,[],[f6])).
% 0.22/0.43  fof(f6,conjecture,(
% 0.22/0.43    ! [X0] : k1_xboole_0 = k8_relat_1(X0,k1_xboole_0)),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_relat_1)).
% 0.22/0.43  % SZS output end Proof for theBenchmark
% 0.22/0.43  % (10568)------------------------------
% 0.22/0.43  % (10568)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.43  % (10568)Termination reason: Refutation
% 0.22/0.43  
% 0.22/0.43  % (10568)Memory used [KB]: 10490
% 0.22/0.43  % (10568)Time elapsed: 0.006 s
% 0.22/0.43  % (10568)------------------------------
% 0.22/0.43  % (10568)------------------------------
% 0.22/0.43  % (10562)Success in time 0.071 s
%------------------------------------------------------------------------------
