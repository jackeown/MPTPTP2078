%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:32 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   70 (  95 expanded)
%              Number of leaves         :   21 (  45 expanded)
%              Depth                    :    7
%              Number of atoms          :  147 ( 203 expanded)
%              Number of equality atoms :   46 (  62 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f104,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f29,f34,f44,f48,f52,f56,f60,f64,f70,f81,f87,f100,f103])).

fof(f103,plain,
    ( spl1_1
    | ~ spl1_15 ),
    inference(avatar_contradiction_clause,[],[f102])).

fof(f102,plain,
    ( $false
    | spl1_1
    | ~ spl1_15 ),
    inference(trivial_inequality_removal,[],[f101])).

fof(f101,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl1_1
    | ~ spl1_15 ),
    inference(superposition,[],[f28,f99])).

fof(f99,plain,
    ( ! [X2] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X2)
    | ~ spl1_15 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl1_15
  <=> ! [X2] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_15])])).

fof(f28,plain,
    ( k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0)
    | spl1_1 ),
    inference(avatar_component_clause,[],[f26])).

fof(f26,plain,
    ( spl1_1
  <=> k1_xboole_0 = k9_relat_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f100,plain,
    ( spl1_15
    | ~ spl1_4
    | ~ spl1_8
    | ~ spl1_10
    | ~ spl1_12
    | ~ spl1_13 ),
    inference(avatar_split_clause,[],[f96,f85,f78,f67,f58,f41,f98])).

fof(f41,plain,
    ( spl1_4
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f58,plain,
    ( spl1_8
  <=> ! [X1,X0] :
        ( k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).

fof(f67,plain,
    ( spl1_10
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).

fof(f78,plain,
    ( spl1_12
  <=> k1_xboole_0 = k9_relat_1(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_12])])).

fof(f85,plain,
    ( spl1_13
  <=> ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_13])])).

fof(f96,plain,
    ( ! [X2] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X2)
    | ~ spl1_4
    | ~ spl1_8
    | ~ spl1_10
    | ~ spl1_12
    | ~ spl1_13 ),
    inference(forward_demodulation,[],[f95,f80])).

fof(f80,plain,
    ( k1_xboole_0 = k9_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ spl1_12 ),
    inference(avatar_component_clause,[],[f78])).

fof(f95,plain,
    ( ! [X2] : k9_relat_1(k1_xboole_0,k1_xboole_0) = k9_relat_1(k1_xboole_0,X2)
    | ~ spl1_4
    | ~ spl1_8
    | ~ spl1_10
    | ~ spl1_13 ),
    inference(forward_demodulation,[],[f94,f86])).

fof(f86,plain,
    ( ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)
    | ~ spl1_13 ),
    inference(avatar_component_clause,[],[f85])).

fof(f94,plain,
    ( ! [X2] : k9_relat_1(k1_xboole_0,X2) = k9_relat_1(k1_xboole_0,k3_xboole_0(k1_xboole_0,X2))
    | ~ spl1_4
    | ~ spl1_8
    | ~ spl1_10 ),
    inference(forward_demodulation,[],[f89,f43])).

fof(f43,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl1_4 ),
    inference(avatar_component_clause,[],[f41])).

fof(f89,plain,
    ( ! [X2] : k9_relat_1(k1_xboole_0,X2) = k9_relat_1(k1_xboole_0,k3_xboole_0(k1_relat_1(k1_xboole_0),X2))
    | ~ spl1_8
    | ~ spl1_10 ),
    inference(resolution,[],[f59,f69])).

fof(f69,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl1_10 ),
    inference(avatar_component_clause,[],[f67])).

fof(f59,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) )
    | ~ spl1_8 ),
    inference(avatar_component_clause,[],[f58])).

fof(f87,plain,
    ( spl1_13
    | ~ spl1_6
    | ~ spl1_9 ),
    inference(avatar_split_clause,[],[f83,f62,f50,f85])).

fof(f50,plain,
    ( spl1_6
  <=> ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f62,plain,
    ( spl1_9
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).

fof(f83,plain,
    ( ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)
    | ~ spl1_6
    | ~ spl1_9 ),
    inference(resolution,[],[f63,f51])).

fof(f51,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl1_6 ),
    inference(avatar_component_clause,[],[f50])).

fof(f63,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k3_xboole_0(X0,X1) = X0 )
    | ~ spl1_9 ),
    inference(avatar_component_clause,[],[f62])).

fof(f81,plain,
    ( spl1_12
    | ~ spl1_7
    | ~ spl1_10 ),
    inference(avatar_split_clause,[],[f72,f67,f54,f78])).

fof(f54,plain,
    ( spl1_7
  <=> ! [X0] :
        ( k1_xboole_0 = k9_relat_1(X0,k1_xboole_0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).

fof(f72,plain,
    ( k1_xboole_0 = k9_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ spl1_7
    | ~ spl1_10 ),
    inference(resolution,[],[f55,f69])).

fof(f55,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k1_xboole_0 = k9_relat_1(X0,k1_xboole_0) )
    | ~ spl1_7 ),
    inference(avatar_component_clause,[],[f54])).

fof(f70,plain,
    ( spl1_10
    | ~ spl1_2
    | ~ spl1_5 ),
    inference(avatar_split_clause,[],[f65,f46,f31,f67])).

fof(f31,plain,
    ( spl1_2
  <=> k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f46,plain,
    ( spl1_5
  <=> ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f65,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl1_2
    | ~ spl1_5 ),
    inference(superposition,[],[f47,f33])).

% (9554)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
fof(f33,plain,
    ( k1_xboole_0 = k6_relat_1(k1_xboole_0)
    | ~ spl1_2 ),
    inference(avatar_component_clause,[],[f31])).

fof(f47,plain,
    ( ! [X0] : v1_relat_1(k6_relat_1(X0))
    | ~ spl1_5 ),
    inference(avatar_component_clause,[],[f46])).

fof(f64,plain,(
    spl1_9 ),
    inference(avatar_split_clause,[],[f24,f62])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f60,plain,(
    spl1_8 ),
    inference(avatar_split_clause,[],[f23,f58])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_relat_1)).

fof(f56,plain,(
    spl1_7 ),
    inference(avatar_split_clause,[],[f22,f54])).

fof(f22,plain,(
    ! [X0] :
      ( k1_xboole_0 = k9_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( k1_xboole_0 = k9_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k9_relat_1(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_relat_1)).

fof(f52,plain,(
    spl1_6 ),
    inference(avatar_split_clause,[],[f21,f50])).

fof(f21,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f48,plain,(
    spl1_5 ),
    inference(avatar_split_clause,[],[f20,f46])).

fof(f20,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f44,plain,(
    spl1_4 ),
    inference(avatar_split_clause,[],[f18,f41])).

fof(f18,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f34,plain,(
    spl1_2 ),
    inference(avatar_split_clause,[],[f17,f31])).

fof(f17,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

fof(f29,plain,(
    ~ spl1_1 ),
    inference(avatar_split_clause,[],[f16,f26])).

fof(f16,plain,(
    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f14])).

fof(f14,plain,
    ( ? [X0] : k1_xboole_0 != k9_relat_1(k1_xboole_0,X0)
   => k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] : k1_xboole_0 != k9_relat_1(k1_xboole_0,X0) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:35:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.41  % (9559)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.21/0.41  % (9551)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
% 0.21/0.41  % (9559)Refutation found. Thanks to Tanya!
% 0.21/0.41  % SZS status Theorem for theBenchmark
% 0.21/0.41  % SZS output start Proof for theBenchmark
% 0.21/0.41  fof(f104,plain,(
% 0.21/0.41    $false),
% 0.21/0.41    inference(avatar_sat_refutation,[],[f29,f34,f44,f48,f52,f56,f60,f64,f70,f81,f87,f100,f103])).
% 0.21/0.41  fof(f103,plain,(
% 0.21/0.41    spl1_1 | ~spl1_15),
% 0.21/0.41    inference(avatar_contradiction_clause,[],[f102])).
% 0.21/0.41  fof(f102,plain,(
% 0.21/0.41    $false | (spl1_1 | ~spl1_15)),
% 0.21/0.41    inference(trivial_inequality_removal,[],[f101])).
% 0.21/0.41  fof(f101,plain,(
% 0.21/0.41    k1_xboole_0 != k1_xboole_0 | (spl1_1 | ~spl1_15)),
% 0.21/0.41    inference(superposition,[],[f28,f99])).
% 0.21/0.41  fof(f99,plain,(
% 0.21/0.41    ( ! [X2] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X2)) ) | ~spl1_15),
% 0.21/0.41    inference(avatar_component_clause,[],[f98])).
% 0.21/0.41  fof(f98,plain,(
% 0.21/0.41    spl1_15 <=> ! [X2] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X2)),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl1_15])])).
% 0.21/0.41  fof(f28,plain,(
% 0.21/0.41    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0) | spl1_1),
% 0.21/0.41    inference(avatar_component_clause,[],[f26])).
% 0.21/0.41  fof(f26,plain,(
% 0.21/0.41    spl1_1 <=> k1_xboole_0 = k9_relat_1(k1_xboole_0,sK0)),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.21/0.41  fof(f100,plain,(
% 0.21/0.41    spl1_15 | ~spl1_4 | ~spl1_8 | ~spl1_10 | ~spl1_12 | ~spl1_13),
% 0.21/0.41    inference(avatar_split_clause,[],[f96,f85,f78,f67,f58,f41,f98])).
% 0.21/0.41  fof(f41,plain,(
% 0.21/0.41    spl1_4 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.21/0.41  fof(f58,plain,(
% 0.21/0.41    spl1_8 <=> ! [X1,X0] : (k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).
% 0.21/0.41  fof(f67,plain,(
% 0.21/0.41    spl1_10 <=> v1_relat_1(k1_xboole_0)),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).
% 0.21/0.41  fof(f78,plain,(
% 0.21/0.41    spl1_12 <=> k1_xboole_0 = k9_relat_1(k1_xboole_0,k1_xboole_0)),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl1_12])])).
% 0.21/0.41  fof(f85,plain,(
% 0.21/0.41    spl1_13 <=> ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl1_13])])).
% 0.21/0.41  fof(f96,plain,(
% 0.21/0.41    ( ! [X2] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X2)) ) | (~spl1_4 | ~spl1_8 | ~spl1_10 | ~spl1_12 | ~spl1_13)),
% 0.21/0.41    inference(forward_demodulation,[],[f95,f80])).
% 0.21/0.41  fof(f80,plain,(
% 0.21/0.41    k1_xboole_0 = k9_relat_1(k1_xboole_0,k1_xboole_0) | ~spl1_12),
% 0.21/0.41    inference(avatar_component_clause,[],[f78])).
% 0.21/0.41  fof(f95,plain,(
% 0.21/0.41    ( ! [X2] : (k9_relat_1(k1_xboole_0,k1_xboole_0) = k9_relat_1(k1_xboole_0,X2)) ) | (~spl1_4 | ~spl1_8 | ~spl1_10 | ~spl1_13)),
% 0.21/0.41    inference(forward_demodulation,[],[f94,f86])).
% 0.21/0.41  fof(f86,plain,(
% 0.21/0.41    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) ) | ~spl1_13),
% 0.21/0.41    inference(avatar_component_clause,[],[f85])).
% 0.21/0.41  fof(f94,plain,(
% 0.21/0.41    ( ! [X2] : (k9_relat_1(k1_xboole_0,X2) = k9_relat_1(k1_xboole_0,k3_xboole_0(k1_xboole_0,X2))) ) | (~spl1_4 | ~spl1_8 | ~spl1_10)),
% 0.21/0.41    inference(forward_demodulation,[],[f89,f43])).
% 0.21/0.41  fof(f43,plain,(
% 0.21/0.41    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl1_4),
% 0.21/0.41    inference(avatar_component_clause,[],[f41])).
% 0.21/0.41  fof(f89,plain,(
% 0.21/0.41    ( ! [X2] : (k9_relat_1(k1_xboole_0,X2) = k9_relat_1(k1_xboole_0,k3_xboole_0(k1_relat_1(k1_xboole_0),X2))) ) | (~spl1_8 | ~spl1_10)),
% 0.21/0.41    inference(resolution,[],[f59,f69])).
% 0.21/0.41  fof(f69,plain,(
% 0.21/0.41    v1_relat_1(k1_xboole_0) | ~spl1_10),
% 0.21/0.41    inference(avatar_component_clause,[],[f67])).
% 0.21/0.41  fof(f59,plain,(
% 0.21/0.41    ( ! [X0,X1] : (~v1_relat_1(X1) | k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))) ) | ~spl1_8),
% 0.21/0.41    inference(avatar_component_clause,[],[f58])).
% 0.21/0.41  fof(f87,plain,(
% 0.21/0.41    spl1_13 | ~spl1_6 | ~spl1_9),
% 0.21/0.41    inference(avatar_split_clause,[],[f83,f62,f50,f85])).
% 0.21/0.41  fof(f50,plain,(
% 0.21/0.41    spl1_6 <=> ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 0.21/0.41  fof(f62,plain,(
% 0.21/0.41    spl1_9 <=> ! [X1,X0] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).
% 0.21/0.41  fof(f83,plain,(
% 0.21/0.41    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) ) | (~spl1_6 | ~spl1_9)),
% 0.21/0.41    inference(resolution,[],[f63,f51])).
% 0.21/0.41  fof(f51,plain,(
% 0.21/0.41    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | ~spl1_6),
% 0.21/0.41    inference(avatar_component_clause,[],[f50])).
% 0.21/0.41  fof(f63,plain,(
% 0.21/0.41    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) ) | ~spl1_9),
% 0.21/0.41    inference(avatar_component_clause,[],[f62])).
% 0.21/0.41  fof(f81,plain,(
% 0.21/0.41    spl1_12 | ~spl1_7 | ~spl1_10),
% 0.21/0.41    inference(avatar_split_clause,[],[f72,f67,f54,f78])).
% 0.21/0.41  fof(f54,plain,(
% 0.21/0.41    spl1_7 <=> ! [X0] : (k1_xboole_0 = k9_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).
% 0.21/0.41  fof(f72,plain,(
% 0.21/0.41    k1_xboole_0 = k9_relat_1(k1_xboole_0,k1_xboole_0) | (~spl1_7 | ~spl1_10)),
% 0.21/0.41    inference(resolution,[],[f55,f69])).
% 0.21/0.41  fof(f55,plain,(
% 0.21/0.41    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k9_relat_1(X0,k1_xboole_0)) ) | ~spl1_7),
% 0.21/0.41    inference(avatar_component_clause,[],[f54])).
% 0.21/0.41  fof(f70,plain,(
% 0.21/0.41    spl1_10 | ~spl1_2 | ~spl1_5),
% 0.21/0.41    inference(avatar_split_clause,[],[f65,f46,f31,f67])).
% 0.21/0.41  fof(f31,plain,(
% 0.21/0.41    spl1_2 <=> k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.21/0.41  fof(f46,plain,(
% 0.21/0.41    spl1_5 <=> ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.21/0.41  fof(f65,plain,(
% 0.21/0.41    v1_relat_1(k1_xboole_0) | (~spl1_2 | ~spl1_5)),
% 0.21/0.41    inference(superposition,[],[f47,f33])).
% 0.21/0.41  % (9554)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.21/0.41  fof(f33,plain,(
% 0.21/0.41    k1_xboole_0 = k6_relat_1(k1_xboole_0) | ~spl1_2),
% 0.21/0.41    inference(avatar_component_clause,[],[f31])).
% 0.21/0.41  fof(f47,plain,(
% 0.21/0.41    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) ) | ~spl1_5),
% 0.21/0.41    inference(avatar_component_clause,[],[f46])).
% 0.21/0.41  fof(f64,plain,(
% 0.21/0.41    spl1_9),
% 0.21/0.41    inference(avatar_split_clause,[],[f24,f62])).
% 0.21/0.41  fof(f24,plain,(
% 0.21/0.41    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f13])).
% 0.21/0.41  fof(f13,plain,(
% 0.21/0.41    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.41    inference(ennf_transformation,[],[f1])).
% 0.21/0.41  fof(f1,axiom,(
% 0.21/0.41    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.41  fof(f60,plain,(
% 0.21/0.41    spl1_8),
% 0.21/0.41    inference(avatar_split_clause,[],[f23,f58])).
% 0.21/0.41  fof(f23,plain,(
% 0.21/0.41    ( ! [X0,X1] : (k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f12])).
% 0.21/0.41  fof(f12,plain,(
% 0.21/0.41    ! [X0,X1] : (k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.41    inference(ennf_transformation,[],[f4])).
% 0.21/0.41  fof(f4,axiom,(
% 0.21/0.41    ! [X0,X1] : (v1_relat_1(X1) => k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)))),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_relat_1)).
% 0.21/0.41  fof(f56,plain,(
% 0.21/0.41    spl1_7),
% 0.21/0.41    inference(avatar_split_clause,[],[f22,f54])).
% 0.21/0.41  fof(f22,plain,(
% 0.21/0.41    ( ! [X0] : (k1_xboole_0 = k9_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f11])).
% 0.21/0.41  fof(f11,plain,(
% 0.21/0.41    ! [X0] : (k1_xboole_0 = k9_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 0.21/0.41    inference(ennf_transformation,[],[f5])).
% 0.21/0.41  fof(f5,axiom,(
% 0.21/0.41    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k9_relat_1(X0,k1_xboole_0))),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_relat_1)).
% 0.21/0.41  fof(f52,plain,(
% 0.21/0.41    spl1_6),
% 0.21/0.41    inference(avatar_split_clause,[],[f21,f50])).
% 0.21/0.41  fof(f21,plain,(
% 0.21/0.41    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f2])).
% 0.21/0.41  fof(f2,axiom,(
% 0.21/0.41    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.41  fof(f48,plain,(
% 0.21/0.41    spl1_5),
% 0.21/0.41    inference(avatar_split_clause,[],[f20,f46])).
% 0.21/0.41  fof(f20,plain,(
% 0.21/0.41    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.41    inference(cnf_transformation,[],[f3])).
% 0.21/0.41  fof(f3,axiom,(
% 0.21/0.41    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.21/0.41  fof(f44,plain,(
% 0.21/0.41    spl1_4),
% 0.21/0.41    inference(avatar_split_clause,[],[f18,f41])).
% 0.21/0.41  fof(f18,plain,(
% 0.21/0.41    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.41    inference(cnf_transformation,[],[f6])).
% 0.21/0.41  fof(f6,axiom,(
% 0.21/0.41    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.21/0.41  fof(f34,plain,(
% 0.21/0.41    spl1_2),
% 0.21/0.41    inference(avatar_split_clause,[],[f17,f31])).
% 0.21/0.41  fof(f17,plain,(
% 0.21/0.41    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.21/0.41    inference(cnf_transformation,[],[f7])).
% 0.21/0.41  fof(f7,axiom,(
% 0.21/0.41    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).
% 0.21/0.41  fof(f29,plain,(
% 0.21/0.41    ~spl1_1),
% 0.21/0.41    inference(avatar_split_clause,[],[f16,f26])).
% 0.21/0.41  fof(f16,plain,(
% 0.21/0.41    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0)),
% 0.21/0.41    inference(cnf_transformation,[],[f15])).
% 0.21/0.41  fof(f15,plain,(
% 0.21/0.41    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0)),
% 0.21/0.41    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f14])).
% 0.21/0.41  fof(f14,plain,(
% 0.21/0.41    ? [X0] : k1_xboole_0 != k9_relat_1(k1_xboole_0,X0) => k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0)),
% 0.21/0.41    introduced(choice_axiom,[])).
% 0.21/0.41  fof(f10,plain,(
% 0.21/0.41    ? [X0] : k1_xboole_0 != k9_relat_1(k1_xboole_0,X0)),
% 0.21/0.41    inference(ennf_transformation,[],[f9])).
% 0.21/0.41  fof(f9,negated_conjecture,(
% 0.21/0.41    ~! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 0.21/0.41    inference(negated_conjecture,[],[f8])).
% 0.21/0.41  fof(f8,conjecture,(
% 0.21/0.41    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).
% 0.21/0.41  % SZS output end Proof for theBenchmark
% 0.21/0.41  % (9559)------------------------------
% 0.21/0.41  % (9559)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.41  % (9559)Termination reason: Refutation
% 0.21/0.41  
% 0.21/0.41  % (9559)Memory used [KB]: 6140
% 0.21/0.41  % (9559)Time elapsed: 0.004 s
% 0.21/0.41  % (9559)------------------------------
% 0.21/0.41  % (9559)------------------------------
% 0.21/0.41  % (9548)Success in time 0.059 s
%------------------------------------------------------------------------------
