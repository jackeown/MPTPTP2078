%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:30 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 116 expanded)
%              Number of leaves         :   26 (  56 expanded)
%              Depth                    :    6
%              Number of atoms          :  184 ( 256 expanded)
%              Number of equality atoms :   52 (  72 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f168,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f35,f40,f45,f54,f58,f62,f66,f70,f75,f86,f94,f119,f146,f154,f164,f167])).

fof(f167,plain,
    ( spl2_1
    | ~ spl2_24 ),
    inference(avatar_contradiction_clause,[],[f166])).

fof(f166,plain,
    ( $false
    | spl2_1
    | ~ spl2_24 ),
    inference(trivial_inequality_removal,[],[f165])).

fof(f165,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl2_1
    | ~ spl2_24 ),
    inference(superposition,[],[f34,f163])).

fof(f163,plain,
    ( ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)
    | ~ spl2_24 ),
    inference(avatar_component_clause,[],[f162])).

fof(f162,plain,
    ( spl2_24
  <=> ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).

fof(f34,plain,
    ( k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f32])).

fof(f32,plain,
    ( spl2_1
  <=> k1_xboole_0 = k9_relat_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f164,plain,
    ( spl2_24
    | ~ spl2_3
    | ~ spl2_18
    | ~ spl2_23 ),
    inference(avatar_split_clause,[],[f160,f152,f117,f42,f162])).

fof(f42,plain,
    ( spl2_3
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f117,plain,
    ( spl2_18
  <=> ! [X3] : k2_relat_1(k7_relat_1(k1_xboole_0,X3)) = k9_relat_1(k1_xboole_0,X3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f152,plain,
    ( spl2_23
  <=> ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).

fof(f160,plain,
    ( ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)
    | ~ spl2_3
    | ~ spl2_18
    | ~ spl2_23 ),
    inference(forward_demodulation,[],[f159,f44])).

fof(f44,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f42])).

fof(f159,plain,
    ( ! [X0] : k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,X0)
    | ~ spl2_18
    | ~ spl2_23 ),
    inference(superposition,[],[f118,f153])).

fof(f153,plain,
    ( ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)
    | ~ spl2_23 ),
    inference(avatar_component_clause,[],[f152])).

fof(f118,plain,
    ( ! [X3] : k2_relat_1(k7_relat_1(k1_xboole_0,X3)) = k9_relat_1(k1_xboole_0,X3)
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f117])).

fof(f154,plain,
    ( spl2_23
    | ~ spl2_10
    | ~ spl2_13
    | ~ spl2_22 ),
    inference(avatar_split_clause,[],[f150,f144,f91,f72,f152])).

fof(f72,plain,
    ( spl2_10
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f91,plain,
    ( spl2_13
  <=> k1_xboole_0 = k7_relat_1(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f144,plain,
    ( spl2_22
  <=> ! [X1,X0] :
        ( k7_relat_1(X0,k1_xboole_0) = k7_relat_1(k7_relat_1(X0,k1_xboole_0),X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).

fof(f150,plain,
    ( ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)
    | ~ spl2_10
    | ~ spl2_13
    | ~ spl2_22 ),
    inference(forward_demodulation,[],[f147,f93])).

fof(f93,plain,
    ( k1_xboole_0 = k7_relat_1(sK1,k1_xboole_0)
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f91])).

fof(f147,plain,
    ( ! [X0] : k7_relat_1(sK1,k1_xboole_0) = k7_relat_1(k7_relat_1(sK1,k1_xboole_0),X0)
    | ~ spl2_10
    | ~ spl2_22 ),
    inference(resolution,[],[f145,f74])).

fof(f74,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f72])).

fof(f145,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | k7_relat_1(X0,k1_xboole_0) = k7_relat_1(k7_relat_1(X0,k1_xboole_0),X1) )
    | ~ spl2_22 ),
    inference(avatar_component_clause,[],[f144])).

fof(f146,plain,
    ( spl2_22
    | ~ spl2_6
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f142,f68,f56,f144])).

fof(f56,plain,
    ( spl2_6
  <=> ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f68,plain,
    ( spl2_9
  <=> ! [X1,X0,X2] :
        ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)
        | ~ r1_tarski(X0,X1)
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f142,plain,
    ( ! [X0,X1] :
        ( k7_relat_1(X0,k1_xboole_0) = k7_relat_1(k7_relat_1(X0,k1_xboole_0),X1)
        | ~ v1_relat_1(X0) )
    | ~ spl2_6
    | ~ spl2_9 ),
    inference(resolution,[],[f69,f57])).

fof(f57,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f56])).

fof(f69,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)
        | ~ v1_relat_1(X2) )
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f68])).

fof(f119,plain,
    ( spl2_18
    | ~ spl2_8
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f107,f83,f64,f117])).

fof(f64,plain,
    ( spl2_8
  <=> ! [X1,X0] :
        ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f83,plain,
    ( spl2_12
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f107,plain,
    ( ! [X3] : k2_relat_1(k7_relat_1(k1_xboole_0,X3)) = k9_relat_1(k1_xboole_0,X3)
    | ~ spl2_8
    | ~ spl2_12 ),
    inference(resolution,[],[f65,f85])).

fof(f85,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f83])).

fof(f65,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) )
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f64])).

fof(f94,plain,
    ( spl2_13
    | ~ spl2_7
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f87,f72,f60,f91])).

fof(f60,plain,
    ( spl2_7
  <=> ! [X0] :
        ( k1_xboole_0 = k7_relat_1(X0,k1_xboole_0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f87,plain,
    ( k1_xboole_0 = k7_relat_1(sK1,k1_xboole_0)
    | ~ spl2_7
    | ~ spl2_10 ),
    inference(resolution,[],[f61,f74])).

fof(f61,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) )
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f60])).

fof(f86,plain,
    ( spl2_12
    | ~ spl2_2
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f81,f52,f37,f83])).

fof(f37,plain,
    ( spl2_2
  <=> k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f52,plain,
    ( spl2_5
  <=> ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f81,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl2_2
    | ~ spl2_5 ),
    inference(superposition,[],[f53,f39])).

fof(f39,plain,
    ( k1_xboole_0 = k6_relat_1(k1_xboole_0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f37])).

fof(f53,plain,
    ( ! [X0] : v1_relat_1(k6_relat_1(X0))
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f52])).

fof(f75,plain,(
    spl2_10 ),
    inference(avatar_split_clause,[],[f30,f72])).

fof(f30,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( v1_relat_1(sK1)
    & ~ v1_xboole_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f3,f18])).

fof(f18,plain,
    ( ? [X0] :
        ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
   => ( v1_relat_1(sK1)
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f3,axiom,(
    ? [X0] :
      ( v1_relat_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_relat_1)).

fof(f70,plain,(
    spl2_9 ),
    inference(avatar_split_clause,[],[f28,f68])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_relat_1)).

fof(f66,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f27,f64])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f62,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f26,f60])).

fof(f26,plain,(
    ! [X0] :
      ( k1_xboole_0 = k7_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( k1_xboole_0 = k7_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_relat_1)).

fof(f58,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f25,f56])).

fof(f25,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f54,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f24,f52])).

fof(f24,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f45,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f23,f42])).

fof(f23,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f40,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f21,f37])).

fof(f21,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

fof(f35,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f20,f32])).

fof(f20,plain,(
    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f16])).

fof(f16,plain,
    ( ? [X0] : k1_xboole_0 != k9_relat_1(k1_xboole_0,X0)
   => k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] : k1_xboole_0 != k9_relat_1(k1_xboole_0,X0) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 17:18:21 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.22/0.43  % (5989)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.22/0.43  % (5985)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.22/0.43  % (5990)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.22/0.43  % (5985)Refutation found. Thanks to Tanya!
% 0.22/0.43  % SZS status Theorem for theBenchmark
% 0.22/0.43  % SZS output start Proof for theBenchmark
% 0.22/0.43  fof(f168,plain,(
% 0.22/0.43    $false),
% 0.22/0.43    inference(avatar_sat_refutation,[],[f35,f40,f45,f54,f58,f62,f66,f70,f75,f86,f94,f119,f146,f154,f164,f167])).
% 0.22/0.43  fof(f167,plain,(
% 0.22/0.43    spl2_1 | ~spl2_24),
% 0.22/0.43    inference(avatar_contradiction_clause,[],[f166])).
% 0.22/0.43  fof(f166,plain,(
% 0.22/0.43    $false | (spl2_1 | ~spl2_24)),
% 0.22/0.43    inference(trivial_inequality_removal,[],[f165])).
% 0.22/0.43  fof(f165,plain,(
% 0.22/0.43    k1_xboole_0 != k1_xboole_0 | (spl2_1 | ~spl2_24)),
% 0.22/0.43    inference(superposition,[],[f34,f163])).
% 0.22/0.43  fof(f163,plain,(
% 0.22/0.43    ( ! [X0] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)) ) | ~spl2_24),
% 0.22/0.43    inference(avatar_component_clause,[],[f162])).
% 0.22/0.43  fof(f162,plain,(
% 0.22/0.43    spl2_24 <=> ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).
% 0.22/0.43  fof(f34,plain,(
% 0.22/0.43    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0) | spl2_1),
% 0.22/0.43    inference(avatar_component_clause,[],[f32])).
% 0.22/0.43  fof(f32,plain,(
% 0.22/0.43    spl2_1 <=> k1_xboole_0 = k9_relat_1(k1_xboole_0,sK0)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.43  fof(f164,plain,(
% 0.22/0.43    spl2_24 | ~spl2_3 | ~spl2_18 | ~spl2_23),
% 0.22/0.43    inference(avatar_split_clause,[],[f160,f152,f117,f42,f162])).
% 0.22/0.43  fof(f42,plain,(
% 0.22/0.43    spl2_3 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.22/0.43  fof(f117,plain,(
% 0.22/0.43    spl2_18 <=> ! [X3] : k2_relat_1(k7_relat_1(k1_xboole_0,X3)) = k9_relat_1(k1_xboole_0,X3)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 0.22/0.43  fof(f152,plain,(
% 0.22/0.43    spl2_23 <=> ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).
% 0.22/0.43  fof(f160,plain,(
% 0.22/0.43    ( ! [X0] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)) ) | (~spl2_3 | ~spl2_18 | ~spl2_23)),
% 0.22/0.43    inference(forward_demodulation,[],[f159,f44])).
% 0.22/0.43  fof(f44,plain,(
% 0.22/0.43    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl2_3),
% 0.22/0.43    inference(avatar_component_clause,[],[f42])).
% 0.22/0.43  fof(f159,plain,(
% 0.22/0.43    ( ! [X0] : (k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,X0)) ) | (~spl2_18 | ~spl2_23)),
% 0.22/0.43    inference(superposition,[],[f118,f153])).
% 0.22/0.43  fof(f153,plain,(
% 0.22/0.43    ( ! [X0] : (k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)) ) | ~spl2_23),
% 0.22/0.43    inference(avatar_component_clause,[],[f152])).
% 0.22/0.43  fof(f118,plain,(
% 0.22/0.43    ( ! [X3] : (k2_relat_1(k7_relat_1(k1_xboole_0,X3)) = k9_relat_1(k1_xboole_0,X3)) ) | ~spl2_18),
% 0.22/0.43    inference(avatar_component_clause,[],[f117])).
% 0.22/0.43  fof(f154,plain,(
% 0.22/0.43    spl2_23 | ~spl2_10 | ~spl2_13 | ~spl2_22),
% 0.22/0.43    inference(avatar_split_clause,[],[f150,f144,f91,f72,f152])).
% 0.22/0.43  fof(f72,plain,(
% 0.22/0.43    spl2_10 <=> v1_relat_1(sK1)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.22/0.43  fof(f91,plain,(
% 0.22/0.43    spl2_13 <=> k1_xboole_0 = k7_relat_1(sK1,k1_xboole_0)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.22/0.43  fof(f144,plain,(
% 0.22/0.43    spl2_22 <=> ! [X1,X0] : (k7_relat_1(X0,k1_xboole_0) = k7_relat_1(k7_relat_1(X0,k1_xboole_0),X1) | ~v1_relat_1(X0))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).
% 0.22/0.43  fof(f150,plain,(
% 0.22/0.43    ( ! [X0] : (k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)) ) | (~spl2_10 | ~spl2_13 | ~spl2_22)),
% 0.22/0.43    inference(forward_demodulation,[],[f147,f93])).
% 0.22/0.43  fof(f93,plain,(
% 0.22/0.43    k1_xboole_0 = k7_relat_1(sK1,k1_xboole_0) | ~spl2_13),
% 0.22/0.43    inference(avatar_component_clause,[],[f91])).
% 0.22/0.43  fof(f147,plain,(
% 0.22/0.43    ( ! [X0] : (k7_relat_1(sK1,k1_xboole_0) = k7_relat_1(k7_relat_1(sK1,k1_xboole_0),X0)) ) | (~spl2_10 | ~spl2_22)),
% 0.22/0.43    inference(resolution,[],[f145,f74])).
% 0.22/0.43  fof(f74,plain,(
% 0.22/0.43    v1_relat_1(sK1) | ~spl2_10),
% 0.22/0.43    inference(avatar_component_clause,[],[f72])).
% 0.22/0.43  fof(f145,plain,(
% 0.22/0.43    ( ! [X0,X1] : (~v1_relat_1(X0) | k7_relat_1(X0,k1_xboole_0) = k7_relat_1(k7_relat_1(X0,k1_xboole_0),X1)) ) | ~spl2_22),
% 0.22/0.43    inference(avatar_component_clause,[],[f144])).
% 0.22/0.43  fof(f146,plain,(
% 0.22/0.43    spl2_22 | ~spl2_6 | ~spl2_9),
% 0.22/0.43    inference(avatar_split_clause,[],[f142,f68,f56,f144])).
% 0.22/0.43  fof(f56,plain,(
% 0.22/0.43    spl2_6 <=> ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.22/0.43  fof(f68,plain,(
% 0.22/0.43    spl2_9 <=> ! [X1,X0,X2] : (k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.22/0.43  fof(f142,plain,(
% 0.22/0.43    ( ! [X0,X1] : (k7_relat_1(X0,k1_xboole_0) = k7_relat_1(k7_relat_1(X0,k1_xboole_0),X1) | ~v1_relat_1(X0)) ) | (~spl2_6 | ~spl2_9)),
% 0.22/0.43    inference(resolution,[],[f69,f57])).
% 0.22/0.43  fof(f57,plain,(
% 0.22/0.43    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | ~spl2_6),
% 0.22/0.43    inference(avatar_component_clause,[],[f56])).
% 0.22/0.43  fof(f69,plain,(
% 0.22/0.43    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) ) | ~spl2_9),
% 0.22/0.43    inference(avatar_component_clause,[],[f68])).
% 0.22/0.43  fof(f119,plain,(
% 0.22/0.43    spl2_18 | ~spl2_8 | ~spl2_12),
% 0.22/0.43    inference(avatar_split_clause,[],[f107,f83,f64,f117])).
% 0.22/0.43  fof(f64,plain,(
% 0.22/0.43    spl2_8 <=> ! [X1,X0] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.22/0.43  fof(f83,plain,(
% 0.22/0.43    spl2_12 <=> v1_relat_1(k1_xboole_0)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.22/0.43  fof(f107,plain,(
% 0.22/0.43    ( ! [X3] : (k2_relat_1(k7_relat_1(k1_xboole_0,X3)) = k9_relat_1(k1_xboole_0,X3)) ) | (~spl2_8 | ~spl2_12)),
% 0.22/0.43    inference(resolution,[],[f65,f85])).
% 0.22/0.43  fof(f85,plain,(
% 0.22/0.43    v1_relat_1(k1_xboole_0) | ~spl2_12),
% 0.22/0.43    inference(avatar_component_clause,[],[f83])).
% 0.22/0.43  fof(f65,plain,(
% 0.22/0.43    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) ) | ~spl2_8),
% 0.22/0.43    inference(avatar_component_clause,[],[f64])).
% 0.22/0.43  fof(f94,plain,(
% 0.22/0.43    spl2_13 | ~spl2_7 | ~spl2_10),
% 0.22/0.43    inference(avatar_split_clause,[],[f87,f72,f60,f91])).
% 0.22/0.43  fof(f60,plain,(
% 0.22/0.43    spl2_7 <=> ! [X0] : (k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.22/0.43  fof(f87,plain,(
% 0.22/0.43    k1_xboole_0 = k7_relat_1(sK1,k1_xboole_0) | (~spl2_7 | ~spl2_10)),
% 0.22/0.43    inference(resolution,[],[f61,f74])).
% 0.22/0.43  fof(f61,plain,(
% 0.22/0.43    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k7_relat_1(X0,k1_xboole_0)) ) | ~spl2_7),
% 0.22/0.43    inference(avatar_component_clause,[],[f60])).
% 0.22/0.43  fof(f86,plain,(
% 0.22/0.43    spl2_12 | ~spl2_2 | ~spl2_5),
% 0.22/0.43    inference(avatar_split_clause,[],[f81,f52,f37,f83])).
% 0.22/0.43  fof(f37,plain,(
% 0.22/0.43    spl2_2 <=> k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.43  fof(f52,plain,(
% 0.22/0.43    spl2_5 <=> ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.22/0.43  fof(f81,plain,(
% 0.22/0.43    v1_relat_1(k1_xboole_0) | (~spl2_2 | ~spl2_5)),
% 0.22/0.43    inference(superposition,[],[f53,f39])).
% 0.22/0.43  fof(f39,plain,(
% 0.22/0.43    k1_xboole_0 = k6_relat_1(k1_xboole_0) | ~spl2_2),
% 0.22/0.43    inference(avatar_component_clause,[],[f37])).
% 0.22/0.43  fof(f53,plain,(
% 0.22/0.43    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) ) | ~spl2_5),
% 0.22/0.43    inference(avatar_component_clause,[],[f52])).
% 0.22/0.43  fof(f75,plain,(
% 0.22/0.43    spl2_10),
% 0.22/0.43    inference(avatar_split_clause,[],[f30,f72])).
% 0.22/0.43  fof(f30,plain,(
% 0.22/0.43    v1_relat_1(sK1)),
% 0.22/0.43    inference(cnf_transformation,[],[f19])).
% 0.22/0.43  fof(f19,plain,(
% 0.22/0.43    v1_relat_1(sK1) & ~v1_xboole_0(sK1)),
% 0.22/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f3,f18])).
% 0.22/0.43  fof(f18,plain,(
% 0.22/0.43    ? [X0] : (v1_relat_1(X0) & ~v1_xboole_0(X0)) => (v1_relat_1(sK1) & ~v1_xboole_0(sK1))),
% 0.22/0.43    introduced(choice_axiom,[])).
% 0.22/0.43  fof(f3,axiom,(
% 0.22/0.43    ? [X0] : (v1_relat_1(X0) & ~v1_xboole_0(X0))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_relat_1)).
% 0.22/0.43  fof(f70,plain,(
% 0.22/0.43    spl2_9),
% 0.22/0.43    inference(avatar_split_clause,[],[f28,f68])).
% 0.22/0.43  fof(f28,plain,(
% 0.22/0.43    ( ! [X2,X0,X1] : (k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f15])).
% 0.22/0.43  fof(f15,plain,(
% 0.22/0.43    ! [X0,X1,X2] : (k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.22/0.43    inference(flattening,[],[f14])).
% 0.22/0.43  fof(f14,plain,(
% 0.22/0.43    ! [X0,X1,X2] : ((k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 0.22/0.43    inference(ennf_transformation,[],[f4])).
% 0.22/0.43  fof(f4,axiom,(
% 0.22/0.43    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_relat_1)).
% 0.22/0.43  fof(f66,plain,(
% 0.22/0.43    spl2_8),
% 0.22/0.43    inference(avatar_split_clause,[],[f27,f64])).
% 0.22/0.43  fof(f27,plain,(
% 0.22/0.43    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f13])).
% 0.22/0.43  fof(f13,plain,(
% 0.22/0.43    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.43    inference(ennf_transformation,[],[f6])).
% 0.22/0.43  fof(f6,axiom,(
% 0.22/0.43    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 0.22/0.43  fof(f62,plain,(
% 0.22/0.43    spl2_7),
% 0.22/0.43    inference(avatar_split_clause,[],[f26,f60])).
% 0.22/0.43  fof(f26,plain,(
% 0.22/0.43    ( ! [X0] : (k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f12])).
% 0.22/0.43  fof(f12,plain,(
% 0.22/0.43    ! [X0] : (k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 0.22/0.43    inference(ennf_transformation,[],[f5])).
% 0.22/0.43  fof(f5,axiom,(
% 0.22/0.43    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k7_relat_1(X0,k1_xboole_0))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_relat_1)).
% 0.22/0.43  fof(f58,plain,(
% 0.22/0.43    spl2_6),
% 0.22/0.43    inference(avatar_split_clause,[],[f25,f56])).
% 0.22/0.43  fof(f25,plain,(
% 0.22/0.43    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f1])).
% 0.22/0.43  fof(f1,axiom,(
% 0.22/0.43    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.43  fof(f54,plain,(
% 0.22/0.43    spl2_5),
% 0.22/0.43    inference(avatar_split_clause,[],[f24,f52])).
% 0.22/0.43  fof(f24,plain,(
% 0.22/0.43    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.22/0.43    inference(cnf_transformation,[],[f2])).
% 0.22/0.43  fof(f2,axiom,(
% 0.22/0.43    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.22/0.43  fof(f45,plain,(
% 0.22/0.43    spl2_3),
% 0.22/0.43    inference(avatar_split_clause,[],[f23,f42])).
% 0.22/0.43  fof(f23,plain,(
% 0.22/0.43    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.22/0.43    inference(cnf_transformation,[],[f7])).
% 0.22/0.43  fof(f7,axiom,(
% 0.22/0.43    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.22/0.43  fof(f40,plain,(
% 0.22/0.43    spl2_2),
% 0.22/0.43    inference(avatar_split_clause,[],[f21,f37])).
% 0.22/0.43  fof(f21,plain,(
% 0.22/0.43    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.22/0.43    inference(cnf_transformation,[],[f8])).
% 0.22/0.43  fof(f8,axiom,(
% 0.22/0.43    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).
% 0.22/0.43  fof(f35,plain,(
% 0.22/0.43    ~spl2_1),
% 0.22/0.43    inference(avatar_split_clause,[],[f20,f32])).
% 0.22/0.43  fof(f20,plain,(
% 0.22/0.43    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0)),
% 0.22/0.43    inference(cnf_transformation,[],[f17])).
% 0.22/0.43  fof(f17,plain,(
% 0.22/0.43    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0)),
% 0.22/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f16])).
% 0.22/0.43  fof(f16,plain,(
% 0.22/0.43    ? [X0] : k1_xboole_0 != k9_relat_1(k1_xboole_0,X0) => k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0)),
% 0.22/0.43    introduced(choice_axiom,[])).
% 0.22/0.43  fof(f11,plain,(
% 0.22/0.43    ? [X0] : k1_xboole_0 != k9_relat_1(k1_xboole_0,X0)),
% 0.22/0.43    inference(ennf_transformation,[],[f10])).
% 0.22/0.43  fof(f10,negated_conjecture,(
% 0.22/0.43    ~! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 0.22/0.43    inference(negated_conjecture,[],[f9])).
% 0.22/0.43  fof(f9,conjecture,(
% 0.22/0.43    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).
% 0.22/0.43  % SZS output end Proof for theBenchmark
% 0.22/0.43  % (5985)------------------------------
% 0.22/0.43  % (5985)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.43  % (5985)Termination reason: Refutation
% 0.22/0.43  
% 0.22/0.43  % (5985)Memory used [KB]: 10618
% 0.22/0.43  % (5985)Time elapsed: 0.006 s
% 0.22/0.43  % (5985)------------------------------
% 0.22/0.43  % (5985)------------------------------
% 0.22/0.43  % (5979)Success in time 0.065 s
%------------------------------------------------------------------------------
