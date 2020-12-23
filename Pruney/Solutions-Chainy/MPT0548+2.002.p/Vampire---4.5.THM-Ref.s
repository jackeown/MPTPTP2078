%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:22 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 125 expanded)
%              Number of leaves         :   27 (  60 expanded)
%              Depth                    :    6
%              Number of atoms          :  188 ( 264 expanded)
%              Number of equality atoms :   61 (  88 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f170,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f47,f52,f57,f62,f66,f70,f74,f80,f96,f101,f105,f115,f141,f158,f161,f165,f169])).

fof(f169,plain,
    ( spl1_1
    | ~ spl1_21
    | ~ spl1_22
    | ~ spl1_23 ),
    inference(avatar_contradiction_clause,[],[f168])).

% (15956)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
fof(f168,plain,
    ( $false
    | spl1_1
    | ~ spl1_21
    | ~ spl1_22
    | ~ spl1_23 ),
    inference(subsumption_resolution,[],[f46,f167])).

fof(f167,plain,
    ( ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)
    | ~ spl1_21
    | ~ spl1_22
    | ~ spl1_23 ),
    inference(forward_demodulation,[],[f166,f153])).

fof(f153,plain,
    ( k1_xboole_0 = k9_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ spl1_21 ),
    inference(avatar_component_clause,[],[f151])).

fof(f151,plain,
    ( spl1_21
  <=> k1_xboole_0 = k9_relat_1(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_21])])).

fof(f166,plain,
    ( ! [X0] : k9_relat_1(k1_xboole_0,X0) = k9_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ spl1_22
    | ~ spl1_23 ),
    inference(forward_demodulation,[],[f164,f157])).

fof(f157,plain,
    ( ! [X3] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X3)
    | ~ spl1_22 ),
    inference(avatar_component_clause,[],[f156])).

fof(f156,plain,
    ( spl1_22
  <=> ! [X3] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_22])])).

fof(f164,plain,
    ( ! [X0] : k9_relat_1(k1_xboole_0,X0) = k9_relat_1(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))
    | ~ spl1_23 ),
    inference(avatar_component_clause,[],[f163])).

fof(f163,plain,
    ( spl1_23
  <=> ! [X0] : k9_relat_1(k1_xboole_0,X0) = k9_relat_1(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_23])])).

fof(f46,plain,
    ( k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0)
    | spl1_1 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl1_1
  <=> k1_xboole_0 = k9_relat_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f165,plain,
    ( spl1_23
    | ~ spl1_3
    | ~ spl1_12
    | ~ spl1_15 ),
    inference(avatar_split_clause,[],[f125,f113,f98,f54,f163])).

fof(f54,plain,
    ( spl1_3
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f98,plain,
    ( spl1_12
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_12])])).

fof(f113,plain,
    ( spl1_15
  <=> ! [X1,X0] :
        ( k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_15])])).

fof(f125,plain,
    ( ! [X0] : k9_relat_1(k1_xboole_0,X0) = k9_relat_1(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))
    | ~ spl1_3
    | ~ spl1_12
    | ~ spl1_15 ),
    inference(forward_demodulation,[],[f123,f56])).

fof(f56,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f54])).

fof(f123,plain,
    ( ! [X0] : k9_relat_1(k1_xboole_0,X0) = k9_relat_1(k1_xboole_0,k3_xboole_0(k1_relat_1(k1_xboole_0),X0))
    | ~ spl1_12
    | ~ spl1_15 ),
    inference(unit_resulting_resolution,[],[f100,f114])).

fof(f114,plain,
    ( ! [X0,X1] :
        ( k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
        | ~ v1_relat_1(X1) )
    | ~ spl1_15 ),
    inference(avatar_component_clause,[],[f113])).

fof(f100,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl1_12 ),
    inference(avatar_component_clause,[],[f98])).

fof(f161,plain,
    ( spl1_21
    | ~ spl1_3
    | ~ spl1_4
    | ~ spl1_11
    | ~ spl1_12 ),
    inference(avatar_split_clause,[],[f118,f98,f94,f59,f54,f151])).

fof(f59,plain,
    ( spl1_4
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f94,plain,
    ( spl1_11
  <=> ! [X0] :
        ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).

fof(f118,plain,
    ( k1_xboole_0 = k9_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ spl1_3
    | ~ spl1_4
    | ~ spl1_11
    | ~ spl1_12 ),
    inference(forward_demodulation,[],[f117,f61])).

fof(f61,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl1_4 ),
    inference(avatar_component_clause,[],[f59])).

fof(f117,plain,
    ( k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ spl1_3
    | ~ spl1_11
    | ~ spl1_12 ),
    inference(forward_demodulation,[],[f116,f56])).

fof(f116,plain,
    ( k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,k1_relat_1(k1_xboole_0))
    | ~ spl1_11
    | ~ spl1_12 ),
    inference(unit_resulting_resolution,[],[f100,f95])).

fof(f95,plain,
    ( ! [X0] :
        ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl1_11 ),
    inference(avatar_component_clause,[],[f94])).

fof(f158,plain,
    ( spl1_22
    | ~ spl1_6
    | ~ spl1_13
    | ~ spl1_20 ),
    inference(avatar_split_clause,[],[f148,f139,f103,f68,f156])).

fof(f68,plain,
    ( spl1_6
  <=> ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f103,plain,
    ( spl1_13
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_13])])).

fof(f139,plain,
    ( spl1_20
  <=> ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_20])])).

fof(f148,plain,
    ( ! [X3] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X3)
    | ~ spl1_6
    | ~ spl1_13
    | ~ spl1_20 ),
    inference(forward_demodulation,[],[f144,f69])).

fof(f69,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)
    | ~ spl1_6 ),
    inference(avatar_component_clause,[],[f68])).

fof(f144,plain,
    ( ! [X3] : k3_xboole_0(k1_xboole_0,X3) = k4_xboole_0(k1_xboole_0,X3)
    | ~ spl1_13
    | ~ spl1_20 ),
    inference(superposition,[],[f140,f104])).

fof(f104,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))
    | ~ spl1_13 ),
    inference(avatar_component_clause,[],[f103])).

fof(f140,plain,
    ( ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0
    | ~ spl1_20 ),
    inference(avatar_component_clause,[],[f139])).

fof(f141,plain,
    ( spl1_20
    | ~ spl1_7
    | ~ spl1_8 ),
    inference(avatar_split_clause,[],[f89,f78,f72,f139])).

fof(f72,plain,
    ( spl1_7
  <=> ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).

fof(f78,plain,
    ( spl1_8
  <=> ! [X1,X0] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).

fof(f89,plain,
    ( ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0
    | ~ spl1_7
    | ~ spl1_8 ),
    inference(superposition,[],[f79,f73])).

fof(f73,plain,
    ( ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl1_7 ),
    inference(avatar_component_clause,[],[f72])).

fof(f79,plain,
    ( ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)
    | ~ spl1_8 ),
    inference(avatar_component_clause,[],[f78])).

fof(f115,plain,(
    spl1_15 ),
    inference(avatar_split_clause,[],[f37,f113])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_relat_1)).

fof(f105,plain,(
    spl1_13 ),
    inference(avatar_split_clause,[],[f36,f103])).

fof(f36,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f101,plain,
    ( spl1_12
    | ~ spl1_2
    | ~ spl1_5 ),
    inference(avatar_split_clause,[],[f75,f64,f49,f98])).

fof(f49,plain,
    ( spl1_2
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f64,plain,
    ( spl1_5
  <=> ! [X0] :
        ( v1_relat_1(X0)
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f75,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl1_2
    | ~ spl1_5 ),
    inference(unit_resulting_resolution,[],[f51,f65])).

fof(f65,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | v1_relat_1(X0) )
    | ~ spl1_5 ),
    inference(avatar_component_clause,[],[f64])).

fof(f51,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl1_2 ),
    inference(avatar_component_clause,[],[f49])).

fof(f96,plain,(
    spl1_11 ),
    inference(avatar_split_clause,[],[f32,f94])).

fof(f32,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

fof(f80,plain,(
    spl1_8 ),
    inference(avatar_split_clause,[],[f33,f78])).

fof(f33,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f74,plain,(
    spl1_7 ),
    inference(avatar_split_clause,[],[f30,f72])).

fof(f30,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f70,plain,(
    spl1_6 ),
    inference(avatar_split_clause,[],[f29,f68])).

fof(f29,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(f66,plain,(
    spl1_5 ),
    inference(avatar_split_clause,[],[f31,f64])).

fof(f31,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f62,plain,(
    spl1_4 ),
    inference(avatar_split_clause,[],[f28,f59])).

fof(f28,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f57,plain,(
    spl1_3 ),
    inference(avatar_split_clause,[],[f27,f54])).

fof(f27,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f16])).

fof(f52,plain,(
    spl1_2 ),
    inference(avatar_split_clause,[],[f26,f49])).

fof(f26,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f47,plain,(
    ~ spl1_1 ),
    inference(avatar_split_clause,[],[f25,f44])).

fof(f25,plain,(
    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f23])).

fof(f23,plain,
    ( ? [X0] : k1_xboole_0 != k9_relat_1(k1_xboole_0,X0)
   => k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0] : k1_xboole_0 != k9_relat_1(k1_xboole_0,X0) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:42:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.41  % (15957)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.45  % (15952)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.45  % (15952)Refutation found. Thanks to Tanya!
% 0.20/0.45  % SZS status Theorem for theBenchmark
% 0.20/0.45  % SZS output start Proof for theBenchmark
% 0.20/0.45  fof(f170,plain,(
% 0.20/0.45    $false),
% 0.20/0.45    inference(avatar_sat_refutation,[],[f47,f52,f57,f62,f66,f70,f74,f80,f96,f101,f105,f115,f141,f158,f161,f165,f169])).
% 0.20/0.45  fof(f169,plain,(
% 0.20/0.45    spl1_1 | ~spl1_21 | ~spl1_22 | ~spl1_23),
% 0.20/0.45    inference(avatar_contradiction_clause,[],[f168])).
% 0.20/0.46  % (15956)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.47  fof(f168,plain,(
% 0.20/0.47    $false | (spl1_1 | ~spl1_21 | ~spl1_22 | ~spl1_23)),
% 0.20/0.47    inference(subsumption_resolution,[],[f46,f167])).
% 0.20/0.47  fof(f167,plain,(
% 0.20/0.47    ( ! [X0] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)) ) | (~spl1_21 | ~spl1_22 | ~spl1_23)),
% 0.20/0.47    inference(forward_demodulation,[],[f166,f153])).
% 0.20/0.47  fof(f153,plain,(
% 0.20/0.47    k1_xboole_0 = k9_relat_1(k1_xboole_0,k1_xboole_0) | ~spl1_21),
% 0.20/0.47    inference(avatar_component_clause,[],[f151])).
% 0.20/0.47  fof(f151,plain,(
% 0.20/0.47    spl1_21 <=> k1_xboole_0 = k9_relat_1(k1_xboole_0,k1_xboole_0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_21])])).
% 0.20/0.47  fof(f166,plain,(
% 0.20/0.47    ( ! [X0] : (k9_relat_1(k1_xboole_0,X0) = k9_relat_1(k1_xboole_0,k1_xboole_0)) ) | (~spl1_22 | ~spl1_23)),
% 0.20/0.47    inference(forward_demodulation,[],[f164,f157])).
% 0.20/0.47  fof(f157,plain,(
% 0.20/0.47    ( ! [X3] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X3)) ) | ~spl1_22),
% 0.20/0.47    inference(avatar_component_clause,[],[f156])).
% 0.20/0.47  fof(f156,plain,(
% 0.20/0.47    spl1_22 <=> ! [X3] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X3)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_22])])).
% 0.20/0.47  fof(f164,plain,(
% 0.20/0.47    ( ! [X0] : (k9_relat_1(k1_xboole_0,X0) = k9_relat_1(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) ) | ~spl1_23),
% 0.20/0.47    inference(avatar_component_clause,[],[f163])).
% 0.20/0.47  fof(f163,plain,(
% 0.20/0.47    spl1_23 <=> ! [X0] : k9_relat_1(k1_xboole_0,X0) = k9_relat_1(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_23])])).
% 0.20/0.47  fof(f46,plain,(
% 0.20/0.47    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0) | spl1_1),
% 0.20/0.47    inference(avatar_component_clause,[],[f44])).
% 0.20/0.47  fof(f44,plain,(
% 0.20/0.47    spl1_1 <=> k1_xboole_0 = k9_relat_1(k1_xboole_0,sK0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.20/0.47  fof(f165,plain,(
% 0.20/0.47    spl1_23 | ~spl1_3 | ~spl1_12 | ~spl1_15),
% 0.20/0.47    inference(avatar_split_clause,[],[f125,f113,f98,f54,f163])).
% 0.20/0.47  fof(f54,plain,(
% 0.20/0.47    spl1_3 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.20/0.47  fof(f98,plain,(
% 0.20/0.47    spl1_12 <=> v1_relat_1(k1_xboole_0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_12])])).
% 0.20/0.47  fof(f113,plain,(
% 0.20/0.47    spl1_15 <=> ! [X1,X0] : (k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_15])])).
% 0.20/0.47  fof(f125,plain,(
% 0.20/0.47    ( ! [X0] : (k9_relat_1(k1_xboole_0,X0) = k9_relat_1(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) ) | (~spl1_3 | ~spl1_12 | ~spl1_15)),
% 0.20/0.47    inference(forward_demodulation,[],[f123,f56])).
% 0.20/0.47  fof(f56,plain,(
% 0.20/0.47    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl1_3),
% 0.20/0.47    inference(avatar_component_clause,[],[f54])).
% 0.20/0.47  fof(f123,plain,(
% 0.20/0.47    ( ! [X0] : (k9_relat_1(k1_xboole_0,X0) = k9_relat_1(k1_xboole_0,k3_xboole_0(k1_relat_1(k1_xboole_0),X0))) ) | (~spl1_12 | ~spl1_15)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f100,f114])).
% 0.20/0.47  fof(f114,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1)) ) | ~spl1_15),
% 0.20/0.47    inference(avatar_component_clause,[],[f113])).
% 0.20/0.47  fof(f100,plain,(
% 0.20/0.47    v1_relat_1(k1_xboole_0) | ~spl1_12),
% 0.20/0.47    inference(avatar_component_clause,[],[f98])).
% 0.20/0.47  fof(f161,plain,(
% 0.20/0.47    spl1_21 | ~spl1_3 | ~spl1_4 | ~spl1_11 | ~spl1_12),
% 0.20/0.47    inference(avatar_split_clause,[],[f118,f98,f94,f59,f54,f151])).
% 0.20/0.47  fof(f59,plain,(
% 0.20/0.47    spl1_4 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.20/0.47  fof(f94,plain,(
% 0.20/0.47    spl1_11 <=> ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).
% 0.20/0.47  fof(f118,plain,(
% 0.20/0.47    k1_xboole_0 = k9_relat_1(k1_xboole_0,k1_xboole_0) | (~spl1_3 | ~spl1_4 | ~spl1_11 | ~spl1_12)),
% 0.20/0.47    inference(forward_demodulation,[],[f117,f61])).
% 0.20/0.47  fof(f61,plain,(
% 0.20/0.47    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl1_4),
% 0.20/0.47    inference(avatar_component_clause,[],[f59])).
% 0.20/0.47  fof(f117,plain,(
% 0.20/0.47    k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,k1_xboole_0) | (~spl1_3 | ~spl1_11 | ~spl1_12)),
% 0.20/0.47    inference(forward_demodulation,[],[f116,f56])).
% 0.20/0.47  fof(f116,plain,(
% 0.20/0.47    k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,k1_relat_1(k1_xboole_0)) | (~spl1_11 | ~spl1_12)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f100,f95])).
% 0.20/0.47  fof(f95,plain,(
% 0.20/0.47    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) ) | ~spl1_11),
% 0.20/0.47    inference(avatar_component_clause,[],[f94])).
% 0.20/0.47  fof(f158,plain,(
% 0.20/0.47    spl1_22 | ~spl1_6 | ~spl1_13 | ~spl1_20),
% 0.20/0.47    inference(avatar_split_clause,[],[f148,f139,f103,f68,f156])).
% 0.20/0.47  fof(f68,plain,(
% 0.20/0.47    spl1_6 <=> ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 0.20/0.47  fof(f103,plain,(
% 0.20/0.47    spl1_13 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_13])])).
% 0.20/0.47  fof(f139,plain,(
% 0.20/0.47    spl1_20 <=> ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_20])])).
% 0.20/0.47  fof(f148,plain,(
% 0.20/0.47    ( ! [X3] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X3)) ) | (~spl1_6 | ~spl1_13 | ~spl1_20)),
% 0.20/0.47    inference(forward_demodulation,[],[f144,f69])).
% 0.20/0.47  fof(f69,plain,(
% 0.20/0.47    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) ) | ~spl1_6),
% 0.20/0.47    inference(avatar_component_clause,[],[f68])).
% 0.20/0.47  fof(f144,plain,(
% 0.20/0.47    ( ! [X3] : (k3_xboole_0(k1_xboole_0,X3) = k4_xboole_0(k1_xboole_0,X3)) ) | (~spl1_13 | ~spl1_20)),
% 0.20/0.47    inference(superposition,[],[f140,f104])).
% 0.20/0.47  fof(f104,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) | ~spl1_13),
% 0.20/0.47    inference(avatar_component_clause,[],[f103])).
% 0.20/0.47  fof(f140,plain,(
% 0.20/0.47    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) ) | ~spl1_20),
% 0.20/0.47    inference(avatar_component_clause,[],[f139])).
% 0.20/0.47  fof(f141,plain,(
% 0.20/0.47    spl1_20 | ~spl1_7 | ~spl1_8),
% 0.20/0.47    inference(avatar_split_clause,[],[f89,f78,f72,f139])).
% 0.20/0.47  fof(f72,plain,(
% 0.20/0.47    spl1_7 <=> ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).
% 0.20/0.47  fof(f78,plain,(
% 0.20/0.47    spl1_8 <=> ! [X1,X0] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).
% 0.20/0.47  fof(f89,plain,(
% 0.20/0.47    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) ) | (~spl1_7 | ~spl1_8)),
% 0.20/0.47    inference(superposition,[],[f79,f73])).
% 0.20/0.47  fof(f73,plain,(
% 0.20/0.47    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl1_7),
% 0.20/0.47    inference(avatar_component_clause,[],[f72])).
% 0.20/0.47  fof(f79,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) ) | ~spl1_8),
% 0.20/0.47    inference(avatar_component_clause,[],[f78])).
% 0.20/0.47  fof(f115,plain,(
% 0.20/0.47    spl1_15),
% 0.20/0.47    inference(avatar_split_clause,[],[f37,f113])).
% 0.20/0.47  fof(f37,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f22])).
% 0.20/0.47  fof(f22,plain,(
% 0.20/0.47    ! [X0,X1] : (k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.47    inference(ennf_transformation,[],[f14])).
% 0.20/0.47  fof(f14,axiom,(
% 0.20/0.47    ! [X0,X1] : (v1_relat_1(X1) => k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_relat_1)).
% 0.20/0.47  fof(f105,plain,(
% 0.20/0.47    spl1_13),
% 0.20/0.47    inference(avatar_split_clause,[],[f36,f103])).
% 0.20/0.47  fof(f36,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f3])).
% 0.20/0.47  fof(f3,axiom,(
% 0.20/0.47    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.20/0.47  fof(f101,plain,(
% 0.20/0.47    spl1_12 | ~spl1_2 | ~spl1_5),
% 0.20/0.47    inference(avatar_split_clause,[],[f75,f64,f49,f98])).
% 0.20/0.47  fof(f49,plain,(
% 0.20/0.47    spl1_2 <=> v1_xboole_0(k1_xboole_0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.20/0.47  fof(f64,plain,(
% 0.20/0.47    spl1_5 <=> ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.20/0.47  fof(f75,plain,(
% 0.20/0.47    v1_relat_1(k1_xboole_0) | (~spl1_2 | ~spl1_5)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f51,f65])).
% 0.20/0.47  fof(f65,plain,(
% 0.20/0.47    ( ! [X0] : (~v1_xboole_0(X0) | v1_relat_1(X0)) ) | ~spl1_5),
% 0.20/0.47    inference(avatar_component_clause,[],[f64])).
% 0.20/0.47  fof(f51,plain,(
% 0.20/0.47    v1_xboole_0(k1_xboole_0) | ~spl1_2),
% 0.20/0.47    inference(avatar_component_clause,[],[f49])).
% 0.20/0.47  fof(f96,plain,(
% 0.20/0.47    spl1_11),
% 0.20/0.47    inference(avatar_split_clause,[],[f32,f94])).
% 0.20/0.47  fof(f32,plain,(
% 0.20/0.47    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f21])).
% 0.20/0.47  fof(f21,plain,(
% 0.20/0.47    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f15])).
% 0.20/0.47  fof(f15,axiom,(
% 0.20/0.47    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).
% 0.20/0.47  fof(f80,plain,(
% 0.20/0.47    spl1_8),
% 0.20/0.47    inference(avatar_split_clause,[],[f33,f78])).
% 0.20/0.47  fof(f33,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f1])).
% 0.20/0.47  fof(f1,axiom,(
% 0.20/0.47    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 0.20/0.47  fof(f74,plain,(
% 0.20/0.47    spl1_7),
% 0.20/0.47    inference(avatar_split_clause,[],[f30,f72])).
% 0.20/0.47  fof(f30,plain,(
% 0.20/0.47    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.47    inference(cnf_transformation,[],[f5])).
% 0.20/0.47  fof(f5,axiom,(
% 0.20/0.47    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 0.20/0.47  fof(f70,plain,(
% 0.20/0.47    spl1_6),
% 0.20/0.47    inference(avatar_split_clause,[],[f29,f68])).
% 0.20/0.47  fof(f29,plain,(
% 0.20/0.47    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f4])).
% 0.20/0.47  fof(f4,axiom,(
% 0.20/0.47    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).
% 0.20/0.47  fof(f66,plain,(
% 0.20/0.47    spl1_5),
% 0.20/0.47    inference(avatar_split_clause,[],[f31,f64])).
% 0.20/0.47  fof(f31,plain,(
% 0.20/0.47    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f20])).
% 0.20/0.47  fof(f20,plain,(
% 0.20/0.47    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f13])).
% 0.20/0.47  fof(f13,axiom,(
% 0.20/0.47    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).
% 0.20/0.47  fof(f62,plain,(
% 0.20/0.47    spl1_4),
% 0.20/0.47    inference(avatar_split_clause,[],[f28,f59])).
% 0.20/0.47  fof(f28,plain,(
% 0.20/0.47    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.20/0.47    inference(cnf_transformation,[],[f16])).
% 0.20/0.47  fof(f16,axiom,(
% 0.20/0.47    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.20/0.47  fof(f57,plain,(
% 0.20/0.47    spl1_3),
% 0.20/0.47    inference(avatar_split_clause,[],[f27,f54])).
% 0.20/0.47  fof(f27,plain,(
% 0.20/0.47    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.47    inference(cnf_transformation,[],[f16])).
% 0.20/0.47  fof(f52,plain,(
% 0.20/0.47    spl1_2),
% 0.20/0.47    inference(avatar_split_clause,[],[f26,f49])).
% 0.20/0.47  fof(f26,plain,(
% 0.20/0.47    v1_xboole_0(k1_xboole_0)),
% 0.20/0.47    inference(cnf_transformation,[],[f2])).
% 0.20/0.47  fof(f2,axiom,(
% 0.20/0.47    v1_xboole_0(k1_xboole_0)),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.47  fof(f47,plain,(
% 0.20/0.47    ~spl1_1),
% 0.20/0.47    inference(avatar_split_clause,[],[f25,f44])).
% 0.20/0.47  fof(f25,plain,(
% 0.20/0.47    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f24])).
% 0.20/0.47  fof(f24,plain,(
% 0.20/0.47    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0)),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f23])).
% 0.20/0.47  fof(f23,plain,(
% 0.20/0.47    ? [X0] : k1_xboole_0 != k9_relat_1(k1_xboole_0,X0) => k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0)),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f19,plain,(
% 0.20/0.47    ? [X0] : k1_xboole_0 != k9_relat_1(k1_xboole_0,X0)),
% 0.20/0.47    inference(ennf_transformation,[],[f18])).
% 0.20/0.47  fof(f18,negated_conjecture,(
% 0.20/0.47    ~! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 0.20/0.47    inference(negated_conjecture,[],[f17])).
% 0.20/0.47  fof(f17,conjecture,(
% 0.20/0.47    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (15952)------------------------------
% 0.20/0.47  % (15952)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (15952)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (15952)Memory used [KB]: 6140
% 0.20/0.47  % (15952)Time elapsed: 0.052 s
% 0.20/0.47  % (15952)------------------------------
% 0.20/0.47  % (15952)------------------------------
% 0.20/0.47  % (15961)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.47  % (15946)Success in time 0.112 s
%------------------------------------------------------------------------------
