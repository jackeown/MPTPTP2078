%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:47 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 114 expanded)
%              Number of leaves         :   25 (  53 expanded)
%              Depth                    :    8
%              Number of atoms          :  181 ( 248 expanded)
%              Number of equality atoms :   59 (  88 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f159,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f44,f48,f53,f57,f61,f65,f71,f75,f87,f91,f103,f111,f134,f146,f155])).

fof(f155,plain,
    ( spl1_1
    | ~ spl1_4
    | ~ spl1_7
    | ~ spl1_8
    | ~ spl1_11
    | ~ spl1_16
    | ~ spl1_20
    | ~ spl1_22 ),
    inference(avatar_contradiction_clause,[],[f154])).

fof(f154,plain,
    ( $false
    | spl1_1
    | ~ spl1_4
    | ~ spl1_7
    | ~ spl1_8
    | ~ spl1_11
    | ~ spl1_16
    | ~ spl1_20
    | ~ spl1_22 ),
    inference(subsumption_resolution,[],[f43,f153])).

fof(f153,plain,
    ( ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)
    | ~ spl1_4
    | ~ spl1_7
    | ~ spl1_8
    | ~ spl1_11
    | ~ spl1_16
    | ~ spl1_20
    | ~ spl1_22 ),
    inference(forward_demodulation,[],[f152,f56])).

fof(f56,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)
    | ~ spl1_4 ),
    inference(avatar_component_clause,[],[f55])).

fof(f55,plain,
    ( spl1_4
  <=> ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f152,plain,
    ( ! [X0] : k7_relat_1(k1_xboole_0,X0) = k4_xboole_0(k1_xboole_0,k2_zfmisc_1(X0,k2_relat_1(k1_xboole_0)))
    | ~ spl1_7
    | ~ spl1_8
    | ~ spl1_11
    | ~ spl1_16
    | ~ spl1_20
    | ~ spl1_22 ),
    inference(forward_demodulation,[],[f148,f136])).

fof(f136,plain,
    ( ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0
    | ~ spl1_8
    | ~ spl1_11
    | ~ spl1_16
    | ~ spl1_20 ),
    inference(forward_demodulation,[],[f135,f127])).

fof(f127,plain,
    ( ! [X1] : k2_xboole_0(k1_xboole_0,X1) = X1
    | ~ spl1_8
    | ~ spl1_16 ),
    inference(superposition,[],[f110,f74])).

fof(f74,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)
    | ~ spl1_8 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl1_8
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).

fof(f110,plain,
    ( ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl1_16 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl1_16
  <=> ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_16])])).

fof(f135,plain,
    ( ! [X0] : k2_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,X0)
    | ~ spl1_11
    | ~ spl1_20 ),
    inference(superposition,[],[f86,f133])).

fof(f133,plain,
    ( ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl1_20 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl1_20
  <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_20])])).

fof(f86,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))
    | ~ spl1_11 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl1_11
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).

fof(f148,plain,
    ( ! [X0] : k4_xboole_0(k1_xboole_0,k2_zfmisc_1(X0,k2_relat_1(k1_xboole_0))) = k5_xboole_0(k1_xboole_0,k7_relat_1(k1_xboole_0,X0))
    | ~ spl1_7
    | ~ spl1_22 ),
    inference(unit_resulting_resolution,[],[f70,f145])).

fof(f145,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(X0,k2_zfmisc_1(X1,k2_relat_1(X0))) = k5_xboole_0(X0,k7_relat_1(X0,X1))
        | ~ v1_relat_1(X0) )
    | ~ spl1_22 ),
    inference(avatar_component_clause,[],[f144])).

fof(f144,plain,
    ( spl1_22
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,k2_zfmisc_1(X1,k2_relat_1(X0))) = k5_xboole_0(X0,k7_relat_1(X0,X1))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_22])])).

fof(f70,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl1_7 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl1_7
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).

fof(f43,plain,
    ( k1_xboole_0 != k7_relat_1(k1_xboole_0,sK0)
    | spl1_1 ),
    inference(avatar_component_clause,[],[f41])).

fof(f41,plain,
    ( spl1_1
  <=> k1_xboole_0 = k7_relat_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f146,plain,
    ( spl1_22
    | ~ spl1_12
    | ~ spl1_14 ),
    inference(avatar_split_clause,[],[f114,f101,f89,f144])).

fof(f89,plain,
    ( spl1_12
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_12])])).

fof(f101,plain,
    ( spl1_14
  <=> ! [X1,X0] :
        ( k7_relat_1(X1,X0) = k3_xboole_0(X1,k2_zfmisc_1(X0,k2_relat_1(X1)))
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_14])])).

fof(f114,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(X0,k2_zfmisc_1(X1,k2_relat_1(X0))) = k5_xboole_0(X0,k7_relat_1(X0,X1))
        | ~ v1_relat_1(X0) )
    | ~ spl1_12
    | ~ spl1_14 ),
    inference(superposition,[],[f90,f102])).

fof(f102,plain,
    ( ! [X0,X1] :
        ( k7_relat_1(X1,X0) = k3_xboole_0(X1,k2_zfmisc_1(X0,k2_relat_1(X1)))
        | ~ v1_relat_1(X1) )
    | ~ spl1_14 ),
    inference(avatar_component_clause,[],[f101])).

fof(f90,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))
    | ~ spl1_12 ),
    inference(avatar_component_clause,[],[f89])).

fof(f134,plain,
    ( spl1_20
    | ~ spl1_5
    | ~ spl1_6
    | ~ spl1_12 ),
    inference(avatar_split_clause,[],[f99,f89,f63,f59,f132])).

fof(f59,plain,
    ( spl1_5
  <=> ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f63,plain,
    ( spl1_6
  <=> ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f99,plain,
    ( ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl1_5
    | ~ spl1_6
    | ~ spl1_12 ),
    inference(forward_demodulation,[],[f98,f64])).

fof(f64,plain,
    ( ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl1_6 ),
    inference(avatar_component_clause,[],[f63])).

fof(f98,plain,
    ( ! [X0] : k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0)
    | ~ spl1_5
    | ~ spl1_12 ),
    inference(superposition,[],[f90,f60])).

fof(f60,plain,
    ( ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)
    | ~ spl1_5 ),
    inference(avatar_component_clause,[],[f59])).

fof(f111,plain,
    ( spl1_16
    | ~ spl1_4
    | ~ spl1_6
    | ~ spl1_11 ),
    inference(avatar_split_clause,[],[f97,f85,f63,f55,f109])).

fof(f97,plain,
    ( ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl1_4
    | ~ spl1_6
    | ~ spl1_11 ),
    inference(forward_demodulation,[],[f96,f64])).

fof(f96,plain,
    ( ! [X0] : k5_xboole_0(X0,k1_xboole_0) = k2_xboole_0(X0,k1_xboole_0)
    | ~ spl1_4
    | ~ spl1_11 ),
    inference(superposition,[],[f86,f56])).

fof(f103,plain,(
    spl1_14 ),
    inference(avatar_split_clause,[],[f34,f101])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k3_xboole_0(X1,k2_zfmisc_1(X0,k2_relat_1(X1)))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k3_xboole_0(X1,k2_zfmisc_1(X0,k2_relat_1(X1)))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k3_xboole_0(X1,k2_zfmisc_1(X0,k2_relat_1(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_relat_1)).

fof(f91,plain,(
    spl1_12 ),
    inference(avatar_split_clause,[],[f33,f89])).

fof(f33,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f87,plain,(
    spl1_11 ),
    inference(avatar_split_clause,[],[f32,f85])).

fof(f32,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f75,plain,(
    spl1_8 ),
    inference(avatar_split_clause,[],[f29,f73])).

fof(f29,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f71,plain,
    ( spl1_7
    | ~ spl1_2
    | ~ spl1_3 ),
    inference(avatar_split_clause,[],[f66,f50,f46,f68])).

fof(f46,plain,
    ( spl1_2
  <=> ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f50,plain,
    ( spl1_3
  <=> k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f66,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl1_2
    | ~ spl1_3 ),
    inference(superposition,[],[f47,f52])).

fof(f52,plain,
    ( k1_xboole_0 = k6_relat_1(k1_xboole_0)
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f50])).

fof(f47,plain,
    ( ! [X0] : v1_relat_1(k6_relat_1(X0))
    | ~ spl1_2 ),
    inference(avatar_component_clause,[],[f46])).

fof(f65,plain,(
    spl1_6 ),
    inference(avatar_split_clause,[],[f28,f63])).

fof(f28,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f61,plain,(
    spl1_5 ),
    inference(avatar_split_clause,[],[f27,f59])).

fof(f27,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f57,plain,(
    spl1_4 ),
    inference(avatar_split_clause,[],[f26,f55])).

fof(f26,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(f53,plain,(
    spl1_3 ),
    inference(avatar_split_clause,[],[f24,f50])).

fof(f24,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

fof(f48,plain,(
    spl1_2 ),
    inference(avatar_split_clause,[],[f25,f46])).

fof(f25,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f44,plain,(
    ~ spl1_1 ),
    inference(avatar_split_clause,[],[f23,f41])).

fof(f23,plain,(
    k1_xboole_0 != k7_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    k1_xboole_0 != k7_relat_1(k1_xboole_0,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f21])).

fof(f21,plain,
    ( ? [X0] : k1_xboole_0 != k7_relat_1(k1_xboole_0,X0)
   => k1_xboole_0 != k7_relat_1(k1_xboole_0,sK0) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0] : k1_xboole_0 != k7_relat_1(k1_xboole_0,X0) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:55:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.46  % (31655)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.46  % (31647)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.47  % (31658)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.47  % (31647)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f159,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f44,f48,f53,f57,f61,f65,f71,f75,f87,f91,f103,f111,f134,f146,f155])).
% 0.21/0.47  fof(f155,plain,(
% 0.21/0.47    spl1_1 | ~spl1_4 | ~spl1_7 | ~spl1_8 | ~spl1_11 | ~spl1_16 | ~spl1_20 | ~spl1_22),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f154])).
% 0.21/0.47  fof(f154,plain,(
% 0.21/0.47    $false | (spl1_1 | ~spl1_4 | ~spl1_7 | ~spl1_8 | ~spl1_11 | ~spl1_16 | ~spl1_20 | ~spl1_22)),
% 0.21/0.47    inference(subsumption_resolution,[],[f43,f153])).
% 0.21/0.47  fof(f153,plain,(
% 0.21/0.47    ( ! [X0] : (k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)) ) | (~spl1_4 | ~spl1_7 | ~spl1_8 | ~spl1_11 | ~spl1_16 | ~spl1_20 | ~spl1_22)),
% 0.21/0.47    inference(forward_demodulation,[],[f152,f56])).
% 0.21/0.47  fof(f56,plain,(
% 0.21/0.47    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) ) | ~spl1_4),
% 0.21/0.47    inference(avatar_component_clause,[],[f55])).
% 0.21/0.47  fof(f55,plain,(
% 0.21/0.47    spl1_4 <=> ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.21/0.47  fof(f152,plain,(
% 0.21/0.47    ( ! [X0] : (k7_relat_1(k1_xboole_0,X0) = k4_xboole_0(k1_xboole_0,k2_zfmisc_1(X0,k2_relat_1(k1_xboole_0)))) ) | (~spl1_7 | ~spl1_8 | ~spl1_11 | ~spl1_16 | ~spl1_20 | ~spl1_22)),
% 0.21/0.47    inference(forward_demodulation,[],[f148,f136])).
% 0.21/0.47  fof(f136,plain,(
% 0.21/0.47    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) ) | (~spl1_8 | ~spl1_11 | ~spl1_16 | ~spl1_20)),
% 0.21/0.47    inference(forward_demodulation,[],[f135,f127])).
% 0.21/0.47  fof(f127,plain,(
% 0.21/0.47    ( ! [X1] : (k2_xboole_0(k1_xboole_0,X1) = X1) ) | (~spl1_8 | ~spl1_16)),
% 0.21/0.47    inference(superposition,[],[f110,f74])).
% 0.21/0.47  fof(f74,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) ) | ~spl1_8),
% 0.21/0.47    inference(avatar_component_clause,[],[f73])).
% 0.21/0.47  fof(f73,plain,(
% 0.21/0.47    spl1_8 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).
% 0.21/0.47  fof(f110,plain,(
% 0.21/0.47    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl1_16),
% 0.21/0.47    inference(avatar_component_clause,[],[f109])).
% 0.21/0.47  fof(f109,plain,(
% 0.21/0.47    spl1_16 <=> ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_16])])).
% 0.21/0.47  fof(f135,plain,(
% 0.21/0.47    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,X0)) ) | (~spl1_11 | ~spl1_20)),
% 0.21/0.47    inference(superposition,[],[f86,f133])).
% 0.21/0.47  fof(f133,plain,(
% 0.21/0.47    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl1_20),
% 0.21/0.47    inference(avatar_component_clause,[],[f132])).
% 0.21/0.47  fof(f132,plain,(
% 0.21/0.47    spl1_20 <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_20])])).
% 0.21/0.47  fof(f86,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) ) | ~spl1_11),
% 0.21/0.47    inference(avatar_component_clause,[],[f85])).
% 0.21/0.47  fof(f85,plain,(
% 0.21/0.47    spl1_11 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).
% 0.21/0.47  fof(f148,plain,(
% 0.21/0.47    ( ! [X0] : (k4_xboole_0(k1_xboole_0,k2_zfmisc_1(X0,k2_relat_1(k1_xboole_0))) = k5_xboole_0(k1_xboole_0,k7_relat_1(k1_xboole_0,X0))) ) | (~spl1_7 | ~spl1_22)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f70,f145])).
% 0.21/0.47  fof(f145,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,k2_zfmisc_1(X1,k2_relat_1(X0))) = k5_xboole_0(X0,k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) ) | ~spl1_22),
% 0.21/0.47    inference(avatar_component_clause,[],[f144])).
% 0.21/0.47  fof(f144,plain,(
% 0.21/0.47    spl1_22 <=> ! [X1,X0] : (k4_xboole_0(X0,k2_zfmisc_1(X1,k2_relat_1(X0))) = k5_xboole_0(X0,k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_22])])).
% 0.21/0.47  fof(f70,plain,(
% 0.21/0.47    v1_relat_1(k1_xboole_0) | ~spl1_7),
% 0.21/0.47    inference(avatar_component_clause,[],[f68])).
% 0.21/0.47  fof(f68,plain,(
% 0.21/0.47    spl1_7 <=> v1_relat_1(k1_xboole_0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).
% 0.21/0.47  fof(f43,plain,(
% 0.21/0.47    k1_xboole_0 != k7_relat_1(k1_xboole_0,sK0) | spl1_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f41])).
% 0.21/0.47  fof(f41,plain,(
% 0.21/0.47    spl1_1 <=> k1_xboole_0 = k7_relat_1(k1_xboole_0,sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.21/0.47  fof(f146,plain,(
% 0.21/0.47    spl1_22 | ~spl1_12 | ~spl1_14),
% 0.21/0.47    inference(avatar_split_clause,[],[f114,f101,f89,f144])).
% 0.21/0.47  fof(f89,plain,(
% 0.21/0.47    spl1_12 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_12])])).
% 0.21/0.47  fof(f101,plain,(
% 0.21/0.47    spl1_14 <=> ! [X1,X0] : (k7_relat_1(X1,X0) = k3_xboole_0(X1,k2_zfmisc_1(X0,k2_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_14])])).
% 0.21/0.47  fof(f114,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,k2_zfmisc_1(X1,k2_relat_1(X0))) = k5_xboole_0(X0,k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) ) | (~spl1_12 | ~spl1_14)),
% 0.21/0.47    inference(superposition,[],[f90,f102])).
% 0.21/0.47  fof(f102,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k3_xboole_0(X1,k2_zfmisc_1(X0,k2_relat_1(X1))) | ~v1_relat_1(X1)) ) | ~spl1_14),
% 0.21/0.47    inference(avatar_component_clause,[],[f101])).
% 0.21/0.47  fof(f90,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) | ~spl1_12),
% 0.21/0.47    inference(avatar_component_clause,[],[f89])).
% 0.21/0.47  fof(f134,plain,(
% 0.21/0.47    spl1_20 | ~spl1_5 | ~spl1_6 | ~spl1_12),
% 0.21/0.47    inference(avatar_split_clause,[],[f99,f89,f63,f59,f132])).
% 0.21/0.47  fof(f59,plain,(
% 0.21/0.47    spl1_5 <=> ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.21/0.47  fof(f63,plain,(
% 0.21/0.47    spl1_6 <=> ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 0.21/0.47  fof(f99,plain,(
% 0.21/0.47    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) ) | (~spl1_5 | ~spl1_6 | ~spl1_12)),
% 0.21/0.47    inference(forward_demodulation,[],[f98,f64])).
% 0.21/0.47  fof(f64,plain,(
% 0.21/0.47    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl1_6),
% 0.21/0.47    inference(avatar_component_clause,[],[f63])).
% 0.21/0.47  fof(f98,plain,(
% 0.21/0.47    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0)) ) | (~spl1_5 | ~spl1_12)),
% 0.21/0.47    inference(superposition,[],[f90,f60])).
% 0.21/0.47  fof(f60,plain,(
% 0.21/0.47    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) ) | ~spl1_5),
% 0.21/0.47    inference(avatar_component_clause,[],[f59])).
% 0.21/0.47  fof(f111,plain,(
% 0.21/0.47    spl1_16 | ~spl1_4 | ~spl1_6 | ~spl1_11),
% 0.21/0.47    inference(avatar_split_clause,[],[f97,f85,f63,f55,f109])).
% 0.21/0.47  fof(f97,plain,(
% 0.21/0.47    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) ) | (~spl1_4 | ~spl1_6 | ~spl1_11)),
% 0.21/0.47    inference(forward_demodulation,[],[f96,f64])).
% 0.21/0.47  fof(f96,plain,(
% 0.21/0.47    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = k2_xboole_0(X0,k1_xboole_0)) ) | (~spl1_4 | ~spl1_11)),
% 0.21/0.47    inference(superposition,[],[f86,f56])).
% 0.21/0.47  fof(f103,plain,(
% 0.21/0.47    spl1_14),
% 0.21/0.47    inference(avatar_split_clause,[],[f34,f101])).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k3_xboole_0(X1,k2_zfmisc_1(X0,k2_relat_1(X1))) | ~v1_relat_1(X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f20])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ! [X0,X1] : (k7_relat_1(X1,X0) = k3_xboole_0(X1,k2_zfmisc_1(X0,k2_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f16])).
% 0.21/0.47  fof(f16,axiom,(
% 0.21/0.47    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k3_xboole_0(X1,k2_zfmisc_1(X0,k2_relat_1(X1))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_relat_1)).
% 0.21/0.47  fof(f91,plain,(
% 0.21/0.47    spl1_12),
% 0.21/0.47    inference(avatar_split_clause,[],[f33,f89])).
% 0.21/0.47  fof(f33,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.47  fof(f87,plain,(
% 0.21/0.47    spl1_11),
% 0.21/0.47    inference(avatar_split_clause,[],[f32,f85])).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,axiom,(
% 0.21/0.47    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.21/0.47  fof(f75,plain,(
% 0.21/0.47    spl1_8),
% 0.21/0.47    inference(avatar_split_clause,[],[f29,f73])).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.21/0.47  fof(f71,plain,(
% 0.21/0.47    spl1_7 | ~spl1_2 | ~spl1_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f66,f50,f46,f68])).
% 0.21/0.47  fof(f46,plain,(
% 0.21/0.47    spl1_2 <=> ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.21/0.47  fof(f50,plain,(
% 0.21/0.47    spl1_3 <=> k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.21/0.47  fof(f66,plain,(
% 0.21/0.47    v1_relat_1(k1_xboole_0) | (~spl1_2 | ~spl1_3)),
% 0.21/0.47    inference(superposition,[],[f47,f52])).
% 0.21/0.47  fof(f52,plain,(
% 0.21/0.47    k1_xboole_0 = k6_relat_1(k1_xboole_0) | ~spl1_3),
% 0.21/0.47    inference(avatar_component_clause,[],[f50])).
% 0.21/0.47  fof(f47,plain,(
% 0.21/0.47    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) ) | ~spl1_2),
% 0.21/0.47    inference(avatar_component_clause,[],[f46])).
% 0.21/0.47  fof(f65,plain,(
% 0.21/0.47    spl1_6),
% 0.21/0.47    inference(avatar_split_clause,[],[f28,f63])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.47    inference(cnf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,axiom,(
% 0.21/0.47    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 0.21/0.47  fof(f61,plain,(
% 0.21/0.47    spl1_5),
% 0.21/0.47    inference(avatar_split_clause,[],[f27,f59])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 0.21/0.47  fof(f57,plain,(
% 0.21/0.47    spl1_4),
% 0.21/0.47    inference(avatar_split_clause,[],[f26,f55])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).
% 0.21/0.47  fof(f53,plain,(
% 0.21/0.47    spl1_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f24,f50])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.21/0.47    inference(cnf_transformation,[],[f15])).
% 0.21/0.47  fof(f15,axiom,(
% 0.21/0.47    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).
% 0.21/0.47  fof(f48,plain,(
% 0.21/0.47    spl1_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f25,f46])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f14])).
% 0.21/0.47  fof(f14,axiom,(
% 0.21/0.47    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.21/0.47  fof(f44,plain,(
% 0.21/0.47    ~spl1_1),
% 0.21/0.47    inference(avatar_split_clause,[],[f23,f41])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    k1_xboole_0 != k7_relat_1(k1_xboole_0,sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f22])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    k1_xboole_0 != k7_relat_1(k1_xboole_0,sK0)),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f21])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    ? [X0] : k1_xboole_0 != k7_relat_1(k1_xboole_0,X0) => k1_xboole_0 != k7_relat_1(k1_xboole_0,sK0)),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ? [X0] : k1_xboole_0 != k7_relat_1(k1_xboole_0,X0)),
% 0.21/0.47    inference(ennf_transformation,[],[f18])).
% 0.21/0.47  fof(f18,negated_conjecture,(
% 0.21/0.47    ~! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)),
% 0.21/0.47    inference(negated_conjecture,[],[f17])).
% 0.21/0.47  fof(f17,conjecture,(
% 0.21/0.47    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_relat_1)).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (31647)------------------------------
% 0.21/0.47  % (31647)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (31647)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (31647)Memory used [KB]: 6140
% 0.21/0.47  % (31647)Time elapsed: 0.044 s
% 0.21/0.47  % (31647)------------------------------
% 0.21/0.47  % (31647)------------------------------
% 0.21/0.47  % (31641)Success in time 0.108 s
%------------------------------------------------------------------------------
