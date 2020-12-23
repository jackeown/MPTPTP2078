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
% DateTime   : Thu Dec  3 12:49:23 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   49 (  58 expanded)
%              Number of leaves         :   15 (  24 expanded)
%              Depth                    :    7
%              Number of atoms          :   99 ( 120 expanded)
%              Number of equality atoms :   28 (  32 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f71,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f27,f32,f42,f50,f54,f60,f67,f70])).

fof(f70,plain,
    ( spl1_1
    | ~ spl1_4
    | ~ spl1_7
    | ~ spl1_8
    | ~ spl1_9 ),
    inference(avatar_contradiction_clause,[],[f69])).

fof(f69,plain,
    ( $false
    | spl1_1
    | ~ spl1_4
    | ~ spl1_7
    | ~ spl1_8
    | ~ spl1_9 ),
    inference(subsumption_resolution,[],[f26,f68])).

fof(f68,plain,
    ( ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)
    | ~ spl1_4
    | ~ spl1_7
    | ~ spl1_8
    | ~ spl1_9 ),
    inference(subsumption_resolution,[],[f62,f66])).

fof(f66,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl1_9 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl1_9
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).

fof(f62,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl1_4
    | ~ spl1_7
    | ~ spl1_8 ),
    inference(forward_demodulation,[],[f61,f41])).

fof(f41,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl1_4 ),
    inference(avatar_component_clause,[],[f39])).

fof(f39,plain,
    ( spl1_4
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f61,plain,
    ( ! [X0] :
        ( k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,X0)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl1_7
    | ~ spl1_8 ),
    inference(superposition,[],[f59,f53])).

fof(f53,plain,
    ( ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)
    | ~ spl1_7 ),
    inference(avatar_component_clause,[],[f52])).

fof(f52,plain,
    ( spl1_7
  <=> ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).

fof(f59,plain,
    ( ! [X0,X1] :
        ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
        | ~ v1_relat_1(X1) )
    | ~ spl1_8 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl1_8
  <=> ! [X1,X0] :
        ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).

fof(f26,plain,
    ( k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0)
    | spl1_1 ),
    inference(avatar_component_clause,[],[f24])).

fof(f24,plain,
    ( spl1_1
  <=> k1_xboole_0 = k9_relat_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f67,plain,
    ( spl1_9
    | ~ spl1_2
    | ~ spl1_6 ),
    inference(avatar_split_clause,[],[f55,f48,f29,f64])).

fof(f29,plain,
    ( spl1_2
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f48,plain,
    ( spl1_6
  <=> ! [X0] :
        ( v1_relat_1(X0)
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f55,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl1_2
    | ~ spl1_6 ),
    inference(unit_resulting_resolution,[],[f31,f49])).

fof(f49,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | v1_relat_1(X0) )
    | ~ spl1_6 ),
    inference(avatar_component_clause,[],[f48])).

fof(f31,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl1_2 ),
    inference(avatar_component_clause,[],[f29])).

fof(f60,plain,(
    spl1_8 ),
    inference(avatar_split_clause,[],[f21,f58])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f54,plain,(
    spl1_7 ),
    inference(avatar_split_clause,[],[f19,f52])).

fof(f19,plain,(
    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_relat_1)).

fof(f50,plain,(
    spl1_6 ),
    inference(avatar_split_clause,[],[f20,f48])).

fof(f20,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f42,plain,(
    spl1_4 ),
    inference(avatar_split_clause,[],[f16,f39])).

fof(f16,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f32,plain,(
    spl1_2 ),
    inference(avatar_split_clause,[],[f22,f29])).

fof(f22,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(forward_demodulation,[],[f17,f18])).

fof(f18,plain,(
    ! [X0] : k1_subset_1(X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k1_subset_1(X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

fof(f17,plain,(
    ! [X0] : v1_xboole_0(k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : v1_xboole_0(k1_subset_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc13_subset_1)).

fof(f27,plain,(
    ~ spl1_1 ),
    inference(avatar_split_clause,[],[f14,f24])).

fof(f14,plain,(
    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f12])).

fof(f12,plain,
    ( ? [X0] : k1_xboole_0 != k9_relat_1(k1_xboole_0,X0)
   => k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] : k1_xboole_0 != k9_relat_1(k1_xboole_0,X0) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:56:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.43  % (21432)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.43  % (21432)Refutation found. Thanks to Tanya!
% 0.22/0.43  % SZS status Theorem for theBenchmark
% 0.22/0.43  % SZS output start Proof for theBenchmark
% 0.22/0.43  fof(f71,plain,(
% 0.22/0.43    $false),
% 0.22/0.43    inference(avatar_sat_refutation,[],[f27,f32,f42,f50,f54,f60,f67,f70])).
% 0.22/0.43  fof(f70,plain,(
% 0.22/0.43    spl1_1 | ~spl1_4 | ~spl1_7 | ~spl1_8 | ~spl1_9),
% 0.22/0.43    inference(avatar_contradiction_clause,[],[f69])).
% 0.22/0.43  fof(f69,plain,(
% 0.22/0.43    $false | (spl1_1 | ~spl1_4 | ~spl1_7 | ~spl1_8 | ~spl1_9)),
% 0.22/0.43    inference(subsumption_resolution,[],[f26,f68])).
% 0.22/0.43  fof(f68,plain,(
% 0.22/0.43    ( ! [X0] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)) ) | (~spl1_4 | ~spl1_7 | ~spl1_8 | ~spl1_9)),
% 0.22/0.43    inference(subsumption_resolution,[],[f62,f66])).
% 0.22/0.43  fof(f66,plain,(
% 0.22/0.43    v1_relat_1(k1_xboole_0) | ~spl1_9),
% 0.22/0.43    inference(avatar_component_clause,[],[f64])).
% 0.22/0.43  fof(f64,plain,(
% 0.22/0.43    spl1_9 <=> v1_relat_1(k1_xboole_0)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).
% 0.22/0.43  fof(f62,plain,(
% 0.22/0.43    ( ! [X0] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) | ~v1_relat_1(k1_xboole_0)) ) | (~spl1_4 | ~spl1_7 | ~spl1_8)),
% 0.22/0.43    inference(forward_demodulation,[],[f61,f41])).
% 0.22/0.43  fof(f41,plain,(
% 0.22/0.43    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl1_4),
% 0.22/0.43    inference(avatar_component_clause,[],[f39])).
% 0.22/0.43  fof(f39,plain,(
% 0.22/0.43    spl1_4 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.22/0.43  fof(f61,plain,(
% 0.22/0.43    ( ! [X0] : (k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,X0) | ~v1_relat_1(k1_xboole_0)) ) | (~spl1_7 | ~spl1_8)),
% 0.22/0.43    inference(superposition,[],[f59,f53])).
% 0.22/0.43  fof(f53,plain,(
% 0.22/0.43    ( ! [X0] : (k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)) ) | ~spl1_7),
% 0.22/0.43    inference(avatar_component_clause,[],[f52])).
% 0.22/0.43  fof(f52,plain,(
% 0.22/0.43    spl1_7 <=> ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).
% 0.22/0.43  fof(f59,plain,(
% 0.22/0.43    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) ) | ~spl1_8),
% 0.22/0.43    inference(avatar_component_clause,[],[f58])).
% 0.22/0.43  fof(f58,plain,(
% 0.22/0.43    spl1_8 <=> ! [X1,X0] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).
% 0.22/0.43  fof(f26,plain,(
% 0.22/0.43    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0) | spl1_1),
% 0.22/0.43    inference(avatar_component_clause,[],[f24])).
% 0.22/0.43  fof(f24,plain,(
% 0.22/0.43    spl1_1 <=> k1_xboole_0 = k9_relat_1(k1_xboole_0,sK0)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.22/0.43  fof(f67,plain,(
% 0.22/0.43    spl1_9 | ~spl1_2 | ~spl1_6),
% 0.22/0.43    inference(avatar_split_clause,[],[f55,f48,f29,f64])).
% 0.22/0.43  fof(f29,plain,(
% 0.22/0.43    spl1_2 <=> v1_xboole_0(k1_xboole_0)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.22/0.43  fof(f48,plain,(
% 0.22/0.43    spl1_6 <=> ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 0.22/0.43  fof(f55,plain,(
% 0.22/0.43    v1_relat_1(k1_xboole_0) | (~spl1_2 | ~spl1_6)),
% 0.22/0.43    inference(unit_resulting_resolution,[],[f31,f49])).
% 0.22/0.43  fof(f49,plain,(
% 0.22/0.43    ( ! [X0] : (~v1_xboole_0(X0) | v1_relat_1(X0)) ) | ~spl1_6),
% 0.22/0.43    inference(avatar_component_clause,[],[f48])).
% 0.22/0.43  fof(f31,plain,(
% 0.22/0.43    v1_xboole_0(k1_xboole_0) | ~spl1_2),
% 0.22/0.43    inference(avatar_component_clause,[],[f29])).
% 0.22/0.43  fof(f60,plain,(
% 0.22/0.43    spl1_8),
% 0.22/0.43    inference(avatar_split_clause,[],[f21,f58])).
% 0.22/0.43  fof(f21,plain,(
% 0.22/0.43    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f11])).
% 0.22/0.43  fof(f11,plain,(
% 0.22/0.43    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.43    inference(ennf_transformation,[],[f5])).
% 0.22/0.43  fof(f5,axiom,(
% 0.22/0.43    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 0.22/0.43  fof(f54,plain,(
% 0.22/0.43    spl1_7),
% 0.22/0.43    inference(avatar_split_clause,[],[f19,f52])).
% 0.22/0.43  fof(f19,plain,(
% 0.22/0.43    ( ! [X0] : (k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f4])).
% 0.22/0.43  fof(f4,axiom,(
% 0.22/0.43    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_relat_1)).
% 0.22/0.43  fof(f50,plain,(
% 0.22/0.43    spl1_6),
% 0.22/0.43    inference(avatar_split_clause,[],[f20,f48])).
% 0.22/0.43  fof(f20,plain,(
% 0.22/0.43    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f10])).
% 0.22/0.43  fof(f10,plain,(
% 0.22/0.43    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 0.22/0.43    inference(ennf_transformation,[],[f3])).
% 0.22/0.43  fof(f3,axiom,(
% 0.22/0.43    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).
% 0.22/0.43  fof(f42,plain,(
% 0.22/0.43    spl1_4),
% 0.22/0.43    inference(avatar_split_clause,[],[f16,f39])).
% 0.22/0.43  fof(f16,plain,(
% 0.22/0.43    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.22/0.43    inference(cnf_transformation,[],[f6])).
% 0.22/0.43  fof(f6,axiom,(
% 0.22/0.43    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.22/0.43  fof(f32,plain,(
% 0.22/0.43    spl1_2),
% 0.22/0.43    inference(avatar_split_clause,[],[f22,f29])).
% 0.22/0.43  fof(f22,plain,(
% 0.22/0.43    v1_xboole_0(k1_xboole_0)),
% 0.22/0.43    inference(forward_demodulation,[],[f17,f18])).
% 0.22/0.43  fof(f18,plain,(
% 0.22/0.43    ( ! [X0] : (k1_subset_1(X0) = k1_xboole_0) )),
% 0.22/0.43    inference(cnf_transformation,[],[f1])).
% 0.22/0.43  fof(f1,axiom,(
% 0.22/0.43    ! [X0] : k1_subset_1(X0) = k1_xboole_0),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).
% 0.22/0.43  fof(f17,plain,(
% 0.22/0.43    ( ! [X0] : (v1_xboole_0(k1_subset_1(X0))) )),
% 0.22/0.43    inference(cnf_transformation,[],[f2])).
% 0.22/0.43  fof(f2,axiom,(
% 0.22/0.43    ! [X0] : v1_xboole_0(k1_subset_1(X0))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc13_subset_1)).
% 0.22/0.43  fof(f27,plain,(
% 0.22/0.43    ~spl1_1),
% 0.22/0.43    inference(avatar_split_clause,[],[f14,f24])).
% 0.22/0.43  fof(f14,plain,(
% 0.22/0.43    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0)),
% 0.22/0.43    inference(cnf_transformation,[],[f13])).
% 0.22/0.43  fof(f13,plain,(
% 0.22/0.43    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0)),
% 0.22/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f12])).
% 0.22/0.43  fof(f12,plain,(
% 0.22/0.43    ? [X0] : k1_xboole_0 != k9_relat_1(k1_xboole_0,X0) => k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0)),
% 0.22/0.43    introduced(choice_axiom,[])).
% 0.22/0.43  fof(f9,plain,(
% 0.22/0.43    ? [X0] : k1_xboole_0 != k9_relat_1(k1_xboole_0,X0)),
% 0.22/0.43    inference(ennf_transformation,[],[f8])).
% 0.22/0.43  fof(f8,negated_conjecture,(
% 0.22/0.43    ~! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 0.22/0.43    inference(negated_conjecture,[],[f7])).
% 0.22/0.43  fof(f7,conjecture,(
% 0.22/0.43    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).
% 0.22/0.43  % SZS output end Proof for theBenchmark
% 0.22/0.43  % (21432)------------------------------
% 0.22/0.43  % (21432)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.43  % (21432)Termination reason: Refutation
% 0.22/0.43  
% 0.22/0.43  % (21432)Memory used [KB]: 6140
% 0.22/0.43  % (21432)Time elapsed: 0.005 s
% 0.22/0.43  % (21432)------------------------------
% 0.22/0.43  % (21432)------------------------------
% 0.22/0.43  % (21426)Success in time 0.07 s
%------------------------------------------------------------------------------
