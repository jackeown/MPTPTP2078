%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:30 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   40 (  46 expanded)
%              Number of leaves         :   12 (  18 expanded)
%              Depth                    :    9
%              Number of atoms          :   68 (  80 expanded)
%              Number of equality atoms :   29 (  35 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f52,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f23,f28,f33,f39,f44,f51])).

fof(f51,plain,
    ( ~ spl1_3
    | ~ spl1_4
    | spl1_5 ),
    inference(avatar_contradiction_clause,[],[f50])).

fof(f50,plain,
    ( $false
    | ~ spl1_3
    | ~ spl1_4
    | spl1_5 ),
    inference(trivial_inequality_removal,[],[f49])).

fof(f49,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl1_3
    | ~ spl1_4
    | spl1_5 ),
    inference(superposition,[],[f43,f48])).

fof(f48,plain,
    ( ! [X2] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X2)
    | ~ spl1_3
    | ~ spl1_4 ),
    inference(forward_demodulation,[],[f47,f32])).

fof(f32,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f30])).

fof(f30,plain,
    ( spl1_3
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f47,plain,
    ( ! [X2] : k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,X2)
    | ~ spl1_4 ),
    inference(forward_demodulation,[],[f46,f17])).

fof(f17,plain,(
    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_relat_1)).

fof(f46,plain,
    ( ! [X2] : k2_relat_1(k7_relat_1(k1_xboole_0,X2)) = k9_relat_1(k1_xboole_0,X2)
    | ~ spl1_4 ),
    inference(resolution,[],[f18,f38])).

fof(f38,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl1_4 ),
    inference(avatar_component_clause,[],[f36])).

fof(f36,plain,
    ( spl1_4
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f43,plain,
    ( k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0)
    | spl1_5 ),
    inference(avatar_component_clause,[],[f41])).

fof(f41,plain,
    ( spl1_5
  <=> k1_xboole_0 = k9_relat_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f44,plain,(
    ~ spl1_5 ),
    inference(avatar_split_clause,[],[f12,f41])).

fof(f12,plain,(
    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f8,f10])).

fof(f10,plain,
    ( ? [X0] : k1_xboole_0 != k9_relat_1(k1_xboole_0,X0)
   => k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] : k1_xboole_0 != k9_relat_1(k1_xboole_0,X0) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).

fof(f39,plain,
    ( spl1_4
    | ~ spl1_1 ),
    inference(avatar_split_clause,[],[f34,f20,f36])).

fof(f20,plain,
    ( spl1_1
  <=> k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f34,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl1_1 ),
    inference(superposition,[],[f16,f22])).

fof(f22,plain,
    ( k1_xboole_0 = k6_relat_1(k1_xboole_0)
    | ~ spl1_1 ),
    inference(avatar_component_clause,[],[f20])).

fof(f16,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f33,plain,(
    spl1_3 ),
    inference(avatar_split_clause,[],[f15,f30])).

fof(f15,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f28,plain,(
    spl1_2 ),
    inference(avatar_split_clause,[],[f14,f25])).

fof(f25,plain,
    ( spl1_2
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f14,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f23,plain,(
    spl1_1 ),
    inference(avatar_split_clause,[],[f13,f20])).

fof(f13,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:21:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.38  % (20637)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.19/0.41  % (20634)lrs+1004_5:4_aac=none:add=large:afp=100000:afq=1.4:anc=all_dependent:bd=off:cond=fast:gsp=input_only:gs=on:gsem=off:lma=on:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sp=occurrence:updr=off:uhcvi=on_99 on theBenchmark
% 0.19/0.42  % (20637)Refutation found. Thanks to Tanya!
% 0.19/0.42  % SZS status Theorem for theBenchmark
% 0.19/0.42  % SZS output start Proof for theBenchmark
% 0.19/0.42  fof(f52,plain,(
% 0.19/0.42    $false),
% 0.19/0.42    inference(avatar_sat_refutation,[],[f23,f28,f33,f39,f44,f51])).
% 0.19/0.42  fof(f51,plain,(
% 0.19/0.42    ~spl1_3 | ~spl1_4 | spl1_5),
% 0.19/0.42    inference(avatar_contradiction_clause,[],[f50])).
% 0.19/0.42  fof(f50,plain,(
% 0.19/0.42    $false | (~spl1_3 | ~spl1_4 | spl1_5)),
% 0.19/0.42    inference(trivial_inequality_removal,[],[f49])).
% 0.19/0.42  fof(f49,plain,(
% 0.19/0.42    k1_xboole_0 != k1_xboole_0 | (~spl1_3 | ~spl1_4 | spl1_5)),
% 0.19/0.42    inference(superposition,[],[f43,f48])).
% 0.19/0.42  fof(f48,plain,(
% 0.19/0.42    ( ! [X2] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X2)) ) | (~spl1_3 | ~spl1_4)),
% 0.19/0.42    inference(forward_demodulation,[],[f47,f32])).
% 0.19/0.42  fof(f32,plain,(
% 0.19/0.42    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl1_3),
% 0.19/0.42    inference(avatar_component_clause,[],[f30])).
% 0.19/0.42  fof(f30,plain,(
% 0.19/0.42    spl1_3 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.19/0.42  fof(f47,plain,(
% 0.19/0.42    ( ! [X2] : (k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,X2)) ) | ~spl1_4),
% 0.19/0.42    inference(forward_demodulation,[],[f46,f17])).
% 0.19/0.42  fof(f17,plain,(
% 0.19/0.42    ( ! [X0] : (k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f2])).
% 0.19/0.42  fof(f2,axiom,(
% 0.19/0.42    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)),
% 0.19/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_relat_1)).
% 0.19/0.42  fof(f46,plain,(
% 0.19/0.42    ( ! [X2] : (k2_relat_1(k7_relat_1(k1_xboole_0,X2)) = k9_relat_1(k1_xboole_0,X2)) ) | ~spl1_4),
% 0.19/0.42    inference(resolution,[],[f18,f38])).
% 0.19/0.42  fof(f38,plain,(
% 0.19/0.42    v1_relat_1(k1_xboole_0) | ~spl1_4),
% 0.19/0.42    inference(avatar_component_clause,[],[f36])).
% 0.19/0.42  fof(f36,plain,(
% 0.19/0.42    spl1_4 <=> v1_relat_1(k1_xboole_0)),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.19/0.42  fof(f18,plain,(
% 0.19/0.42    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f9])).
% 0.19/0.42  fof(f9,plain,(
% 0.19/0.42    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.19/0.42    inference(ennf_transformation,[],[f3])).
% 0.19/0.42  fof(f3,axiom,(
% 0.19/0.42    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.19/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 0.19/0.42  fof(f43,plain,(
% 0.19/0.42    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0) | spl1_5),
% 0.19/0.42    inference(avatar_component_clause,[],[f41])).
% 0.19/0.42  fof(f41,plain,(
% 0.19/0.42    spl1_5 <=> k1_xboole_0 = k9_relat_1(k1_xboole_0,sK0)),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.19/0.42  fof(f44,plain,(
% 0.19/0.42    ~spl1_5),
% 0.19/0.42    inference(avatar_split_clause,[],[f12,f41])).
% 0.19/0.42  fof(f12,plain,(
% 0.19/0.42    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0)),
% 0.19/0.42    inference(cnf_transformation,[],[f11])).
% 0.19/0.42  fof(f11,plain,(
% 0.19/0.42    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0)),
% 0.19/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f8,f10])).
% 0.19/0.42  fof(f10,plain,(
% 0.19/0.42    ? [X0] : k1_xboole_0 != k9_relat_1(k1_xboole_0,X0) => k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0)),
% 0.19/0.42    introduced(choice_axiom,[])).
% 0.19/0.42  fof(f8,plain,(
% 0.19/0.42    ? [X0] : k1_xboole_0 != k9_relat_1(k1_xboole_0,X0)),
% 0.19/0.42    inference(ennf_transformation,[],[f7])).
% 0.19/0.42  fof(f7,negated_conjecture,(
% 0.19/0.42    ~! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 0.19/0.42    inference(negated_conjecture,[],[f6])).
% 0.19/0.42  fof(f6,conjecture,(
% 0.19/0.42    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 0.19/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).
% 0.19/0.42  fof(f39,plain,(
% 0.19/0.42    spl1_4 | ~spl1_1),
% 0.19/0.42    inference(avatar_split_clause,[],[f34,f20,f36])).
% 0.19/0.42  fof(f20,plain,(
% 0.19/0.42    spl1_1 <=> k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.19/0.42  fof(f34,plain,(
% 0.19/0.42    v1_relat_1(k1_xboole_0) | ~spl1_1),
% 0.19/0.42    inference(superposition,[],[f16,f22])).
% 0.19/0.42  fof(f22,plain,(
% 0.19/0.42    k1_xboole_0 = k6_relat_1(k1_xboole_0) | ~spl1_1),
% 0.19/0.42    inference(avatar_component_clause,[],[f20])).
% 0.19/0.42  fof(f16,plain,(
% 0.19/0.42    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.19/0.42    inference(cnf_transformation,[],[f1])).
% 0.19/0.42  fof(f1,axiom,(
% 0.19/0.42    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.19/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.19/0.42  fof(f33,plain,(
% 0.19/0.42    spl1_3),
% 0.19/0.42    inference(avatar_split_clause,[],[f15,f30])).
% 0.19/0.42  fof(f15,plain,(
% 0.19/0.42    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.19/0.42    inference(cnf_transformation,[],[f4])).
% 0.19/0.42  fof(f4,axiom,(
% 0.19/0.42    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.19/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.19/0.42  fof(f28,plain,(
% 0.19/0.42    spl1_2),
% 0.19/0.42    inference(avatar_split_clause,[],[f14,f25])).
% 0.19/0.42  fof(f25,plain,(
% 0.19/0.42    spl1_2 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.19/0.42  fof(f14,plain,(
% 0.19/0.42    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.19/0.42    inference(cnf_transformation,[],[f4])).
% 0.19/0.42  fof(f23,plain,(
% 0.19/0.42    spl1_1),
% 0.19/0.42    inference(avatar_split_clause,[],[f13,f20])).
% 0.19/0.42  fof(f13,plain,(
% 0.19/0.42    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.19/0.42    inference(cnf_transformation,[],[f5])).
% 0.19/0.42  fof(f5,axiom,(
% 0.19/0.42    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.19/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).
% 0.19/0.42  % SZS output end Proof for theBenchmark
% 0.19/0.42  % (20637)------------------------------
% 0.19/0.42  % (20637)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.42  % (20637)Termination reason: Refutation
% 0.19/0.42  
% 0.19/0.42  % (20637)Memory used [KB]: 6012
% 0.19/0.42  % (20637)Time elapsed: 0.038 s
% 0.19/0.42  % (20637)------------------------------
% 0.19/0.42  % (20637)------------------------------
% 0.19/0.42  % (20630)Success in time 0.073 s
%------------------------------------------------------------------------------
