%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:11 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 104 expanded)
%              Number of leaves         :   19 (  50 expanded)
%              Depth                    :    7
%              Number of atoms          :  135 ( 218 expanded)
%              Number of equality atoms :   51 (  91 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2005,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f25,f29,f33,f37,f41,f52,f56,f101,f181,f185,f1957,f1993])).

fof(f1993,plain,
    ( spl2_1
    | ~ spl2_11
    | ~ spl2_16
    | ~ spl2_51 ),
    inference(avatar_contradiction_clause,[],[f1992])).

fof(f1992,plain,
    ( $false
    | spl2_1
    | ~ spl2_11
    | ~ spl2_16
    | ~ spl2_51 ),
    inference(subsumption_resolution,[],[f24,f1991])).

fof(f1991,plain,
    ( ! [X8,X9] : k4_xboole_0(X8,X9) = k5_xboole_0(X8,k3_xboole_0(X8,X9))
    | ~ spl2_11
    | ~ spl2_16
    | ~ spl2_51 ),
    inference(forward_demodulation,[],[f1967,f184])).

fof(f184,plain,
    ( ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f183])).

fof(f183,plain,
    ( spl2_16
  <=> ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f1967,plain,
    ( ! [X8,X9] : k5_xboole_0(k1_xboole_0,k4_xboole_0(X8,X9)) = k5_xboole_0(X8,k3_xboole_0(X8,X9))
    | ~ spl2_11
    | ~ spl2_51 ),
    inference(superposition,[],[f100,f1956])).

fof(f1956,plain,
    ( ! [X4,X3] : k3_xboole_0(X3,X4) = k5_xboole_0(X3,k4_xboole_0(X3,X4))
    | ~ spl2_51 ),
    inference(avatar_component_clause,[],[f1955])).

fof(f1955,plain,
    ( spl2_51
  <=> ! [X3,X4] : k3_xboole_0(X3,X4) = k5_xboole_0(X3,k4_xboole_0(X3,X4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_51])])).

fof(f100,plain,
    ( ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1)
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl2_11
  <=> ! [X1,X0] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f24,plain,
    ( k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f22])).

fof(f22,plain,
    ( spl2_1
  <=> k4_xboole_0(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f1957,plain,
    ( spl2_51
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_8
    | ~ spl2_11
    | ~ spl2_15 ),
    inference(avatar_split_clause,[],[f211,f179,f99,f54,f39,f31,f27,f1955])).

fof(f27,plain,
    ( spl2_2
  <=> ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f31,plain,
    ( spl2_3
  <=> ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f39,plain,
    ( spl2_5
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f54,plain,
    ( spl2_8
  <=> ! [X1,X0,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f179,plain,
    ( spl2_15
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f211,plain,
    ( ! [X4,X3] : k3_xboole_0(X3,X4) = k5_xboole_0(X3,k4_xboole_0(X3,X4))
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_8
    | ~ spl2_11
    | ~ spl2_15 ),
    inference(forward_demodulation,[],[f198,f116])).

fof(f116,plain,
    ( ! [X2,X3] : k4_xboole_0(X3,X2) = k5_xboole_0(X2,k2_xboole_0(X2,X3))
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_11 ),
    inference(forward_demodulation,[],[f104,f114])).

fof(f114,plain,
    ( ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_11 ),
    inference(forward_demodulation,[],[f102,f32])).

fof(f32,plain,
    ( ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f31])).

fof(f102,plain,
    ( ! [X0] : k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,X0)
    | ~ spl2_2
    | ~ spl2_11 ),
    inference(superposition,[],[f100,f28])).

fof(f28,plain,
    ( ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f27])).

fof(f104,plain,
    ( ! [X2,X3] : k5_xboole_0(k1_xboole_0,k4_xboole_0(X3,X2)) = k5_xboole_0(X2,k2_xboole_0(X2,X3))
    | ~ spl2_5
    | ~ spl2_11 ),
    inference(superposition,[],[f100,f40])).

fof(f40,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f39])).

fof(f198,plain,
    ( ! [X4,X3] : k5_xboole_0(X3,k5_xboole_0(X4,k2_xboole_0(X4,X3))) = k3_xboole_0(X3,X4)
    | ~ spl2_8
    | ~ spl2_15 ),
    inference(superposition,[],[f180,f55])).

fof(f55,plain,
    ( ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f54])).

fof(f180,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X1,X0))
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f179])).

fof(f185,plain,
    ( spl2_16
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f114,f99,f31,f27,f183])).

fof(f181,plain,
    ( spl2_15
    | ~ spl2_4
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f61,f50,f35,f179])).

fof(f35,plain,
    ( spl2_4
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f50,plain,
    ( spl2_7
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f61,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X1,X0))
    | ~ spl2_4
    | ~ spl2_7 ),
    inference(superposition,[],[f51,f36])).

fof(f36,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f35])).

fof(f51,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f50])).

fof(f101,plain,
    ( spl2_11
    | ~ spl2_2
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f64,f54,f27,f99])).

fof(f64,plain,
    ( ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1)
    | ~ spl2_2
    | ~ spl2_8 ),
    inference(superposition,[],[f55,f28])).

fof(f56,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f20,f54])).

fof(f20,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f52,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f19,f50])).

fof(f19,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f41,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f17,f39])).

fof(f17,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f37,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f16,f35])).

fof(f16,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f33,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f15,f31])).

fof(f15,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f29,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f14,f27])).

fof(f14,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f25,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f13,f22])).

fof(f13,plain,(
    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f11])).

fof(f11,plain,
    ( ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1))
   => k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:54:31 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.41  % (32755)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.47  % (32745)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.47  % (32754)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.47  % (32754)Refutation not found, incomplete strategy% (32754)------------------------------
% 0.22/0.47  % (32754)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (32754)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.47  
% 0.22/0.47  % (32754)Memory used [KB]: 10490
% 0.22/0.47  % (32754)Time elapsed: 0.061 s
% 0.22/0.47  % (32754)------------------------------
% 0.22/0.47  % (32754)------------------------------
% 0.22/0.47  % (32747)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.48  % (32749)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.48  % (32756)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.48  % (32742)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.49  % (32743)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.49  % (32757)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.49  % (32753)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.49  % (32748)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.49  % (32750)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.50  % (32760)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.50  % (32746)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.50  % (32744)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.51  % (32758)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.51  % (32759)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.51  % (32747)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f2005,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(avatar_sat_refutation,[],[f25,f29,f33,f37,f41,f52,f56,f101,f181,f185,f1957,f1993])).
% 0.22/0.51  fof(f1993,plain,(
% 0.22/0.51    spl2_1 | ~spl2_11 | ~spl2_16 | ~spl2_51),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f1992])).
% 0.22/0.51  fof(f1992,plain,(
% 0.22/0.51    $false | (spl2_1 | ~spl2_11 | ~spl2_16 | ~spl2_51)),
% 0.22/0.51    inference(subsumption_resolution,[],[f24,f1991])).
% 0.22/0.51  fof(f1991,plain,(
% 0.22/0.51    ( ! [X8,X9] : (k4_xboole_0(X8,X9) = k5_xboole_0(X8,k3_xboole_0(X8,X9))) ) | (~spl2_11 | ~spl2_16 | ~spl2_51)),
% 0.22/0.51    inference(forward_demodulation,[],[f1967,f184])).
% 0.22/0.51  fof(f184,plain,(
% 0.22/0.51    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) ) | ~spl2_16),
% 0.22/0.51    inference(avatar_component_clause,[],[f183])).
% 0.22/0.51  fof(f183,plain,(
% 0.22/0.51    spl2_16 <=> ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.22/0.51  fof(f1967,plain,(
% 0.22/0.51    ( ! [X8,X9] : (k5_xboole_0(k1_xboole_0,k4_xboole_0(X8,X9)) = k5_xboole_0(X8,k3_xboole_0(X8,X9))) ) | (~spl2_11 | ~spl2_51)),
% 0.22/0.51    inference(superposition,[],[f100,f1956])).
% 0.22/0.51  fof(f1956,plain,(
% 0.22/0.51    ( ! [X4,X3] : (k3_xboole_0(X3,X4) = k5_xboole_0(X3,k4_xboole_0(X3,X4))) ) | ~spl2_51),
% 0.22/0.51    inference(avatar_component_clause,[],[f1955])).
% 0.22/0.51  fof(f1955,plain,(
% 0.22/0.51    spl2_51 <=> ! [X3,X4] : k3_xboole_0(X3,X4) = k5_xboole_0(X3,k4_xboole_0(X3,X4))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_51])])).
% 0.22/0.51  fof(f100,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1)) ) | ~spl2_11),
% 0.22/0.51    inference(avatar_component_clause,[],[f99])).
% 0.22/0.51  fof(f99,plain,(
% 0.22/0.51    spl2_11 <=> ! [X1,X0] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.22/0.51  fof(f24,plain,(
% 0.22/0.51    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) | spl2_1),
% 0.22/0.51    inference(avatar_component_clause,[],[f22])).
% 0.22/0.51  fof(f22,plain,(
% 0.22/0.51    spl2_1 <=> k4_xboole_0(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.51  fof(f1957,plain,(
% 0.22/0.51    spl2_51 | ~spl2_2 | ~spl2_3 | ~spl2_5 | ~spl2_8 | ~spl2_11 | ~spl2_15),
% 0.22/0.51    inference(avatar_split_clause,[],[f211,f179,f99,f54,f39,f31,f27,f1955])).
% 0.22/0.51  fof(f27,plain,(
% 0.22/0.51    spl2_2 <=> ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.51  fof(f31,plain,(
% 0.22/0.51    spl2_3 <=> ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.22/0.51  fof(f39,plain,(
% 0.22/0.51    spl2_5 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.22/0.51  fof(f54,plain,(
% 0.22/0.51    spl2_8 <=> ! [X1,X0,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.22/0.51  fof(f179,plain,(
% 0.22/0.51    spl2_15 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X1,X0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.22/0.51  fof(f211,plain,(
% 0.22/0.51    ( ! [X4,X3] : (k3_xboole_0(X3,X4) = k5_xboole_0(X3,k4_xboole_0(X3,X4))) ) | (~spl2_2 | ~spl2_3 | ~spl2_5 | ~spl2_8 | ~spl2_11 | ~spl2_15)),
% 0.22/0.51    inference(forward_demodulation,[],[f198,f116])).
% 0.22/0.51  fof(f116,plain,(
% 0.22/0.51    ( ! [X2,X3] : (k4_xboole_0(X3,X2) = k5_xboole_0(X2,k2_xboole_0(X2,X3))) ) | (~spl2_2 | ~spl2_3 | ~spl2_5 | ~spl2_11)),
% 0.22/0.51    inference(forward_demodulation,[],[f104,f114])).
% 0.22/0.51  fof(f114,plain,(
% 0.22/0.51    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) ) | (~spl2_2 | ~spl2_3 | ~spl2_11)),
% 0.22/0.51    inference(forward_demodulation,[],[f102,f32])).
% 0.22/0.51  fof(f32,plain,(
% 0.22/0.51    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl2_3),
% 0.22/0.51    inference(avatar_component_clause,[],[f31])).
% 0.22/0.51  fof(f102,plain,(
% 0.22/0.51    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,X0)) ) | (~spl2_2 | ~spl2_11)),
% 0.22/0.51    inference(superposition,[],[f100,f28])).
% 0.22/0.51  fof(f28,plain,(
% 0.22/0.51    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) ) | ~spl2_2),
% 0.22/0.51    inference(avatar_component_clause,[],[f27])).
% 0.22/0.51  fof(f104,plain,(
% 0.22/0.51    ( ! [X2,X3] : (k5_xboole_0(k1_xboole_0,k4_xboole_0(X3,X2)) = k5_xboole_0(X2,k2_xboole_0(X2,X3))) ) | (~spl2_5 | ~spl2_11)),
% 0.22/0.51    inference(superposition,[],[f100,f40])).
% 0.22/0.51  fof(f40,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) ) | ~spl2_5),
% 0.22/0.51    inference(avatar_component_clause,[],[f39])).
% 0.22/0.51  fof(f198,plain,(
% 0.22/0.51    ( ! [X4,X3] : (k5_xboole_0(X3,k5_xboole_0(X4,k2_xboole_0(X4,X3))) = k3_xboole_0(X3,X4)) ) | (~spl2_8 | ~spl2_15)),
% 0.22/0.51    inference(superposition,[],[f180,f55])).
% 0.22/0.51  fof(f55,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) ) | ~spl2_8),
% 0.22/0.51    inference(avatar_component_clause,[],[f54])).
% 0.22/0.51  fof(f180,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X1,X0))) ) | ~spl2_15),
% 0.22/0.51    inference(avatar_component_clause,[],[f179])).
% 0.22/0.51  fof(f185,plain,(
% 0.22/0.51    spl2_16 | ~spl2_2 | ~spl2_3 | ~spl2_11),
% 0.22/0.51    inference(avatar_split_clause,[],[f114,f99,f31,f27,f183])).
% 0.22/0.51  fof(f181,plain,(
% 0.22/0.51    spl2_15 | ~spl2_4 | ~spl2_7),
% 0.22/0.51    inference(avatar_split_clause,[],[f61,f50,f35,f179])).
% 0.22/0.51  fof(f35,plain,(
% 0.22/0.51    spl2_4 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.22/0.51  fof(f50,plain,(
% 0.22/0.51    spl2_7 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.22/0.51  fof(f61,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X1,X0))) ) | (~spl2_4 | ~spl2_7)),
% 0.22/0.51    inference(superposition,[],[f51,f36])).
% 0.22/0.51  fof(f36,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) ) | ~spl2_4),
% 0.22/0.51    inference(avatar_component_clause,[],[f35])).
% 0.22/0.51  fof(f51,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) ) | ~spl2_7),
% 0.22/0.51    inference(avatar_component_clause,[],[f50])).
% 0.22/0.51  fof(f101,plain,(
% 0.22/0.51    spl2_11 | ~spl2_2 | ~spl2_8),
% 0.22/0.51    inference(avatar_split_clause,[],[f64,f54,f27,f99])).
% 0.22/0.51  fof(f64,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1)) ) | (~spl2_2 | ~spl2_8)),
% 0.22/0.51    inference(superposition,[],[f55,f28])).
% 0.22/0.51  fof(f56,plain,(
% 0.22/0.51    spl2_8),
% 0.22/0.51    inference(avatar_split_clause,[],[f20,f54])).
% 0.22/0.51  fof(f20,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f4])).
% 0.22/0.51  fof(f4,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 0.22/0.51  fof(f52,plain,(
% 0.22/0.51    spl2_7),
% 0.22/0.51    inference(avatar_split_clause,[],[f19,f50])).
% 0.22/0.51  fof(f19,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f6])).
% 0.22/0.51  fof(f6,axiom,(
% 0.22/0.51    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).
% 0.22/0.51  fof(f41,plain,(
% 0.22/0.51    spl2_5),
% 0.22/0.51    inference(avatar_split_clause,[],[f17,f39])).
% 0.22/0.51  fof(f17,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f7])).
% 0.22/0.51  fof(f7,axiom,(
% 0.22/0.51    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.22/0.51  fof(f37,plain,(
% 0.22/0.51    spl2_4),
% 0.22/0.51    inference(avatar_split_clause,[],[f16,f35])).
% 0.22/0.51  fof(f16,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.22/0.51  fof(f33,plain,(
% 0.22/0.51    spl2_3),
% 0.22/0.51    inference(avatar_split_clause,[],[f15,f31])).
% 0.22/0.51  fof(f15,plain,(
% 0.22/0.51    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.51    inference(cnf_transformation,[],[f3])).
% 0.22/0.51  fof(f3,axiom,(
% 0.22/0.51    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 0.22/0.51  fof(f29,plain,(
% 0.22/0.51    spl2_2),
% 0.22/0.51    inference(avatar_split_clause,[],[f14,f27])).
% 0.22/0.51  fof(f14,plain,(
% 0.22/0.51    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f5])).
% 0.22/0.51  fof(f5,axiom,(
% 0.22/0.51    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 0.22/0.51  fof(f25,plain,(
% 0.22/0.51    ~spl2_1),
% 0.22/0.51    inference(avatar_split_clause,[],[f13,f22])).
% 0.22/0.51  fof(f13,plain,(
% 0.22/0.51    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 0.22/0.51    inference(cnf_transformation,[],[f12])).
% 0.22/0.51  fof(f12,plain,(
% 0.22/0.51    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f11])).
% 0.22/0.51  fof(f11,plain,(
% 0.22/0.51    ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1)) => k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f10,plain,(
% 0.22/0.51    ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.51    inference(ennf_transformation,[],[f9])).
% 0.22/0.51  fof(f9,negated_conjecture,(
% 0.22/0.51    ~! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.51    inference(negated_conjecture,[],[f8])).
% 0.22/0.51  fof(f8,conjecture,(
% 0.22/0.51    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (32747)------------------------------
% 0.22/0.51  % (32747)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (32747)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (32747)Memory used [KB]: 8059
% 0.22/0.51  % (32747)Time elapsed: 0.102 s
% 0.22/0.51  % (32747)------------------------------
% 0.22/0.51  % (32747)------------------------------
% 0.22/0.51  % (32751)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.52  % (32741)Success in time 0.157 s
%------------------------------------------------------------------------------
