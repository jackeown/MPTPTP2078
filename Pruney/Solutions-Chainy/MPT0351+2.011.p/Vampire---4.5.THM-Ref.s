%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:04 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 241 expanded)
%              Number of leaves         :   35 (  96 expanded)
%              Depth                    :   12
%              Number of atoms          :  218 ( 390 expanded)
%              Number of equality atoms :   83 ( 192 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f261,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f72,f77,f83,f94,f111,f128,f146,f160,f165,f194,f202,f210,f255])).

fof(f255,plain,
    ( spl2_15
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f254,f197,f207])).

fof(f207,plain,
    ( spl2_15
  <=> sK0 = k4_subset_1(sK0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f197,plain,
    ( spl2_14
  <=> k4_subset_1(sK0,sK0,sK1) = k5_xboole_0(k5_xboole_0(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f254,plain,
    ( sK0 = k4_subset_1(sK0,sK0,sK1)
    | ~ spl2_14 ),
    inference(forward_demodulation,[],[f253,f39])).

fof(f39,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f253,plain,
    ( k4_subset_1(sK0,sK0,sK1) = k5_xboole_0(sK0,k1_xboole_0)
    | ~ spl2_14 ),
    inference(forward_demodulation,[],[f247,f37])).

fof(f37,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f247,plain,
    ( k4_subset_1(sK0,sK0,sK1) = k5_xboole_0(sK0,k5_xboole_0(sK1,sK1))
    | ~ spl2_14 ),
    inference(superposition,[],[f53,f199])).

fof(f199,plain,
    ( k4_subset_1(sK0,sK0,sK1) = k5_xboole_0(k5_xboole_0(sK0,sK1),sK1)
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f197])).

fof(f53,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f210,plain,
    ( ~ spl2_15
    | spl2_3
    | ~ spl2_13 ),
    inference(avatar_split_clause,[],[f205,f191,f80,f207])).

fof(f80,plain,
    ( spl2_3
  <=> sK0 = k4_subset_1(sK0,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f191,plain,
    ( spl2_13
  <=> k4_subset_1(sK0,sK1,sK0) = k4_subset_1(sK0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f205,plain,
    ( sK0 != k4_subset_1(sK0,sK0,sK1)
    | spl2_3
    | ~ spl2_13 ),
    inference(superposition,[],[f82,f193])).

fof(f193,plain,
    ( k4_subset_1(sK0,sK1,sK0) = k4_subset_1(sK0,sK0,sK1)
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f191])).

fof(f82,plain,
    ( sK0 != k4_subset_1(sK0,sK1,sK0)
    | spl2_3 ),
    inference(avatar_component_clause,[],[f80])).

fof(f202,plain,
    ( spl2_14
    | ~ spl2_8
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f201,f162,f140,f197])).

fof(f140,plain,
    ( spl2_8
  <=> sK1 = k3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f162,plain,
    ( spl2_10
  <=> k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) = k4_subset_1(sK0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f201,plain,
    ( k4_subset_1(sK0,sK0,sK1) = k5_xboole_0(k5_xboole_0(sK0,sK1),sK1)
    | ~ spl2_8
    | ~ spl2_10 ),
    inference(forward_demodulation,[],[f189,f142])).

fof(f142,plain,
    ( sK1 = k3_xboole_0(sK0,sK1)
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f140])).

% (7810)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% (7820)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% (7822)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% (7824)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% (7817)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% (7808)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% (7815)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% (7807)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
fof(f189,plain,
    ( k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) = k4_subset_1(sK0,sK0,sK1)
    | ~ spl2_10 ),
    inference(superposition,[],[f66,f164])).

fof(f164,plain,
    ( k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) = k4_subset_1(sK0,sK0,sK1)
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f162])).

fof(f66,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f45,f64])).

fof(f64,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f43,f63])).

fof(f63,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f44,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f52,f61])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f55,f60])).

fof(f60,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f56,f59])).

% (7814)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
fof(f59,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f57,f58])).

fof(f58,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f57,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f56,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f55,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f52,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f44,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f43,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f45,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

fof(f194,plain,
    ( spl2_13
    | ~ spl2_9
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f187,f162,f157,f191])).

fof(f157,plain,
    ( spl2_9
  <=> k4_subset_1(sK0,sK1,sK0) = k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f187,plain,
    ( k4_subset_1(sK0,sK1,sK0) = k4_subset_1(sK0,sK0,sK1)
    | ~ spl2_9
    | ~ spl2_10 ),
    inference(backward_demodulation,[],[f159,f164])).

fof(f159,plain,
    ( k4_subset_1(sK0,sK1,sK0) = k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f157])).

fof(f165,plain,
    ( spl2_10
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f150,f74,f162])).

fof(f74,plain,
    ( spl2_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f150,plain,
    ( k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) = k4_subset_1(sK0,sK0,sK1)
    | ~ spl2_2 ),
    inference(unit_resulting_resolution,[],[f84,f76,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) ) ),
    inference(definition_unfolding,[],[f54,f64])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f76,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f74])).

fof(f84,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f40,f36])).

fof(f36,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f40,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f160,plain,
    ( spl2_9
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f155,f74,f157])).

fof(f155,plain,
    ( k4_subset_1(sK0,sK1,sK0) = k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f151,f65])).

fof(f65,plain,(
    ! [X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f42,f63,f63])).

fof(f42,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f151,plain,
    ( k4_subset_1(sK0,sK1,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK0))
    | ~ spl2_2 ),
    inference(unit_resulting_resolution,[],[f76,f84,f67])).

fof(f146,plain,
    ( spl2_8
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f138,f124,f140])).

fof(f124,plain,
    ( spl2_7
  <=> sK1 = k3_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f138,plain,
    ( sK1 = k3_xboole_0(sK0,sK1)
    | ~ spl2_7 ),
    inference(superposition,[],[f41,f126])).

fof(f126,plain,
    ( sK1 = k3_xboole_0(sK1,sK0)
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f124])).

fof(f41,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f128,plain,
    ( spl2_7
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f122,f106,f124])).

fof(f106,plain,
    ( spl2_6
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f122,plain,
    ( sK1 = k3_xboole_0(sK1,sK0)
    | ~ spl2_6 ),
    inference(resolution,[],[f108,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f108,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f106])).

fof(f111,plain,
    ( spl2_6
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f110,f91,f106])).

fof(f91,plain,
    ( spl2_4
  <=> r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f110,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl2_4 ),
    inference(forward_demodulation,[],[f103,f38])).

fof(f38,plain,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).

fof(f103,plain,
    ( r1_tarski(sK1,k3_tarski(k1_zfmisc_1(sK0)))
    | ~ spl2_4 ),
    inference(resolution,[],[f93,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(X0,k3_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

fof(f93,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f91])).

fof(f94,plain,
    ( spl2_4
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f86,f74,f91])).

fof(f86,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | ~ spl2_2 ),
    inference(unit_resulting_resolution,[],[f35,f76,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f35,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f83,plain,
    ( ~ spl2_3
    | spl2_1 ),
    inference(avatar_split_clause,[],[f78,f69,f80])).

fof(f69,plain,
    ( spl2_1
  <=> k2_subset_1(sK0) = k4_subset_1(sK0,sK1,k2_subset_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f78,plain,
    ( sK0 != k4_subset_1(sK0,sK1,sK0)
    | spl2_1 ),
    inference(backward_demodulation,[],[f71,f36])).

fof(f71,plain,
    ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f69])).

fof(f77,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f33,f74])).

fof(f33,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f30])).

fof(f30,plain,
    ( ? [X0,X1] :
        ( k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0))
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0,X1] :
      ( k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0))
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_subset_1)).

fof(f72,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f34,f69])).

fof(f34,plain,(
    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0)) ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:24:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.44  % (7811)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.46  % (7813)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.47  % (7809)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.47  % (7813)Refutation found. Thanks to Tanya!
% 0.22/0.47  % SZS status Theorem for theBenchmark
% 0.22/0.47  % SZS output start Proof for theBenchmark
% 0.22/0.47  fof(f261,plain,(
% 0.22/0.47    $false),
% 0.22/0.47    inference(avatar_sat_refutation,[],[f72,f77,f83,f94,f111,f128,f146,f160,f165,f194,f202,f210,f255])).
% 0.22/0.47  fof(f255,plain,(
% 0.22/0.47    spl2_15 | ~spl2_14),
% 0.22/0.47    inference(avatar_split_clause,[],[f254,f197,f207])).
% 0.22/0.47  fof(f207,plain,(
% 0.22/0.47    spl2_15 <=> sK0 = k4_subset_1(sK0,sK0,sK1)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.22/0.47  fof(f197,plain,(
% 0.22/0.47    spl2_14 <=> k4_subset_1(sK0,sK0,sK1) = k5_xboole_0(k5_xboole_0(sK0,sK1),sK1)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.22/0.47  fof(f254,plain,(
% 0.22/0.47    sK0 = k4_subset_1(sK0,sK0,sK1) | ~spl2_14),
% 0.22/0.47    inference(forward_demodulation,[],[f253,f39])).
% 0.22/0.47  fof(f39,plain,(
% 0.22/0.47    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.47    inference(cnf_transformation,[],[f3])).
% 0.22/0.47  fof(f3,axiom,(
% 0.22/0.47    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 0.22/0.47  fof(f253,plain,(
% 0.22/0.47    k4_subset_1(sK0,sK0,sK1) = k5_xboole_0(sK0,k1_xboole_0) | ~spl2_14),
% 0.22/0.47    inference(forward_demodulation,[],[f247,f37])).
% 0.22/0.47  fof(f37,plain,(
% 0.22/0.47    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f5])).
% 0.22/0.47  fof(f5,axiom,(
% 0.22/0.47    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 0.22/0.47  fof(f247,plain,(
% 0.22/0.47    k4_subset_1(sK0,sK0,sK1) = k5_xboole_0(sK0,k5_xboole_0(sK1,sK1)) | ~spl2_14),
% 0.22/0.47    inference(superposition,[],[f53,f199])).
% 0.22/0.47  fof(f199,plain,(
% 0.22/0.47    k4_subset_1(sK0,sK0,sK1) = k5_xboole_0(k5_xboole_0(sK0,sK1),sK1) | ~spl2_14),
% 0.22/0.47    inference(avatar_component_clause,[],[f197])).
% 0.22/0.47  fof(f53,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f4])).
% 0.22/0.47  fof(f4,axiom,(
% 0.22/0.47    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 0.22/0.47  fof(f210,plain,(
% 0.22/0.47    ~spl2_15 | spl2_3 | ~spl2_13),
% 0.22/0.47    inference(avatar_split_clause,[],[f205,f191,f80,f207])).
% 0.22/0.47  fof(f80,plain,(
% 0.22/0.47    spl2_3 <=> sK0 = k4_subset_1(sK0,sK1,sK0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.22/0.47  fof(f191,plain,(
% 0.22/0.47    spl2_13 <=> k4_subset_1(sK0,sK1,sK0) = k4_subset_1(sK0,sK0,sK1)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.22/0.47  fof(f205,plain,(
% 0.22/0.47    sK0 != k4_subset_1(sK0,sK0,sK1) | (spl2_3 | ~spl2_13)),
% 0.22/0.47    inference(superposition,[],[f82,f193])).
% 0.22/0.47  fof(f193,plain,(
% 0.22/0.47    k4_subset_1(sK0,sK1,sK0) = k4_subset_1(sK0,sK0,sK1) | ~spl2_13),
% 0.22/0.47    inference(avatar_component_clause,[],[f191])).
% 0.22/0.47  fof(f82,plain,(
% 0.22/0.47    sK0 != k4_subset_1(sK0,sK1,sK0) | spl2_3),
% 0.22/0.47    inference(avatar_component_clause,[],[f80])).
% 0.22/0.47  fof(f202,plain,(
% 0.22/0.47    spl2_14 | ~spl2_8 | ~spl2_10),
% 0.22/0.47    inference(avatar_split_clause,[],[f201,f162,f140,f197])).
% 0.22/0.47  fof(f140,plain,(
% 0.22/0.47    spl2_8 <=> sK1 = k3_xboole_0(sK0,sK1)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.22/0.47  fof(f162,plain,(
% 0.22/0.47    spl2_10 <=> k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) = k4_subset_1(sK0,sK0,sK1)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.22/0.47  fof(f201,plain,(
% 0.22/0.47    k4_subset_1(sK0,sK0,sK1) = k5_xboole_0(k5_xboole_0(sK0,sK1),sK1) | (~spl2_8 | ~spl2_10)),
% 0.22/0.47    inference(forward_demodulation,[],[f189,f142])).
% 0.22/0.47  fof(f142,plain,(
% 0.22/0.47    sK1 = k3_xboole_0(sK0,sK1) | ~spl2_8),
% 0.22/0.47    inference(avatar_component_clause,[],[f140])).
% 0.22/0.47  % (7810)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.48  % (7820)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.49  % (7822)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.49  % (7824)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.49  % (7817)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.49  % (7808)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.49  % (7815)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.49  % (7807)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.49  fof(f189,plain,(
% 0.22/0.49    k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) = k4_subset_1(sK0,sK0,sK1) | ~spl2_10),
% 0.22/0.49    inference(superposition,[],[f66,f164])).
% 0.22/0.49  fof(f164,plain,(
% 0.22/0.49    k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) = k4_subset_1(sK0,sK0,sK1) | ~spl2_10),
% 0.22/0.49    inference(avatar_component_clause,[],[f162])).
% 0.22/0.49  fof(f66,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 0.22/0.49    inference(definition_unfolding,[],[f45,f64])).
% 0.22/0.49  fof(f64,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 0.22/0.49    inference(definition_unfolding,[],[f43,f63])).
% 0.22/0.49  fof(f63,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.22/0.49    inference(definition_unfolding,[],[f44,f62])).
% 0.22/0.49  fof(f62,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.22/0.49    inference(definition_unfolding,[],[f52,f61])).
% 0.22/0.49  fof(f61,plain,(
% 0.22/0.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.22/0.49    inference(definition_unfolding,[],[f55,f60])).
% 0.22/0.49  fof(f60,plain,(
% 0.22/0.49    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.22/0.49    inference(definition_unfolding,[],[f56,f59])).
% 0.22/0.49  % (7814)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.49  fof(f59,plain,(
% 0.22/0.49    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.22/0.49    inference(definition_unfolding,[],[f57,f58])).
% 0.22/0.49  fof(f58,plain,(
% 0.22/0.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f13])).
% 0.22/0.49  fof(f13,axiom,(
% 0.22/0.49    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 0.22/0.49  fof(f57,plain,(
% 0.22/0.49    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f12])).
% 0.22/0.49  fof(f12,axiom,(
% 0.22/0.49    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 0.22/0.49  fof(f56,plain,(
% 0.22/0.49    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f11])).
% 0.22/0.49  fof(f11,axiom,(
% 0.22/0.49    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 0.22/0.49  fof(f55,plain,(
% 0.22/0.49    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f10])).
% 0.22/0.49  fof(f10,axiom,(
% 0.22/0.49    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.22/0.49  fof(f52,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f9])).
% 0.22/0.49  fof(f9,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.49  fof(f44,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f8])).
% 0.22/0.49  fof(f8,axiom,(
% 0.22/0.49    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.49  fof(f43,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f15])).
% 0.22/0.49  fof(f15,axiom,(
% 0.22/0.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.22/0.49  fof(f45,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f6])).
% 0.22/0.49  fof(f6,axiom,(
% 0.22/0.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).
% 0.22/0.49  fof(f194,plain,(
% 0.22/0.49    spl2_13 | ~spl2_9 | ~spl2_10),
% 0.22/0.49    inference(avatar_split_clause,[],[f187,f162,f157,f191])).
% 0.22/0.49  fof(f157,plain,(
% 0.22/0.49    spl2_9 <=> k4_subset_1(sK0,sK1,sK0) = k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.22/0.49  fof(f187,plain,(
% 0.22/0.49    k4_subset_1(sK0,sK1,sK0) = k4_subset_1(sK0,sK0,sK1) | (~spl2_9 | ~spl2_10)),
% 0.22/0.49    inference(backward_demodulation,[],[f159,f164])).
% 0.22/0.49  fof(f159,plain,(
% 0.22/0.49    k4_subset_1(sK0,sK1,sK0) = k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | ~spl2_9),
% 0.22/0.49    inference(avatar_component_clause,[],[f157])).
% 0.22/0.49  fof(f165,plain,(
% 0.22/0.49    spl2_10 | ~spl2_2),
% 0.22/0.49    inference(avatar_split_clause,[],[f150,f74,f162])).
% 0.22/0.49  fof(f74,plain,(
% 0.22/0.49    spl2_2 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.49  fof(f150,plain,(
% 0.22/0.49    k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) = k4_subset_1(sK0,sK0,sK1) | ~spl2_2),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f84,f76,f67])).
% 0.22/0.49  fof(f67,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) )),
% 0.22/0.49    inference(definition_unfolding,[],[f54,f64])).
% 0.22/0.49  fof(f54,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f29])).
% 0.22/0.49  fof(f29,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.49    inference(flattening,[],[f28])).
% 0.22/0.49  fof(f28,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.22/0.49    inference(ennf_transformation,[],[f21])).
% 0.22/0.49  fof(f21,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 0.22/0.49  fof(f76,plain,(
% 0.22/0.49    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl2_2),
% 0.22/0.49    inference(avatar_component_clause,[],[f74])).
% 0.22/0.49  fof(f84,plain,(
% 0.22/0.49    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.22/0.49    inference(forward_demodulation,[],[f40,f36])).
% 0.22/0.49  fof(f36,plain,(
% 0.22/0.49    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.22/0.49    inference(cnf_transformation,[],[f18])).
% 0.22/0.49  fof(f18,axiom,(
% 0.22/0.49    ! [X0] : k2_subset_1(X0) = X0),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 0.22/0.49  fof(f40,plain,(
% 0.22/0.49    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f19])).
% 0.22/0.49  fof(f19,axiom,(
% 0.22/0.49    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.22/0.49  fof(f160,plain,(
% 0.22/0.49    spl2_9 | ~spl2_2),
% 0.22/0.49    inference(avatar_split_clause,[],[f155,f74,f157])).
% 0.22/0.49  fof(f155,plain,(
% 0.22/0.49    k4_subset_1(sK0,sK1,sK0) = k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | ~spl2_2),
% 0.22/0.49    inference(forward_demodulation,[],[f151,f65])).
% 0.22/0.49  fof(f65,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)) )),
% 0.22/0.49    inference(definition_unfolding,[],[f42,f63,f63])).
% 0.22/0.49  fof(f42,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f7])).
% 0.22/0.49  fof(f7,axiom,(
% 0.22/0.49    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.22/0.49  fof(f151,plain,(
% 0.22/0.49    k4_subset_1(sK0,sK1,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK0)) | ~spl2_2),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f76,f84,f67])).
% 0.22/0.49  fof(f146,plain,(
% 0.22/0.49    spl2_8 | ~spl2_7),
% 0.22/0.49    inference(avatar_split_clause,[],[f138,f124,f140])).
% 0.22/0.49  fof(f124,plain,(
% 0.22/0.49    spl2_7 <=> sK1 = k3_xboole_0(sK1,sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.22/0.49  fof(f138,plain,(
% 0.22/0.49    sK1 = k3_xboole_0(sK0,sK1) | ~spl2_7),
% 0.22/0.49    inference(superposition,[],[f41,f126])).
% 0.22/0.49  fof(f126,plain,(
% 0.22/0.49    sK1 = k3_xboole_0(sK1,sK0) | ~spl2_7),
% 0.22/0.49    inference(avatar_component_clause,[],[f124])).
% 0.22/0.49  fof(f41,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.22/0.49  fof(f128,plain,(
% 0.22/0.49    spl2_7 | ~spl2_6),
% 0.22/0.49    inference(avatar_split_clause,[],[f122,f106,f124])).
% 0.22/0.49  fof(f106,plain,(
% 0.22/0.49    spl2_6 <=> r1_tarski(sK1,sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.22/0.49  fof(f122,plain,(
% 0.22/0.49    sK1 = k3_xboole_0(sK1,sK0) | ~spl2_6),
% 0.22/0.49    inference(resolution,[],[f108,f51])).
% 0.22/0.49  fof(f51,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.22/0.49    inference(cnf_transformation,[],[f27])).
% 0.22/0.49  fof(f27,plain,(
% 0.22/0.49    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.22/0.49    inference(ennf_transformation,[],[f2])).
% 0.22/0.49  fof(f2,axiom,(
% 0.22/0.49    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.22/0.49  fof(f108,plain,(
% 0.22/0.49    r1_tarski(sK1,sK0) | ~spl2_6),
% 0.22/0.49    inference(avatar_component_clause,[],[f106])).
% 0.22/0.49  fof(f111,plain,(
% 0.22/0.49    spl2_6 | ~spl2_4),
% 0.22/0.49    inference(avatar_split_clause,[],[f110,f91,f106])).
% 0.22/0.49  fof(f91,plain,(
% 0.22/0.49    spl2_4 <=> r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.22/0.49  fof(f110,plain,(
% 0.22/0.49    r1_tarski(sK1,sK0) | ~spl2_4),
% 0.22/0.49    inference(forward_demodulation,[],[f103,f38])).
% 0.22/0.49  fof(f38,plain,(
% 0.22/0.49    ( ! [X0] : (k3_tarski(k1_zfmisc_1(X0)) = X0) )),
% 0.22/0.49    inference(cnf_transformation,[],[f16])).
% 0.22/0.49  fof(f16,axiom,(
% 0.22/0.49    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).
% 0.22/0.49  fof(f103,plain,(
% 0.22/0.49    r1_tarski(sK1,k3_tarski(k1_zfmisc_1(sK0))) | ~spl2_4),
% 0.22/0.49    inference(resolution,[],[f93,f50])).
% 0.22/0.49  fof(f50,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(X0,k3_tarski(X1))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f26])).
% 0.22/0.49  fof(f26,plain,(
% 0.22/0.49    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1))),
% 0.22/0.49    inference(ennf_transformation,[],[f14])).
% 0.22/0.49  fof(f14,axiom,(
% 0.22/0.49    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(X0,k3_tarski(X1)))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).
% 0.22/0.49  fof(f93,plain,(
% 0.22/0.49    r2_hidden(sK1,k1_zfmisc_1(sK0)) | ~spl2_4),
% 0.22/0.49    inference(avatar_component_clause,[],[f91])).
% 0.22/0.49  fof(f94,plain,(
% 0.22/0.49    spl2_4 | ~spl2_2),
% 0.22/0.49    inference(avatar_split_clause,[],[f86,f74,f91])).
% 0.22/0.49  fof(f86,plain,(
% 0.22/0.49    r2_hidden(sK1,k1_zfmisc_1(sK0)) | ~spl2_2),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f35,f76,f46])).
% 0.22/0.49  fof(f46,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f32])).
% 0.22/0.49  fof(f32,plain,(
% 0.22/0.49    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 0.22/0.49    inference(nnf_transformation,[],[f25])).
% 0.22/0.49  fof(f25,plain,(
% 0.22/0.49    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f17])).
% 0.22/0.49  fof(f17,axiom,(
% 0.22/0.49    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 0.22/0.49  fof(f35,plain,(
% 0.22/0.49    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f20])).
% 0.22/0.49  fof(f20,axiom,(
% 0.22/0.49    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).
% 0.22/0.49  fof(f83,plain,(
% 0.22/0.49    ~spl2_3 | spl2_1),
% 0.22/0.49    inference(avatar_split_clause,[],[f78,f69,f80])).
% 0.22/0.49  fof(f69,plain,(
% 0.22/0.49    spl2_1 <=> k2_subset_1(sK0) = k4_subset_1(sK0,sK1,k2_subset_1(sK0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.49  fof(f78,plain,(
% 0.22/0.49    sK0 != k4_subset_1(sK0,sK1,sK0) | spl2_1),
% 0.22/0.49    inference(backward_demodulation,[],[f71,f36])).
% 0.22/0.49  fof(f71,plain,(
% 0.22/0.49    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0)) | spl2_1),
% 0.22/0.49    inference(avatar_component_clause,[],[f69])).
% 0.22/0.49  fof(f77,plain,(
% 0.22/0.49    spl2_2),
% 0.22/0.49    inference(avatar_split_clause,[],[f33,f74])).
% 0.22/0.49  fof(f33,plain,(
% 0.22/0.49    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.22/0.49    inference(cnf_transformation,[],[f31])).
% 0.22/0.49  fof(f31,plain,(
% 0.22/0.49    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0)) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f30])).
% 0.22/0.49  fof(f30,plain,(
% 0.22/0.49    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0)) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f24,plain,(
% 0.22/0.49    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f23])).
% 0.22/0.49  fof(f23,negated_conjecture,(
% 0.22/0.49    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)))),
% 0.22/0.49    inference(negated_conjecture,[],[f22])).
% 0.22/0.49  fof(f22,conjecture,(
% 0.22/0.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_subset_1)).
% 0.22/0.49  fof(f72,plain,(
% 0.22/0.49    ~spl2_1),
% 0.22/0.49    inference(avatar_split_clause,[],[f34,f69])).
% 0.22/0.49  fof(f34,plain,(
% 0.22/0.49    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0))),
% 0.22/0.49    inference(cnf_transformation,[],[f31])).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (7813)------------------------------
% 0.22/0.49  % (7813)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (7813)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (7813)Memory used [KB]: 6268
% 0.22/0.49  % (7813)Time elapsed: 0.048 s
% 0.22/0.49  % (7813)------------------------------
% 0.22/0.49  % (7813)------------------------------
% 0.22/0.50  % (7803)Success in time 0.134 s
%------------------------------------------------------------------------------
