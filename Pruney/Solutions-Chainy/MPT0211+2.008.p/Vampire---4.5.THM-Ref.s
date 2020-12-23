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
% DateTime   : Thu Dec  3 12:34:43 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 123 expanded)
%              Number of leaves         :   24 (  63 expanded)
%              Depth                    :    6
%              Number of atoms          :  155 ( 243 expanded)
%              Number of equality atoms :   61 ( 105 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1041,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f29,f37,f49,f53,f57,f72,f76,f101,f119,f159,f177,f197,f243,f336,f471,f957,f1040])).

fof(f1040,plain,
    ( spl3_12
    | ~ spl3_32
    | ~ spl3_57 ),
    inference(avatar_contradiction_clause,[],[f1039])).

fof(f1039,plain,
    ( $false
    | spl3_12
    | ~ spl3_32
    | ~ spl3_57 ),
    inference(subsumption_resolution,[],[f100,f989])).

fof(f989,plain,
    ( ! [X39,X41,X40] : k1_enumset1(X41,X39,X40) = k2_enumset1(X39,X41,X40,X41)
    | ~ spl3_32
    | ~ spl3_57 ),
    inference(superposition,[],[f956,f335])).

fof(f335,plain,
    ( ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X1,X2,X0,X0)
    | ~ spl3_32 ),
    inference(avatar_component_clause,[],[f334])).

fof(f334,plain,
    ( spl3_32
  <=> ! [X1,X0,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X1,X2,X0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f956,plain,
    ( ! [X6,X4,X7,X5] : k2_enumset1(X7,X4,X5,X6) = k2_enumset1(X7,X5,X6,X4)
    | ~ spl3_57 ),
    inference(avatar_component_clause,[],[f955])).

fof(f955,plain,
    ( spl3_57
  <=> ! [X5,X7,X4,X6] : k2_enumset1(X7,X4,X5,X6) = k2_enumset1(X7,X5,X6,X4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_57])])).

fof(f100,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK1,sK0,sK2,sK0)
    | spl3_12 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl3_12
  <=> k1_enumset1(sK0,sK1,sK2) = k2_enumset1(sK1,sK0,sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f957,plain,
    ( spl3_57
    | ~ spl3_20
    | ~ spl3_39 ),
    inference(avatar_split_clause,[],[f480,f469,f157,f955])).

fof(f157,plain,
    ( spl3_20
  <=> ! [X5,X7,X4,X6] : k2_xboole_0(k1_enumset1(X5,X6,X7),k1_tarski(X4)) = k2_enumset1(X4,X5,X6,X7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f469,plain,
    ( spl3_39
  <=> ! [X3,X5,X2,X4] : k2_enumset1(X5,X2,X3,X4) = k2_xboole_0(k1_enumset1(X4,X2,X3),k1_tarski(X5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).

fof(f480,plain,
    ( ! [X6,X4,X7,X5] : k2_enumset1(X7,X4,X5,X6) = k2_enumset1(X7,X5,X6,X4)
    | ~ spl3_20
    | ~ spl3_39 ),
    inference(superposition,[],[f470,f158])).

fof(f158,plain,
    ( ! [X6,X4,X7,X5] : k2_xboole_0(k1_enumset1(X5,X6,X7),k1_tarski(X4)) = k2_enumset1(X4,X5,X6,X7)
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f157])).

fof(f470,plain,
    ( ! [X4,X2,X5,X3] : k2_enumset1(X5,X2,X3,X4) = k2_xboole_0(k1_enumset1(X4,X2,X3),k1_tarski(X5))
    | ~ spl3_39 ),
    inference(avatar_component_clause,[],[f469])).

fof(f471,plain,
    ( spl3_39
    | ~ spl3_20
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f205,f195,f157,f469])).

fof(f195,plain,
    ( spl3_23
  <=> ! [X3,X5,X4] : k1_enumset1(X3,X4,X5) = k1_enumset1(X5,X3,X4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f205,plain,
    ( ! [X4,X2,X5,X3] : k2_enumset1(X5,X2,X3,X4) = k2_xboole_0(k1_enumset1(X4,X2,X3),k1_tarski(X5))
    | ~ spl3_20
    | ~ spl3_23 ),
    inference(superposition,[],[f158,f196])).

fof(f196,plain,
    ( ! [X4,X5,X3] : k1_enumset1(X3,X4,X5) = k1_enumset1(X5,X3,X4)
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f195])).

fof(f336,plain,
    ( spl3_32
    | ~ spl3_6
    | ~ spl3_26 ),
    inference(avatar_split_clause,[],[f244,f241,f47,f334])).

fof(f47,plain,
    ( spl3_6
  <=> ! [X1,X0,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f241,plain,
    ( spl3_26
  <=> ! [X5,X7,X4,X6] : k2_enumset1(X4,X5,X6,X7) = k2_enumset1(X6,X7,X4,X5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f244,plain,
    ( ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X1,X2,X0,X0)
    | ~ spl3_6
    | ~ spl3_26 ),
    inference(superposition,[],[f242,f48])).

fof(f48,plain,
    ( ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f47])).

fof(f242,plain,
    ( ! [X6,X4,X7,X5] : k2_enumset1(X4,X5,X6,X7) = k2_enumset1(X6,X7,X4,X5)
    | ~ spl3_26 ),
    inference(avatar_component_clause,[],[f241])).

fof(f243,plain,
    ( spl3_26
    | ~ spl3_10
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f180,f175,f74,f241])).

fof(f74,plain,
    ( spl3_10
  <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f175,plain,
    ( spl3_21
  <=> ! [X5,X7,X4,X6] : k2_enumset1(X4,X5,X6,X7) = k2_xboole_0(k2_tarski(X6,X7),k2_tarski(X4,X5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f180,plain,
    ( ! [X6,X4,X7,X5] : k2_enumset1(X4,X5,X6,X7) = k2_enumset1(X6,X7,X4,X5)
    | ~ spl3_10
    | ~ spl3_21 ),
    inference(superposition,[],[f176,f75])).

fof(f75,plain,
    ( ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f74])).

fof(f176,plain,
    ( ! [X6,X4,X7,X5] : k2_enumset1(X4,X5,X6,X7) = k2_xboole_0(k2_tarski(X6,X7),k2_tarski(X4,X5))
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f175])).

fof(f197,plain,
    ( spl3_23
    | ~ spl3_8
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f125,f117,f55,f195])).

fof(f55,plain,
    ( spl3_8
  <=> ! [X1,X0,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f117,plain,
    ( spl3_15
  <=> ! [X3,X5,X4] : k2_xboole_0(k2_tarski(X4,X5),k1_tarski(X3)) = k1_enumset1(X3,X4,X5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f125,plain,
    ( ! [X4,X5,X3] : k1_enumset1(X3,X4,X5) = k1_enumset1(X5,X3,X4)
    | ~ spl3_8
    | ~ spl3_15 ),
    inference(superposition,[],[f118,f56])).

fof(f56,plain,
    ( ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f55])).

fof(f118,plain,
    ( ! [X4,X5,X3] : k2_xboole_0(k2_tarski(X4,X5),k1_tarski(X3)) = k1_enumset1(X3,X4,X5)
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f117])).

fof(f177,plain,
    ( spl3_21
    | ~ spl3_3
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f90,f74,f35,f175])).

fof(f35,plain,
    ( spl3_3
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f90,plain,
    ( ! [X6,X4,X7,X5] : k2_enumset1(X4,X5,X6,X7) = k2_xboole_0(k2_tarski(X6,X7),k2_tarski(X4,X5))
    | ~ spl3_3
    | ~ spl3_10 ),
    inference(superposition,[],[f75,f36])).

fof(f36,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f35])).

fof(f159,plain,
    ( spl3_20
    | ~ spl3_3
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f78,f70,f35,f157])).

fof(f70,plain,
    ( spl3_9
  <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f78,plain,
    ( ! [X6,X4,X7,X5] : k2_xboole_0(k1_enumset1(X5,X6,X7),k1_tarski(X4)) = k2_enumset1(X4,X5,X6,X7)
    | ~ spl3_3
    | ~ spl3_9 ),
    inference(superposition,[],[f71,f36])).

fof(f71,plain,
    ( ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f70])).

fof(f119,plain,
    ( spl3_15
    | ~ spl3_3
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f59,f51,f35,f117])).

fof(f51,plain,
    ( spl3_7
  <=> ! [X1,X0,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f59,plain,
    ( ! [X4,X5,X3] : k2_xboole_0(k2_tarski(X4,X5),k1_tarski(X3)) = k1_enumset1(X3,X4,X5)
    | ~ spl3_3
    | ~ spl3_7 ),
    inference(superposition,[],[f52,f36])).

fof(f52,plain,
    ( ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f51])).

fof(f101,plain,
    ( ~ spl3_12
    | spl3_1
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f92,f74,f26,f98])).

fof(f26,plain,
    ( spl3_1
  <=> k1_enumset1(sK0,sK1,sK2) = k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f92,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK1,sK0,sK2,sK0)
    | spl3_1
    | ~ spl3_10 ),
    inference(superposition,[],[f28,f75])).

fof(f28,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f26])).

fof(f76,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f24,f74])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).

fof(f72,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f23,f70])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

fof(f57,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f22,f55])).

fof(f22,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).

fof(f53,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f21,f51])).

fof(f21,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

fof(f49,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f20,f47])).

fof(f20,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f37,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f17,f35])).

fof(f17,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f29,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f15,f26])).

fof(f15,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))
   => k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n018.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:44:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.46  % (28573)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.46  % (28580)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.46  % (28574)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.47  % (28568)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.47  % (28578)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.47  % (28579)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.48  % (28579)Refutation not found, incomplete strategy% (28579)------------------------------
% 0.21/0.48  % (28579)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (28579)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (28579)Memory used [KB]: 10618
% 0.21/0.48  % (28579)Time elapsed: 0.060 s
% 0.21/0.48  % (28579)------------------------------
% 0.21/0.48  % (28579)------------------------------
% 0.21/0.48  % (28583)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.48  % (28582)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.48  % (28571)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.49  % (28581)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.49  % (28575)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.49  % (28572)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.50  % (28573)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f1041,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f29,f37,f49,f53,f57,f72,f76,f101,f119,f159,f177,f197,f243,f336,f471,f957,f1040])).
% 0.21/0.50  fof(f1040,plain,(
% 0.21/0.50    spl3_12 | ~spl3_32 | ~spl3_57),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f1039])).
% 0.21/0.50  fof(f1039,plain,(
% 0.21/0.50    $false | (spl3_12 | ~spl3_32 | ~spl3_57)),
% 0.21/0.50    inference(subsumption_resolution,[],[f100,f989])).
% 0.21/0.50  fof(f989,plain,(
% 0.21/0.50    ( ! [X39,X41,X40] : (k1_enumset1(X41,X39,X40) = k2_enumset1(X39,X41,X40,X41)) ) | (~spl3_32 | ~spl3_57)),
% 0.21/0.50    inference(superposition,[],[f956,f335])).
% 0.21/0.50  fof(f335,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X1,X2,X0,X0)) ) | ~spl3_32),
% 0.21/0.50    inference(avatar_component_clause,[],[f334])).
% 0.21/0.50  fof(f334,plain,(
% 0.21/0.50    spl3_32 <=> ! [X1,X0,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X1,X2,X0,X0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 0.21/0.50  fof(f956,plain,(
% 0.21/0.50    ( ! [X6,X4,X7,X5] : (k2_enumset1(X7,X4,X5,X6) = k2_enumset1(X7,X5,X6,X4)) ) | ~spl3_57),
% 0.21/0.50    inference(avatar_component_clause,[],[f955])).
% 0.21/0.50  fof(f955,plain,(
% 0.21/0.50    spl3_57 <=> ! [X5,X7,X4,X6] : k2_enumset1(X7,X4,X5,X6) = k2_enumset1(X7,X5,X6,X4)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_57])])).
% 0.21/0.50  fof(f100,plain,(
% 0.21/0.50    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK1,sK0,sK2,sK0) | spl3_12),
% 0.21/0.50    inference(avatar_component_clause,[],[f98])).
% 0.21/0.50  fof(f98,plain,(
% 0.21/0.50    spl3_12 <=> k1_enumset1(sK0,sK1,sK2) = k2_enumset1(sK1,sK0,sK2,sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.50  fof(f957,plain,(
% 0.21/0.50    spl3_57 | ~spl3_20 | ~spl3_39),
% 0.21/0.50    inference(avatar_split_clause,[],[f480,f469,f157,f955])).
% 0.21/0.50  fof(f157,plain,(
% 0.21/0.50    spl3_20 <=> ! [X5,X7,X4,X6] : k2_xboole_0(k1_enumset1(X5,X6,X7),k1_tarski(X4)) = k2_enumset1(X4,X5,X6,X7)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.21/0.50  fof(f469,plain,(
% 0.21/0.50    spl3_39 <=> ! [X3,X5,X2,X4] : k2_enumset1(X5,X2,X3,X4) = k2_xboole_0(k1_enumset1(X4,X2,X3),k1_tarski(X5))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).
% 0.21/0.50  fof(f480,plain,(
% 0.21/0.50    ( ! [X6,X4,X7,X5] : (k2_enumset1(X7,X4,X5,X6) = k2_enumset1(X7,X5,X6,X4)) ) | (~spl3_20 | ~spl3_39)),
% 0.21/0.50    inference(superposition,[],[f470,f158])).
% 0.21/0.50  fof(f158,plain,(
% 0.21/0.50    ( ! [X6,X4,X7,X5] : (k2_xboole_0(k1_enumset1(X5,X6,X7),k1_tarski(X4)) = k2_enumset1(X4,X5,X6,X7)) ) | ~spl3_20),
% 0.21/0.50    inference(avatar_component_clause,[],[f157])).
% 0.21/0.50  fof(f470,plain,(
% 0.21/0.50    ( ! [X4,X2,X5,X3] : (k2_enumset1(X5,X2,X3,X4) = k2_xboole_0(k1_enumset1(X4,X2,X3),k1_tarski(X5))) ) | ~spl3_39),
% 0.21/0.50    inference(avatar_component_clause,[],[f469])).
% 0.21/0.50  fof(f471,plain,(
% 0.21/0.50    spl3_39 | ~spl3_20 | ~spl3_23),
% 0.21/0.50    inference(avatar_split_clause,[],[f205,f195,f157,f469])).
% 0.21/0.50  fof(f195,plain,(
% 0.21/0.50    spl3_23 <=> ! [X3,X5,X4] : k1_enumset1(X3,X4,X5) = k1_enumset1(X5,X3,X4)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.21/0.50  fof(f205,plain,(
% 0.21/0.50    ( ! [X4,X2,X5,X3] : (k2_enumset1(X5,X2,X3,X4) = k2_xboole_0(k1_enumset1(X4,X2,X3),k1_tarski(X5))) ) | (~spl3_20 | ~spl3_23)),
% 0.21/0.50    inference(superposition,[],[f158,f196])).
% 0.21/0.50  fof(f196,plain,(
% 0.21/0.50    ( ! [X4,X5,X3] : (k1_enumset1(X3,X4,X5) = k1_enumset1(X5,X3,X4)) ) | ~spl3_23),
% 0.21/0.50    inference(avatar_component_clause,[],[f195])).
% 0.21/0.50  fof(f336,plain,(
% 0.21/0.50    spl3_32 | ~spl3_6 | ~spl3_26),
% 0.21/0.50    inference(avatar_split_clause,[],[f244,f241,f47,f334])).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    spl3_6 <=> ! [X1,X0,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.50  fof(f241,plain,(
% 0.21/0.50    spl3_26 <=> ! [X5,X7,X4,X6] : k2_enumset1(X4,X5,X6,X7) = k2_enumset1(X6,X7,X4,X5)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 0.21/0.50  fof(f244,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X1,X2,X0,X0)) ) | (~spl3_6 | ~spl3_26)),
% 0.21/0.50    inference(superposition,[],[f242,f48])).
% 0.21/0.50  fof(f48,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) ) | ~spl3_6),
% 0.21/0.50    inference(avatar_component_clause,[],[f47])).
% 0.21/0.50  fof(f242,plain,(
% 0.21/0.50    ( ! [X6,X4,X7,X5] : (k2_enumset1(X4,X5,X6,X7) = k2_enumset1(X6,X7,X4,X5)) ) | ~spl3_26),
% 0.21/0.50    inference(avatar_component_clause,[],[f241])).
% 0.21/0.50  fof(f243,plain,(
% 0.21/0.50    spl3_26 | ~spl3_10 | ~spl3_21),
% 0.21/0.50    inference(avatar_split_clause,[],[f180,f175,f74,f241])).
% 0.21/0.50  fof(f74,plain,(
% 0.21/0.50    spl3_10 <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.50  fof(f175,plain,(
% 0.21/0.50    spl3_21 <=> ! [X5,X7,X4,X6] : k2_enumset1(X4,X5,X6,X7) = k2_xboole_0(k2_tarski(X6,X7),k2_tarski(X4,X5))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.21/0.50  fof(f180,plain,(
% 0.21/0.50    ( ! [X6,X4,X7,X5] : (k2_enumset1(X4,X5,X6,X7) = k2_enumset1(X6,X7,X4,X5)) ) | (~spl3_10 | ~spl3_21)),
% 0.21/0.50    inference(superposition,[],[f176,f75])).
% 0.21/0.50  fof(f75,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) ) | ~spl3_10),
% 0.21/0.50    inference(avatar_component_clause,[],[f74])).
% 0.21/0.50  fof(f176,plain,(
% 0.21/0.50    ( ! [X6,X4,X7,X5] : (k2_enumset1(X4,X5,X6,X7) = k2_xboole_0(k2_tarski(X6,X7),k2_tarski(X4,X5))) ) | ~spl3_21),
% 0.21/0.50    inference(avatar_component_clause,[],[f175])).
% 0.21/0.50  fof(f197,plain,(
% 0.21/0.50    spl3_23 | ~spl3_8 | ~spl3_15),
% 0.21/0.50    inference(avatar_split_clause,[],[f125,f117,f55,f195])).
% 0.21/0.50  fof(f55,plain,(
% 0.21/0.50    spl3_8 <=> ! [X1,X0,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.50  fof(f117,plain,(
% 0.21/0.50    spl3_15 <=> ! [X3,X5,X4] : k2_xboole_0(k2_tarski(X4,X5),k1_tarski(X3)) = k1_enumset1(X3,X4,X5)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.21/0.50  fof(f125,plain,(
% 0.21/0.50    ( ! [X4,X5,X3] : (k1_enumset1(X3,X4,X5) = k1_enumset1(X5,X3,X4)) ) | (~spl3_8 | ~spl3_15)),
% 0.21/0.50    inference(superposition,[],[f118,f56])).
% 0.21/0.50  fof(f56,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))) ) | ~spl3_8),
% 0.21/0.50    inference(avatar_component_clause,[],[f55])).
% 0.21/0.50  fof(f118,plain,(
% 0.21/0.50    ( ! [X4,X5,X3] : (k2_xboole_0(k2_tarski(X4,X5),k1_tarski(X3)) = k1_enumset1(X3,X4,X5)) ) | ~spl3_15),
% 0.21/0.50    inference(avatar_component_clause,[],[f117])).
% 0.21/0.50  fof(f177,plain,(
% 0.21/0.50    spl3_21 | ~spl3_3 | ~spl3_10),
% 0.21/0.50    inference(avatar_split_clause,[],[f90,f74,f35,f175])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    spl3_3 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.50  fof(f90,plain,(
% 0.21/0.50    ( ! [X6,X4,X7,X5] : (k2_enumset1(X4,X5,X6,X7) = k2_xboole_0(k2_tarski(X6,X7),k2_tarski(X4,X5))) ) | (~spl3_3 | ~spl3_10)),
% 0.21/0.50    inference(superposition,[],[f75,f36])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) ) | ~spl3_3),
% 0.21/0.50    inference(avatar_component_clause,[],[f35])).
% 0.21/0.50  fof(f159,plain,(
% 0.21/0.50    spl3_20 | ~spl3_3 | ~spl3_9),
% 0.21/0.50    inference(avatar_split_clause,[],[f78,f70,f35,f157])).
% 0.21/0.50  fof(f70,plain,(
% 0.21/0.50    spl3_9 <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.50  fof(f78,plain,(
% 0.21/0.50    ( ! [X6,X4,X7,X5] : (k2_xboole_0(k1_enumset1(X5,X6,X7),k1_tarski(X4)) = k2_enumset1(X4,X5,X6,X7)) ) | (~spl3_3 | ~spl3_9)),
% 0.21/0.50    inference(superposition,[],[f71,f36])).
% 0.21/0.50  fof(f71,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))) ) | ~spl3_9),
% 0.21/0.50    inference(avatar_component_clause,[],[f70])).
% 0.21/0.50  fof(f119,plain,(
% 0.21/0.50    spl3_15 | ~spl3_3 | ~spl3_7),
% 0.21/0.50    inference(avatar_split_clause,[],[f59,f51,f35,f117])).
% 0.21/0.50  fof(f51,plain,(
% 0.21/0.50    spl3_7 <=> ! [X1,X0,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.50  fof(f59,plain,(
% 0.21/0.50    ( ! [X4,X5,X3] : (k2_xboole_0(k2_tarski(X4,X5),k1_tarski(X3)) = k1_enumset1(X3,X4,X5)) ) | (~spl3_3 | ~spl3_7)),
% 0.21/0.50    inference(superposition,[],[f52,f36])).
% 0.21/0.50  fof(f52,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))) ) | ~spl3_7),
% 0.21/0.50    inference(avatar_component_clause,[],[f51])).
% 0.21/0.50  fof(f101,plain,(
% 0.21/0.50    ~spl3_12 | spl3_1 | ~spl3_10),
% 0.21/0.50    inference(avatar_split_clause,[],[f92,f74,f26,f98])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    spl3_1 <=> k1_enumset1(sK0,sK1,sK2) = k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.50  fof(f92,plain,(
% 0.21/0.50    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK1,sK0,sK2,sK0) | (spl3_1 | ~spl3_10)),
% 0.21/0.50    inference(superposition,[],[f28,f75])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) | spl3_1),
% 0.21/0.50    inference(avatar_component_clause,[],[f26])).
% 0.21/0.50  fof(f76,plain,(
% 0.21/0.50    spl3_10),
% 0.21/0.50    inference(avatar_split_clause,[],[f24,f74])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).
% 0.21/0.50  fof(f72,plain,(
% 0.21/0.50    spl3_9),
% 0.21/0.50    inference(avatar_split_clause,[],[f23,f70])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).
% 0.21/0.50  fof(f57,plain,(
% 0.21/0.50    spl3_8),
% 0.21/0.50    inference(avatar_split_clause,[],[f22,f55])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).
% 0.21/0.50  fof(f53,plain,(
% 0.21/0.50    spl3_7),
% 0.21/0.50    inference(avatar_split_clause,[],[f21,f51])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).
% 0.21/0.50  fof(f49,plain,(
% 0.21/0.50    spl3_6),
% 0.21/0.50    inference(avatar_split_clause,[],[f20,f47])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    spl3_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f17,f35])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ~spl3_1),
% 0.21/0.50    inference(avatar_split_clause,[],[f15,f26])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0))),
% 0.21/0.50    inference(cnf_transformation,[],[f14])).
% 0.21/0.50  fof(f14,plain,(
% 0.21/0.50    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0))),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f13])).
% 0.21/0.50  fof(f13,plain,(
% 0.21/0.50    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) => k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f12,plain,(
% 0.21/0.50    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f11])).
% 0.21/0.50  fof(f11,negated_conjecture,(
% 0.21/0.50    ~! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))),
% 0.21/0.50    inference(negated_conjecture,[],[f10])).
% 0.21/0.50  fof(f10,conjecture,(
% 0.21/0.50    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_enumset1)).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (28573)------------------------------
% 0.21/0.50  % (28573)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (28573)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (28573)Memory used [KB]: 6652
% 0.21/0.50  % (28573)Time elapsed: 0.080 s
% 0.21/0.50  % (28573)------------------------------
% 0.21/0.50  % (28573)------------------------------
% 0.21/0.50  % (28569)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.50  % (28567)Success in time 0.143 s
%------------------------------------------------------------------------------
