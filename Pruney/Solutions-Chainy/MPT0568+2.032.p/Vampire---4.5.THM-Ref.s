%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:14 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 198 expanded)
%              Number of leaves         :   24 (  69 expanded)
%              Depth                    :   19
%              Number of atoms          :  127 ( 251 expanded)
%              Number of equality atoms :   74 ( 185 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f150,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f59,f64,f69,f74,f82,f149])).

fof(f149,plain,
    ( spl1_1
    | ~ spl1_3
    | ~ spl1_4
    | ~ spl1_5 ),
    inference(avatar_contradiction_clause,[],[f145])).

fof(f145,plain,
    ( $false
    | spl1_1
    | ~ spl1_3
    | ~ spl1_4
    | ~ spl1_5 ),
    inference(unit_resulting_resolution,[],[f58,f116])).

fof(f116,plain,
    ( ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)
    | ~ spl1_3
    | ~ spl1_4
    | ~ spl1_5 ),
    inference(forward_demodulation,[],[f114,f101])).

fof(f101,plain,
    ( k1_xboole_0 = k10_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ spl1_3
    | ~ spl1_4
    | ~ spl1_5 ),
    inference(forward_demodulation,[],[f100,f68])).

fof(f68,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl1_3
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

% (31087)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
fof(f100,plain,
    ( k1_relat_1(k1_xboole_0) = k10_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ spl1_4
    | ~ spl1_5 ),
    inference(forward_demodulation,[],[f97,f73])).

fof(f73,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl1_4 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl1_4
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f97,plain,
    ( k1_relat_1(k1_xboole_0) = k10_relat_1(k1_xboole_0,k2_relat_1(k1_xboole_0))
    | ~ spl1_5 ),
    inference(unit_resulting_resolution,[],[f81,f33])).

fof(f33,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

fof(f81,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl1_5 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl1_5
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f114,plain,
    ( ! [X0] : k10_relat_1(k1_xboole_0,X0) = k10_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ spl1_4
    | ~ spl1_5 ),
    inference(backward_demodulation,[],[f102,f106])).

fof(f106,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k5_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) ),
    inference(superposition,[],[f92,f51])).

fof(f51,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_setfam_1(k5_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0))) ),
    inference(definition_unfolding,[],[f30,f49])).

fof(f49,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f38,f48])).

fof(f48,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f35,f47])).

fof(f47,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f36,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f40,f45])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f41,f44])).

fof(f44,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f42,f43])).

fof(f43,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f42,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f41,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f40,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f36,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f35,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f38,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f30,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(f92,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(forward_demodulation,[],[f91,f32])).

fof(f32,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f91,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f90,f51])).

fof(f90,plain,(
    ! [X0] : k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k1_setfam_1(k5_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)))) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f86,f32])).

fof(f86,plain,(
    ! [X0] : k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k1_setfam_1(k5_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[],[f53,f52])).

fof(f52,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f31,f48])).

fof(f31,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f53,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k5_enumset1(X1,X1,X1,X1,X1,X1,X0)))) = k5_xboole_0(X1,k5_xboole_0(X0,k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)))) ),
    inference(definition_unfolding,[],[f34,f50,f50])).

fof(f50,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k5_enumset1(X1,X1,X1,X1,X1,X1,X0)))) ),
    inference(definition_unfolding,[],[f37,f49])).

fof(f37,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f34,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f102,plain,
    ( ! [X0] : k10_relat_1(k1_xboole_0,X0) = k10_relat_1(k1_xboole_0,k1_setfam_1(k5_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)))
    | ~ spl1_4
    | ~ spl1_5 ),
    inference(forward_demodulation,[],[f96,f73])).

fof(f96,plain,
    ( ! [X0] : k10_relat_1(k1_xboole_0,X0) = k10_relat_1(k1_xboole_0,k1_setfam_1(k5_enumset1(k2_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0),X0)))
    | ~ spl1_5 ),
    inference(unit_resulting_resolution,[],[f81,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k10_relat_1(X1,X0) = k10_relat_1(X1,k1_setfam_1(k5_enumset1(k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),X0))) ) ),
    inference(definition_unfolding,[],[f39,f48])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).

fof(f58,plain,
    ( k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0)
    | spl1_1 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl1_1
  <=> k1_xboole_0 = k10_relat_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f82,plain,
    ( spl1_5
    | ~ spl1_2 ),
    inference(avatar_split_clause,[],[f75,f61,f79])).

fof(f61,plain,
    ( spl1_2
  <=> k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f75,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl1_2 ),
    inference(superposition,[],[f29,f63])).

fof(f63,plain,
    ( k1_xboole_0 = k6_relat_1(k1_xboole_0)
    | ~ spl1_2 ),
    inference(avatar_component_clause,[],[f61])).

fof(f29,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f74,plain,(
    spl1_4 ),
    inference(avatar_split_clause,[],[f28,f71])).

fof(f28,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f69,plain,(
    spl1_3 ),
    inference(avatar_split_clause,[],[f27,f66])).

fof(f27,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f16])).

fof(f64,plain,(
    spl1_2 ),
    inference(avatar_split_clause,[],[f26,f61])).

fof(f26,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

fof(f59,plain,(
    ~ spl1_1 ),
    inference(avatar_split_clause,[],[f25,f56])).

fof(f25,plain,(
    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f23])).

fof(f23,plain,
    ( ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0)
   => k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:33:34 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.42  % (31082)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.43  % (31091)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.44  % (31097)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.44  % (31083)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.44  % (31097)Refutation found. Thanks to Tanya!
% 0.22/0.44  % SZS status Theorem for theBenchmark
% 0.22/0.44  % SZS output start Proof for theBenchmark
% 0.22/0.44  fof(f150,plain,(
% 0.22/0.44    $false),
% 0.22/0.44    inference(avatar_sat_refutation,[],[f59,f64,f69,f74,f82,f149])).
% 0.22/0.44  fof(f149,plain,(
% 0.22/0.44    spl1_1 | ~spl1_3 | ~spl1_4 | ~spl1_5),
% 0.22/0.44    inference(avatar_contradiction_clause,[],[f145])).
% 0.22/0.44  fof(f145,plain,(
% 0.22/0.44    $false | (spl1_1 | ~spl1_3 | ~spl1_4 | ~spl1_5)),
% 0.22/0.44    inference(unit_resulting_resolution,[],[f58,f116])).
% 0.22/0.44  fof(f116,plain,(
% 0.22/0.44    ( ! [X0] : (k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)) ) | (~spl1_3 | ~spl1_4 | ~spl1_5)),
% 0.22/0.44    inference(forward_demodulation,[],[f114,f101])).
% 0.22/0.44  fof(f101,plain,(
% 0.22/0.44    k1_xboole_0 = k10_relat_1(k1_xboole_0,k1_xboole_0) | (~spl1_3 | ~spl1_4 | ~spl1_5)),
% 0.22/0.44    inference(forward_demodulation,[],[f100,f68])).
% 0.22/0.44  fof(f68,plain,(
% 0.22/0.44    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl1_3),
% 0.22/0.44    inference(avatar_component_clause,[],[f66])).
% 0.22/0.44  fof(f66,plain,(
% 0.22/0.44    spl1_3 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.22/0.44  % (31087)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.44  fof(f100,plain,(
% 0.22/0.44    k1_relat_1(k1_xboole_0) = k10_relat_1(k1_xboole_0,k1_xboole_0) | (~spl1_4 | ~spl1_5)),
% 0.22/0.44    inference(forward_demodulation,[],[f97,f73])).
% 0.22/0.44  fof(f73,plain,(
% 0.22/0.44    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl1_4),
% 0.22/0.44    inference(avatar_component_clause,[],[f71])).
% 0.22/0.44  fof(f71,plain,(
% 0.22/0.44    spl1_4 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.22/0.44  fof(f97,plain,(
% 0.22/0.44    k1_relat_1(k1_xboole_0) = k10_relat_1(k1_xboole_0,k2_relat_1(k1_xboole_0)) | ~spl1_5),
% 0.22/0.44    inference(unit_resulting_resolution,[],[f81,f33])).
% 0.22/0.44  fof(f33,plain,(
% 0.22/0.44    ( ! [X0] : (~v1_relat_1(X0) | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f21])).
% 0.22/0.44  fof(f21,plain,(
% 0.22/0.44    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.44    inference(ennf_transformation,[],[f15])).
% 0.22/0.44  fof(f15,axiom,(
% 0.22/0.44    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).
% 0.22/0.44  fof(f81,plain,(
% 0.22/0.44    v1_relat_1(k1_xboole_0) | ~spl1_5),
% 0.22/0.44    inference(avatar_component_clause,[],[f79])).
% 0.22/0.44  fof(f79,plain,(
% 0.22/0.44    spl1_5 <=> v1_relat_1(k1_xboole_0)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.22/0.44  fof(f114,plain,(
% 0.22/0.44    ( ! [X0] : (k10_relat_1(k1_xboole_0,X0) = k10_relat_1(k1_xboole_0,k1_xboole_0)) ) | (~spl1_4 | ~spl1_5)),
% 0.22/0.44    inference(backward_demodulation,[],[f102,f106])).
% 0.22/0.44  fof(f106,plain,(
% 0.22/0.44    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k5_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0))) )),
% 0.22/0.44    inference(superposition,[],[f92,f51])).
% 0.22/0.44  fof(f51,plain,(
% 0.22/0.44    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_setfam_1(k5_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)))) )),
% 0.22/0.44    inference(definition_unfolding,[],[f30,f49])).
% 0.22/0.44  fof(f49,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)))) )),
% 0.22/0.44    inference(definition_unfolding,[],[f38,f48])).
% 0.22/0.44  fof(f48,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) )),
% 0.22/0.44    inference(definition_unfolding,[],[f35,f47])).
% 0.22/0.44  fof(f47,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) )),
% 0.22/0.44    inference(definition_unfolding,[],[f36,f46])).
% 0.22/0.44  fof(f46,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) )),
% 0.22/0.44    inference(definition_unfolding,[],[f40,f45])).
% 0.22/0.44  fof(f45,plain,(
% 0.22/0.44    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)) )),
% 0.22/0.44    inference(definition_unfolding,[],[f41,f44])).
% 0.22/0.44  fof(f44,plain,(
% 0.22/0.44    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4)) )),
% 0.22/0.44    inference(definition_unfolding,[],[f42,f43])).
% 0.22/0.44  fof(f43,plain,(
% 0.22/0.44    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f11])).
% 0.22/0.44  fof(f11,axiom,(
% 0.22/0.44    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 0.22/0.44  fof(f42,plain,(
% 0.22/0.44    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f10])).
% 0.22/0.44  fof(f10,axiom,(
% 0.22/0.44    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 0.22/0.44  fof(f41,plain,(
% 0.22/0.44    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f9])).
% 0.22/0.44  fof(f9,axiom,(
% 0.22/0.44    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.22/0.44  fof(f40,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f8])).
% 0.22/0.44  fof(f8,axiom,(
% 0.22/0.44    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.44  fof(f36,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f7])).
% 0.22/0.44  fof(f7,axiom,(
% 0.22/0.44    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.44  fof(f35,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f12])).
% 0.22/0.44  fof(f12,axiom,(
% 0.22/0.44    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.22/0.44  fof(f38,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f2])).
% 0.22/0.44  fof(f2,axiom,(
% 0.22/0.44    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.22/0.44  fof(f30,plain,(
% 0.22/0.44    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f4])).
% 0.22/0.44  fof(f4,axiom,(
% 0.22/0.44    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).
% 0.22/0.44  fof(f92,plain,(
% 0.22/0.44    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 0.22/0.44    inference(forward_demodulation,[],[f91,f32])).
% 0.22/0.44  fof(f32,plain,(
% 0.22/0.44    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.44    inference(cnf_transformation,[],[f5])).
% 0.22/0.44  fof(f5,axiom,(
% 0.22/0.44    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 0.22/0.44  fof(f91,plain,(
% 0.22/0.44    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,X0)) )),
% 0.22/0.44    inference(forward_demodulation,[],[f90,f51])).
% 0.22/0.44  fof(f90,plain,(
% 0.22/0.44    ( ! [X0] : (k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k1_setfam_1(k5_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)))) = k5_xboole_0(k1_xboole_0,X0)) )),
% 0.22/0.44    inference(forward_demodulation,[],[f86,f32])).
% 0.22/0.44  fof(f86,plain,(
% 0.22/0.44    ( ! [X0] : (k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k1_setfam_1(k5_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k1_xboole_0))) )),
% 0.22/0.44    inference(superposition,[],[f53,f52])).
% 0.22/0.44  fof(f52,plain,(
% 0.22/0.44    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,k1_xboole_0))) )),
% 0.22/0.44    inference(definition_unfolding,[],[f31,f48])).
% 0.22/0.44  fof(f31,plain,(
% 0.22/0.44    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f3])).
% 0.22/0.44  fof(f3,axiom,(
% 0.22/0.44    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 0.22/0.44  fof(f53,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k5_enumset1(X1,X1,X1,X1,X1,X1,X0)))) = k5_xboole_0(X1,k5_xboole_0(X0,k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))))) )),
% 0.22/0.44    inference(definition_unfolding,[],[f34,f50,f50])).
% 0.22/0.44  fof(f50,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k5_enumset1(X1,X1,X1,X1,X1,X1,X0))))) )),
% 0.22/0.44    inference(definition_unfolding,[],[f37,f49])).
% 0.22/0.44  fof(f37,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f6])).
% 0.22/0.44  fof(f6,axiom,(
% 0.22/0.44    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.22/0.44  fof(f34,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f1])).
% 0.22/0.44  fof(f1,axiom,(
% 0.22/0.44    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.22/0.44  fof(f102,plain,(
% 0.22/0.44    ( ! [X0] : (k10_relat_1(k1_xboole_0,X0) = k10_relat_1(k1_xboole_0,k1_setfam_1(k5_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)))) ) | (~spl1_4 | ~spl1_5)),
% 0.22/0.44    inference(forward_demodulation,[],[f96,f73])).
% 0.22/0.44  fof(f96,plain,(
% 0.22/0.44    ( ! [X0] : (k10_relat_1(k1_xboole_0,X0) = k10_relat_1(k1_xboole_0,k1_setfam_1(k5_enumset1(k2_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0),X0)))) ) | ~spl1_5),
% 0.22/0.44    inference(unit_resulting_resolution,[],[f81,f54])).
% 0.22/0.44  fof(f54,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~v1_relat_1(X1) | k10_relat_1(X1,X0) = k10_relat_1(X1,k1_setfam_1(k5_enumset1(k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),X0)))) )),
% 0.22/0.44    inference(definition_unfolding,[],[f39,f48])).
% 0.22/0.44  fof(f39,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f22])).
% 0.22/0.44  fof(f22,plain,(
% 0.22/0.44    ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.44    inference(ennf_transformation,[],[f14])).
% 0.22/0.44  fof(f14,axiom,(
% 0.22/0.44    ! [X0,X1] : (v1_relat_1(X1) => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).
% 0.22/0.44  fof(f58,plain,(
% 0.22/0.44    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0) | spl1_1),
% 0.22/0.44    inference(avatar_component_clause,[],[f56])).
% 0.22/0.44  fof(f56,plain,(
% 0.22/0.44    spl1_1 <=> k1_xboole_0 = k10_relat_1(k1_xboole_0,sK0)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.22/0.44  fof(f82,plain,(
% 0.22/0.44    spl1_5 | ~spl1_2),
% 0.22/0.44    inference(avatar_split_clause,[],[f75,f61,f79])).
% 0.22/0.44  fof(f61,plain,(
% 0.22/0.44    spl1_2 <=> k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.22/0.44  fof(f75,plain,(
% 0.22/0.44    v1_relat_1(k1_xboole_0) | ~spl1_2),
% 0.22/0.44    inference(superposition,[],[f29,f63])).
% 0.22/0.44  fof(f63,plain,(
% 0.22/0.44    k1_xboole_0 = k6_relat_1(k1_xboole_0) | ~spl1_2),
% 0.22/0.44    inference(avatar_component_clause,[],[f61])).
% 0.22/0.44  fof(f29,plain,(
% 0.22/0.44    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f13])).
% 0.22/0.44  fof(f13,axiom,(
% 0.22/0.44    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.22/0.44  fof(f74,plain,(
% 0.22/0.44    spl1_4),
% 0.22/0.44    inference(avatar_split_clause,[],[f28,f71])).
% 0.22/0.44  fof(f28,plain,(
% 0.22/0.44    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.22/0.44    inference(cnf_transformation,[],[f16])).
% 0.22/0.44  fof(f16,axiom,(
% 0.22/0.44    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.22/0.44  fof(f69,plain,(
% 0.22/0.44    spl1_3),
% 0.22/0.44    inference(avatar_split_clause,[],[f27,f66])).
% 0.22/0.44  fof(f27,plain,(
% 0.22/0.44    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.44    inference(cnf_transformation,[],[f16])).
% 0.22/0.44  fof(f64,plain,(
% 0.22/0.44    spl1_2),
% 0.22/0.44    inference(avatar_split_clause,[],[f26,f61])).
% 0.22/0.44  fof(f26,plain,(
% 0.22/0.44    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.22/0.44    inference(cnf_transformation,[],[f17])).
% 0.22/0.44  fof(f17,axiom,(
% 0.22/0.44    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).
% 0.22/0.44  fof(f59,plain,(
% 0.22/0.44    ~spl1_1),
% 0.22/0.44    inference(avatar_split_clause,[],[f25,f56])).
% 0.22/0.44  fof(f25,plain,(
% 0.22/0.44    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0)),
% 0.22/0.44    inference(cnf_transformation,[],[f24])).
% 0.22/0.44  fof(f24,plain,(
% 0.22/0.44    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0)),
% 0.22/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f23])).
% 0.22/0.44  fof(f23,plain,(
% 0.22/0.44    ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0) => k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0)),
% 0.22/0.44    introduced(choice_axiom,[])).
% 0.22/0.44  fof(f20,plain,(
% 0.22/0.44    ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0)),
% 0.22/0.44    inference(ennf_transformation,[],[f19])).
% 0.22/0.44  fof(f19,negated_conjecture,(
% 0.22/0.44    ~! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)),
% 0.22/0.44    inference(negated_conjecture,[],[f18])).
% 0.22/0.44  fof(f18,conjecture,(
% 0.22/0.44    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).
% 0.22/0.44  % SZS output end Proof for theBenchmark
% 0.22/0.44  % (31097)------------------------------
% 0.22/0.44  % (31097)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.44  % (31097)Termination reason: Refutation
% 0.22/0.44  
% 0.22/0.44  % (31097)Memory used [KB]: 10618
% 0.22/0.44  % (31097)Time elapsed: 0.038 s
% 0.22/0.44  % (31097)------------------------------
% 0.22/0.44  % (31097)------------------------------
% 0.22/0.45  % (31081)Success in time 0.08 s
%------------------------------------------------------------------------------
