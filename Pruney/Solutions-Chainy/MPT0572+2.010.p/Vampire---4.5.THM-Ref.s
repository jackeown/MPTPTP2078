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
% DateTime   : Thu Dec  3 12:50:40 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 387 expanded)
%              Number of leaves         :   21 ( 132 expanded)
%              Depth                    :   14
%              Number of atoms          :  133 ( 462 expanded)
%              Number of equality atoms :   33 ( 317 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f158,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f135,f145,f147,f153,f155,f157])).

fof(f157,plain,(
    spl3_5 ),
    inference(avatar_contradiction_clause,[],[f156])).

fof(f156,plain,
    ( $false
    | spl3_5 ),
    inference(resolution,[],[f152,f93])).

fof(f93,plain,(
    ! [X4,X3] : r1_tarski(k4_xboole_0(X4,k4_xboole_0(X4,X3)),X3) ),
    inference(forward_demodulation,[],[f86,f49])).

fof(f49,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f31,f45])).

fof(f45,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f29,f44])).

fof(f44,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f30,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f33,f42])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f36,f41])).

fof(f41,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f37,f40])).

fof(f40,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f38,f39])).

fof(f39,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f38,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f37,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f36,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f33,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f30,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f29,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f31,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f86,plain,(
    ! [X4,X3] : r1_tarski(k1_setfam_1(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X3)),X3) ),
    inference(superposition,[],[f57,f78])).

% (24075)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
fof(f78,plain,(
    ! [X4,X5] : k4_xboole_0(X4,k4_xboole_0(X4,X5)) = k1_setfam_1(k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X4)) ),
    inference(superposition,[],[f48,f49])).

fof(f48,plain,(
    ! [X0,X1] : k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)) ),
    inference(definition_unfolding,[],[f28,f45,f45])).

fof(f28,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f57,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(backward_demodulation,[],[f47,f49])).

fof(f47,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f27,f45])).

fof(f27,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f152,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1)
    | spl3_5 ),
    inference(avatar_component_clause,[],[f150])).

fof(f150,plain,
    ( spl3_5
  <=> r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f155,plain,(
    spl3_3 ),
    inference(avatar_contradiction_clause,[],[f154])).

fof(f154,plain,
    ( $false
    | spl3_3 ),
    inference(resolution,[],[f140,f57])).

fof(f140,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f138])).

fof(f138,plain,
    ( spl3_3
  <=> r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f153,plain,
    ( ~ spl3_5
    | ~ spl3_4
    | spl3_2 ),
    inference(avatar_split_clause,[],[f148,f132,f142,f150])).

fof(f142,plain,
    ( spl3_4
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f132,plain,
    ( spl3_2
  <=> r1_tarski(k10_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k10_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f148,plain,
    ( ~ v1_relat_1(sK2)
    | ~ r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1)
    | spl3_2 ),
    inference(resolution,[],[f134,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f54,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f54,plain,(
    ! [X4,X5,X3] :
      ( r1_tarski(k10_relat_1(X3,X4),k10_relat_1(X3,k2_xboole_0(X4,X5)))
      | ~ v1_relat_1(X3) ) ),
    inference(superposition,[],[f26,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_relat_1)).

fof(f26,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f134,plain,
    ( ~ r1_tarski(k10_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k10_relat_1(sK2,sK1))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f132])).

fof(f147,plain,(
    spl3_4 ),
    inference(avatar_contradiction_clause,[],[f146])).

fof(f146,plain,
    ( $false
    | spl3_4 ),
    inference(resolution,[],[f144,f24])).

fof(f24,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ~ r1_tarski(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f22])).

fof(f22,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k10_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k10_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => r1_tarski(k10_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k10_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t176_relat_1)).

fof(f144,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f142])).

fof(f145,plain,
    ( ~ spl3_3
    | ~ spl3_4
    | spl3_1 ),
    inference(avatar_split_clause,[],[f136,f128,f142,f138])).

fof(f128,plain,
    ( spl3_1
  <=> r1_tarski(k10_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k10_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f136,plain,
    ( ~ v1_relat_1(sK2)
    | ~ r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0)
    | spl3_1 ),
    inference(resolution,[],[f130,f55])).

fof(f130,plain,
    ( ~ r1_tarski(k10_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k10_relat_1(sK2,sK0))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f128])).

fof(f135,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f126,f132,f128])).

fof(f126,plain,
    ( ~ r1_tarski(k10_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k10_relat_1(sK2,sK1))
    | ~ r1_tarski(k10_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k10_relat_1(sK2,sK0)) ),
    inference(resolution,[],[f101,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(forward_demodulation,[],[f50,f49])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f35,f45])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

fof(f101,plain,(
    ~ r1_tarski(k10_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k10_relat_1(sK2,sK0),k4_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))) ),
    inference(forward_demodulation,[],[f100,f49])).

fof(f100,plain,(
    ~ r1_tarski(k10_relat_1(sK2,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k4_xboole_0(k10_relat_1(sK2,sK0),k4_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))) ),
    inference(forward_demodulation,[],[f46,f49])).

fof(f46,plain,(
    ~ r1_tarski(k10_relat_1(sK2,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k1_setfam_1(k6_enumset1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))) ),
    inference(definition_unfolding,[],[f25,f45,f45])).

fof(f25,plain,(
    ~ r1_tarski(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f23])).
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
% 0.15/0.35  % DateTime   : Tue Dec  1 18:47:06 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.23/0.47  % (24074)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.23/0.48  % (24074)Refutation found. Thanks to Tanya!
% 0.23/0.48  % SZS status Theorem for theBenchmark
% 0.23/0.48  % (24081)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.23/0.48  % (24073)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.23/0.48  % (24071)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.23/0.48  % (24082)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.23/0.48  % SZS output start Proof for theBenchmark
% 0.23/0.48  fof(f158,plain,(
% 0.23/0.48    $false),
% 0.23/0.48    inference(avatar_sat_refutation,[],[f135,f145,f147,f153,f155,f157])).
% 0.23/0.48  fof(f157,plain,(
% 0.23/0.48    spl3_5),
% 0.23/0.48    inference(avatar_contradiction_clause,[],[f156])).
% 0.23/0.48  fof(f156,plain,(
% 0.23/0.48    $false | spl3_5),
% 0.23/0.48    inference(resolution,[],[f152,f93])).
% 0.23/0.48  fof(f93,plain,(
% 0.23/0.48    ( ! [X4,X3] : (r1_tarski(k4_xboole_0(X4,k4_xboole_0(X4,X3)),X3)) )),
% 0.23/0.48    inference(forward_demodulation,[],[f86,f49])).
% 0.23/0.48  fof(f49,plain,(
% 0.23/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 0.23/0.48    inference(definition_unfolding,[],[f31,f45])).
% 0.23/0.48  fof(f45,plain,(
% 0.23/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 0.23/0.48    inference(definition_unfolding,[],[f29,f44])).
% 0.23/0.48  fof(f44,plain,(
% 0.23/0.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.23/0.48    inference(definition_unfolding,[],[f30,f43])).
% 0.23/0.48  fof(f43,plain,(
% 0.23/0.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.23/0.48    inference(definition_unfolding,[],[f33,f42])).
% 0.23/0.48  fof(f42,plain,(
% 0.23/0.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.23/0.48    inference(definition_unfolding,[],[f36,f41])).
% 0.23/0.48  fof(f41,plain,(
% 0.23/0.48    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.23/0.48    inference(definition_unfolding,[],[f37,f40])).
% 0.23/0.48  fof(f40,plain,(
% 0.23/0.48    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.23/0.48    inference(definition_unfolding,[],[f38,f39])).
% 0.23/0.48  fof(f39,plain,(
% 0.23/0.48    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.23/0.48    inference(cnf_transformation,[],[f12])).
% 0.23/0.48  fof(f12,axiom,(
% 0.23/0.48    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.23/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 0.23/0.48  fof(f38,plain,(
% 0.23/0.48    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.23/0.48    inference(cnf_transformation,[],[f11])).
% 0.23/0.48  fof(f11,axiom,(
% 0.23/0.48    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.23/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 0.23/0.48  fof(f37,plain,(
% 0.23/0.48    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.23/0.48    inference(cnf_transformation,[],[f10])).
% 0.23/0.48  fof(f10,axiom,(
% 0.23/0.48    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.23/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 0.23/0.48  fof(f36,plain,(
% 0.23/0.48    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.23/0.48    inference(cnf_transformation,[],[f9])).
% 0.23/0.48  fof(f9,axiom,(
% 0.23/0.48    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.23/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.23/0.48  fof(f33,plain,(
% 0.23/0.48    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.23/0.48    inference(cnf_transformation,[],[f8])).
% 0.23/0.48  fof(f8,axiom,(
% 0.23/0.48    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.23/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.23/0.48  fof(f30,plain,(
% 0.23/0.48    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.23/0.48    inference(cnf_transformation,[],[f7])).
% 0.23/0.48  fof(f7,axiom,(
% 0.23/0.48    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.23/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.23/0.48  fof(f29,plain,(
% 0.23/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.23/0.48    inference(cnf_transformation,[],[f13])).
% 0.23/0.48  fof(f13,axiom,(
% 0.23/0.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.23/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.23/0.48  fof(f31,plain,(
% 0.23/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.23/0.48    inference(cnf_transformation,[],[f5])).
% 0.23/0.48  fof(f5,axiom,(
% 0.23/0.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.23/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.23/0.48  fof(f86,plain,(
% 0.23/0.48    ( ! [X4,X3] : (r1_tarski(k1_setfam_1(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X3)),X3)) )),
% 0.23/0.48    inference(superposition,[],[f57,f78])).
% 0.23/0.48  % (24075)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.23/0.49  fof(f78,plain,(
% 0.23/0.49    ( ! [X4,X5] : (k4_xboole_0(X4,k4_xboole_0(X4,X5)) = k1_setfam_1(k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X4))) )),
% 0.23/0.49    inference(superposition,[],[f48,f49])).
% 0.23/0.49  fof(f48,plain,(
% 0.23/0.49    ( ! [X0,X1] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))) )),
% 0.23/0.49    inference(definition_unfolding,[],[f28,f45,f45])).
% 0.23/0.49  fof(f28,plain,(
% 0.23/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.23/0.49    inference(cnf_transformation,[],[f1])).
% 0.23/0.49  fof(f1,axiom,(
% 0.23/0.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.23/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.23/0.49  fof(f57,plain,(
% 0.23/0.49    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) )),
% 0.23/0.49    inference(backward_demodulation,[],[f47,f49])).
% 0.23/0.49  fof(f47,plain,(
% 0.23/0.49    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0)) )),
% 0.23/0.49    inference(definition_unfolding,[],[f27,f45])).
% 0.23/0.49  fof(f27,plain,(
% 0.23/0.49    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.23/0.49    inference(cnf_transformation,[],[f3])).
% 0.23/0.49  fof(f3,axiom,(
% 0.23/0.49    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.23/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.23/0.49  fof(f152,plain,(
% 0.23/0.49    ~r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1) | spl3_5),
% 0.23/0.49    inference(avatar_component_clause,[],[f150])).
% 0.23/0.49  fof(f150,plain,(
% 0.23/0.49    spl3_5 <=> r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1)),
% 0.23/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.23/0.49  fof(f155,plain,(
% 0.23/0.49    spl3_3),
% 0.23/0.49    inference(avatar_contradiction_clause,[],[f154])).
% 0.23/0.49  fof(f154,plain,(
% 0.23/0.49    $false | spl3_3),
% 0.23/0.49    inference(resolution,[],[f140,f57])).
% 0.23/0.49  fof(f140,plain,(
% 0.23/0.49    ~r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0) | spl3_3),
% 0.23/0.49    inference(avatar_component_clause,[],[f138])).
% 0.23/0.49  fof(f138,plain,(
% 0.23/0.49    spl3_3 <=> r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0)),
% 0.23/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.23/0.49  fof(f153,plain,(
% 0.23/0.49    ~spl3_5 | ~spl3_4 | spl3_2),
% 0.23/0.49    inference(avatar_split_clause,[],[f148,f132,f142,f150])).
% 0.23/0.49  fof(f142,plain,(
% 0.23/0.49    spl3_4 <=> v1_relat_1(sK2)),
% 0.23/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.23/0.49  fof(f132,plain,(
% 0.23/0.49    spl3_2 <=> r1_tarski(k10_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k10_relat_1(sK2,sK1))),
% 0.23/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.23/0.49  fof(f148,plain,(
% 0.23/0.49    ~v1_relat_1(sK2) | ~r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1) | spl3_2),
% 0.23/0.49    inference(resolution,[],[f134,f55])).
% 0.23/0.49  fof(f55,plain,(
% 0.23/0.49    ( ! [X2,X0,X1] : (r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_relat_1(X2) | ~r1_tarski(X0,X1)) )),
% 0.23/0.49    inference(superposition,[],[f54,f32])).
% 0.23/0.49  fof(f32,plain,(
% 0.23/0.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 0.23/0.49    inference(cnf_transformation,[],[f18])).
% 0.23/0.49  fof(f18,plain,(
% 0.23/0.49    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.23/0.49    inference(ennf_transformation,[],[f2])).
% 0.23/0.49  fof(f2,axiom,(
% 0.23/0.49    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.23/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.23/0.49  fof(f54,plain,(
% 0.23/0.49    ( ! [X4,X5,X3] : (r1_tarski(k10_relat_1(X3,X4),k10_relat_1(X3,k2_xboole_0(X4,X5))) | ~v1_relat_1(X3)) )),
% 0.23/0.49    inference(superposition,[],[f26,f34])).
% 0.23/0.49  fof(f34,plain,(
% 0.23/0.49    ( ! [X2,X0,X1] : (k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 0.23/0.49    inference(cnf_transformation,[],[f19])).
% 0.23/0.49  fof(f19,plain,(
% 0.23/0.49    ! [X0,X1,X2] : (k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 0.23/0.49    inference(ennf_transformation,[],[f14])).
% 0.23/0.49  fof(f14,axiom,(
% 0.23/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))),
% 0.23/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_relat_1)).
% 0.23/0.49  fof(f26,plain,(
% 0.23/0.49    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.23/0.49    inference(cnf_transformation,[],[f6])).
% 0.23/0.49  fof(f6,axiom,(
% 0.23/0.49    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.23/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.23/0.49  fof(f134,plain,(
% 0.23/0.49    ~r1_tarski(k10_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k10_relat_1(sK2,sK1)) | spl3_2),
% 0.23/0.49    inference(avatar_component_clause,[],[f132])).
% 0.23/0.49  fof(f147,plain,(
% 0.23/0.49    spl3_4),
% 0.23/0.49    inference(avatar_contradiction_clause,[],[f146])).
% 0.23/0.49  fof(f146,plain,(
% 0.23/0.49    $false | spl3_4),
% 0.23/0.49    inference(resolution,[],[f144,f24])).
% 0.23/0.49  fof(f24,plain,(
% 0.23/0.49    v1_relat_1(sK2)),
% 0.23/0.49    inference(cnf_transformation,[],[f23])).
% 0.23/0.49  fof(f23,plain,(
% 0.23/0.49    ~r1_tarski(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))) & v1_relat_1(sK2)),
% 0.23/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f22])).
% 0.23/0.49  fof(f22,plain,(
% 0.23/0.49    ? [X0,X1,X2] : (~r1_tarski(k10_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) & v1_relat_1(X2)) => (~r1_tarski(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))) & v1_relat_1(sK2))),
% 0.23/0.49    introduced(choice_axiom,[])).
% 0.23/0.49  fof(f17,plain,(
% 0.23/0.49    ? [X0,X1,X2] : (~r1_tarski(k10_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) & v1_relat_1(X2))),
% 0.23/0.49    inference(ennf_transformation,[],[f16])).
% 0.23/0.49  fof(f16,negated_conjecture,(
% 0.23/0.49    ~! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k10_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))))),
% 0.23/0.49    inference(negated_conjecture,[],[f15])).
% 0.23/0.49  fof(f15,conjecture,(
% 0.23/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k10_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))))),
% 0.23/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t176_relat_1)).
% 0.23/0.49  fof(f144,plain,(
% 0.23/0.49    ~v1_relat_1(sK2) | spl3_4),
% 0.23/0.49    inference(avatar_component_clause,[],[f142])).
% 0.23/0.49  fof(f145,plain,(
% 0.23/0.49    ~spl3_3 | ~spl3_4 | spl3_1),
% 0.23/0.49    inference(avatar_split_clause,[],[f136,f128,f142,f138])).
% 0.23/0.49  fof(f128,plain,(
% 0.23/0.49    spl3_1 <=> r1_tarski(k10_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k10_relat_1(sK2,sK0))),
% 0.23/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.23/0.49  fof(f136,plain,(
% 0.23/0.49    ~v1_relat_1(sK2) | ~r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0) | spl3_1),
% 0.23/0.49    inference(resolution,[],[f130,f55])).
% 0.23/0.49  fof(f130,plain,(
% 0.23/0.49    ~r1_tarski(k10_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k10_relat_1(sK2,sK0)) | spl3_1),
% 0.23/0.49    inference(avatar_component_clause,[],[f128])).
% 0.23/0.49  fof(f135,plain,(
% 0.23/0.49    ~spl3_1 | ~spl3_2),
% 0.23/0.49    inference(avatar_split_clause,[],[f126,f132,f128])).
% 0.23/0.49  fof(f126,plain,(
% 0.23/0.49    ~r1_tarski(k10_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k10_relat_1(sK2,sK1)) | ~r1_tarski(k10_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k10_relat_1(sK2,sK0))),
% 0.23/0.49    inference(resolution,[],[f101,f60])).
% 0.23/0.49  fof(f60,plain,(
% 0.23/0.49    ( ! [X2,X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.23/0.49    inference(forward_demodulation,[],[f50,f49])).
% 0.23/0.49  fof(f50,plain,(
% 0.23/0.49    ( ! [X2,X0,X1] : (r1_tarski(X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.23/0.49    inference(definition_unfolding,[],[f35,f45])).
% 0.23/0.49  fof(f35,plain,(
% 0.23/0.49    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.23/0.49    inference(cnf_transformation,[],[f21])).
% 0.23/0.49  fof(f21,plain,(
% 0.23/0.49    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.23/0.49    inference(flattening,[],[f20])).
% 0.23/0.49  fof(f20,plain,(
% 0.23/0.49    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.23/0.49    inference(ennf_transformation,[],[f4])).
% 0.23/0.49  fof(f4,axiom,(
% 0.23/0.49    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.23/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).
% 0.23/0.49  fof(f101,plain,(
% 0.23/0.49    ~r1_tarski(k10_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k10_relat_1(sK2,sK0),k4_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))))),
% 0.23/0.49    inference(forward_demodulation,[],[f100,f49])).
% 0.23/0.49  fof(f100,plain,(
% 0.23/0.49    ~r1_tarski(k10_relat_1(sK2,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k4_xboole_0(k10_relat_1(sK2,sK0),k4_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))))),
% 0.23/0.49    inference(forward_demodulation,[],[f46,f49])).
% 0.23/0.49  fof(f46,plain,(
% 0.23/0.49    ~r1_tarski(k10_relat_1(sK2,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k1_setfam_1(k6_enumset1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))))),
% 0.23/0.49    inference(definition_unfolding,[],[f25,f45,f45])).
% 0.23/0.49  fof(f25,plain,(
% 0.23/0.49    ~r1_tarski(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))),
% 0.23/0.49    inference(cnf_transformation,[],[f23])).
% 0.23/0.49  % SZS output end Proof for theBenchmark
% 0.23/0.49  % (24074)------------------------------
% 0.23/0.49  % (24074)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.49  % (24074)Termination reason: Refutation
% 0.23/0.49  
% 0.23/0.49  % (24074)Memory used [KB]: 6140
% 0.23/0.49  % (24074)Time elapsed: 0.058 s
% 0.23/0.49  % (24074)------------------------------
% 0.23/0.49  % (24074)------------------------------
% 0.23/0.49  % (24080)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.23/0.49  % (24069)Success in time 0.121 s
%------------------------------------------------------------------------------
