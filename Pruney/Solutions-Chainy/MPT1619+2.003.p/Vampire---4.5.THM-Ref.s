%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:48 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 207 expanded)
%              Number of leaves         :   31 (  70 expanded)
%              Depth                    :   13
%              Number of atoms          :  219 ( 341 expanded)
%              Number of equality atoms :   58 ( 139 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f147,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f92,f126,f128,f130,f133,f137,f142,f146])).

fof(f146,plain,(
    ~ spl2_1 ),
    inference(avatar_contradiction_clause,[],[f143])).

fof(f143,plain,
    ( $false
    | ~ spl2_1 ),
    inference(resolution,[],[f87,f43])).

fof(f43,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,
    ( g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,sK0)
    & l1_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f38])).

fof(f38,plain,
    ( ? [X0] :
        ( g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,X0)
        & l1_orders_2(X0) )
   => ( g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,sK0)
      & l1_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ? [X0] :
      ( g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,X0)
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k6_yellow_1(k1_xboole_0,X0) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f24,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k6_yellow_1(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_yellow_1)).

fof(f87,plain,
    ( ! [X0] : ~ l1_orders_2(X0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl2_1
  <=> ! [X0] : ~ l1_orders_2(X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f142,plain,(
    ~ spl2_7 ),
    inference(avatar_contradiction_clause,[],[f141])).

fof(f141,plain,
    ( $false
    | ~ spl2_7 ),
    inference(trivial_inequality_removal,[],[f140])).

fof(f140,plain,
    ( k6_yellow_1(k1_xboole_0,sK0) != k6_yellow_1(k1_xboole_0,sK0)
    | ~ spl2_7 ),
    inference(superposition,[],[f76,f125])).

fof(f125,plain,
    ( k6_yellow_1(k1_xboole_0,sK0) = g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_relat_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)))
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl2_7
  <=> k6_yellow_1(k1_xboole_0,sK0) = g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_relat_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f76,plain,(
    k6_yellow_1(k1_xboole_0,sK0) != g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_relat_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) ),
    inference(definition_unfolding,[],[f44,f75,f51,f75])).

fof(f51,plain,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f75,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f52,f74])).

fof(f74,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f59,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f64,f72])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f65,f71])).

fof(f71,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f66,f70])).

fof(f70,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f67,f68])).

fof(f68,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f67,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

% (22005)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% (22004)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% (22010)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
fof(f66,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f8])).

% (22016)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f65,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f64,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f59,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f52,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f44,plain,(
    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f137,plain,(
    spl2_6 ),
    inference(avatar_contradiction_clause,[],[f136])).

fof(f136,plain,
    ( $false
    | spl2_6 ),
    inference(resolution,[],[f121,f80])).

fof(f80,plain,(
    v1_partfun1(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f77,f46])).

fof(f46,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

fof(f77,plain,(
    ! [X0] : v1_partfun1(k6_relat_1(X0),X0) ),
    inference(definition_unfolding,[],[f53,f51])).

fof(f53,plain,(
    ! [X0] : v1_partfun1(k6_partfun1(X0),X0) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] : v1_partfun1(k6_partfun1(X0),X0) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f121,plain,
    ( ~ v1_partfun1(k1_xboole_0,k1_xboole_0)
    | spl2_6 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl2_6
  <=> v1_partfun1(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f133,plain,(
    spl2_5 ),
    inference(avatar_contradiction_clause,[],[f132])).

fof(f132,plain,
    ( $false
    | spl2_5 ),
    inference(resolution,[],[f131,f45])).

fof(f45,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f131,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl2_5 ),
    inference(resolution,[],[f117,f55])).

fof(f55,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f117,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl2_5 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl2_5
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f130,plain,(
    spl2_4 ),
    inference(avatar_contradiction_clause,[],[f129])).

fof(f129,plain,
    ( $false
    | spl2_4 ),
    inference(resolution,[],[f113,f45])).

fof(f113,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl2_4 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl2_4
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f128,plain,(
    spl2_3 ),
    inference(avatar_contradiction_clause,[],[f127])).

fof(f127,plain,
    ( $false
    | spl2_3 ),
    inference(resolution,[],[f109,f49])).

fof(f49,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f109,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | spl2_3 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl2_3
  <=> r1_tarski(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f126,plain,
    ( ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_2
    | ~ spl2_6
    | spl2_7 ),
    inference(avatar_split_clause,[],[f105,f123,f119,f89,f115,f111,f107])).

fof(f89,plain,
    ( spl2_2
  <=> v1_yellow_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f105,plain,
    ( k6_yellow_1(k1_xboole_0,sK0) = g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_relat_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)))
    | ~ v1_partfun1(k1_xboole_0,k1_xboole_0)
    | ~ v1_yellow_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_xboole_0(k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f104,f100])).

fof(f100,plain,(
    k6_yellow_1(k1_xboole_0,sK0) = k5_yellow_1(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f98,f82])).

fof(f82,plain,(
    ! [X0] : k1_xboole_0 = k2_funcop_1(k1_xboole_0,X0) ),
    inference(resolution,[],[f56,f50])).

fof(f50,plain,(
    ! [X0] : v1_xboole_0(k2_funcop_1(k1_xboole_0,X0)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] : v1_xboole_0(k2_funcop_1(k1_xboole_0,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_funcop_1)).

fof(f56,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f98,plain,(
    ! [X0] : k6_yellow_1(X0,sK0) = k5_yellow_1(X0,k2_funcop_1(X0,sK0)) ),
    inference(resolution,[],[f79,f43])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X1)
      | k6_yellow_1(X0,X1) = k5_yellow_1(X0,k2_funcop_1(X0,X1)) ) ),
    inference(definition_unfolding,[],[f63,f58])).

fof(f58,plain,(
    ! [X0,X1] : k7_funcop_1(X0,X1) = k2_funcop_1(X0,X1) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] : k7_funcop_1(X0,X1) = k2_funcop_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_funcop_1)).

fof(f63,plain,(
    ! [X0,X1] :
      ( k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1))
      | ~ l1_orders_2(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1))
      | ~ l1_orders_2(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X1)
     => k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_yellow_1)).

fof(f104,plain,
    ( ~ v1_partfun1(k1_xboole_0,k1_xboole_0)
    | g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_relat_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0)
    | ~ v1_yellow_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_xboole_0(k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[],[f103,f95])).

fof(f95,plain,(
    ! [X0] :
      ( v4_relat_1(k1_xboole_0,X0)
      | ~ r1_tarski(k1_xboole_0,X0) ) ),
    inference(forward_demodulation,[],[f94,f47])).

fof(f47,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f94,plain,(
    ! [X0] :
      ( v4_relat_1(k1_xboole_0,X0)
      | ~ r1_tarski(k1_relat_1(k1_xboole_0),X0) ) ),
    inference(resolution,[],[f93,f45])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | v4_relat_1(X0,X1)
      | ~ r1_tarski(k1_relat_1(X0),X1) ) ),
    inference(resolution,[],[f61,f55])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | v4_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f103,plain,(
    ! [X0] :
      ( ~ v4_relat_1(X0,k1_xboole_0)
      | ~ v1_partfun1(X0,k1_xboole_0)
      | k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_relat_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)))
      | ~ v1_yellow_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f78,f54])).

fof(f54,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_funct_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_1)).

fof(f78,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_yellow_1(X0)
      | ~ v1_partfun1(X0,k1_xboole_0)
      | k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_relat_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)))
      | ~ v4_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f57,f75,f51,f75])).

fof(f57,plain,(
    ! [X0] :
      ( k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))
      | ~ v1_yellow_1(X0)
      | ~ v1_partfun1(X0,k1_xboole_0)
      | ~ v1_funct_1(X0)
      | ~ v4_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))
      | ~ v1_yellow_1(X0)
      | ~ v1_partfun1(X0,k1_xboole_0)
      | ~ v1_funct_1(X0)
      | ~ v4_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))
      | ~ v1_yellow_1(X0)
      | ~ v1_partfun1(X0,k1_xboole_0)
      | ~ v1_funct_1(X0)
      | ~ v4_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( ( v1_yellow_1(X0)
        & v1_partfun1(X0,k1_xboole_0)
        & v1_funct_1(X0)
        & v4_relat_1(X0,k1_xboole_0)
        & v1_relat_1(X0) )
     => k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_yellow_1)).

fof(f92,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f84,f89,f86])).

fof(f84,plain,(
    ! [X0] :
      ( v1_yellow_1(k1_xboole_0)
      | ~ l1_orders_2(X0) ) ),
    inference(superposition,[],[f62,f82])).

fof(f62,plain,(
    ! [X0,X1] :
      ( v1_yellow_1(k2_funcop_1(X0,X1))
      | ~ l1_orders_2(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( v1_yellow_1(k2_funcop_1(X0,X1))
      | ~ l1_orders_2(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X1)
     => v1_yellow_1(k2_funcop_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_yellow_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:27:39 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.47  % (22003)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.47  % (22012)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.47  % (22012)Refutation not found, incomplete strategy% (22012)------------------------------
% 0.20/0.47  % (22012)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (22003)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f147,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(avatar_sat_refutation,[],[f92,f126,f128,f130,f133,f137,f142,f146])).
% 0.20/0.47  fof(f146,plain,(
% 0.20/0.47    ~spl2_1),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f143])).
% 0.20/0.47  fof(f143,plain,(
% 0.20/0.47    $false | ~spl2_1),
% 0.20/0.47    inference(resolution,[],[f87,f43])).
% 0.20/0.47  fof(f43,plain,(
% 0.20/0.47    l1_orders_2(sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f39])).
% 0.20/0.47  fof(f39,plain,(
% 0.20/0.47    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,sK0) & l1_orders_2(sK0)),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f38])).
% 0.20/0.47  fof(f38,plain,(
% 0.20/0.47    ? [X0] : (g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,X0) & l1_orders_2(X0)) => (g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,sK0) & l1_orders_2(sK0))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f29,plain,(
% 0.20/0.47    ? [X0] : (g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,X0) & l1_orders_2(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f25])).
% 0.20/0.47  fof(f25,negated_conjecture,(
% 0.20/0.47    ~! [X0] : (l1_orders_2(X0) => g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k6_yellow_1(k1_xboole_0,X0))),
% 0.20/0.47    inference(negated_conjecture,[],[f24])).
% 0.20/0.47  fof(f24,conjecture,(
% 0.20/0.47    ! [X0] : (l1_orders_2(X0) => g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k6_yellow_1(k1_xboole_0,X0))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_yellow_1)).
% 0.20/0.47  fof(f87,plain,(
% 0.20/0.47    ( ! [X0] : (~l1_orders_2(X0)) ) | ~spl2_1),
% 0.20/0.47    inference(avatar_component_clause,[],[f86])).
% 0.20/0.47  fof(f86,plain,(
% 0.20/0.47    spl2_1 <=> ! [X0] : ~l1_orders_2(X0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.20/0.47  fof(f142,plain,(
% 0.20/0.47    ~spl2_7),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f141])).
% 0.20/0.47  fof(f141,plain,(
% 0.20/0.47    $false | ~spl2_7),
% 0.20/0.47    inference(trivial_inequality_removal,[],[f140])).
% 0.20/0.47  fof(f140,plain,(
% 0.20/0.47    k6_yellow_1(k1_xboole_0,sK0) != k6_yellow_1(k1_xboole_0,sK0) | ~spl2_7),
% 0.20/0.47    inference(superposition,[],[f76,f125])).
% 0.20/0.47  fof(f125,plain,(
% 0.20/0.47    k6_yellow_1(k1_xboole_0,sK0) = g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_relat_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) | ~spl2_7),
% 0.20/0.47    inference(avatar_component_clause,[],[f123])).
% 0.20/0.47  fof(f123,plain,(
% 0.20/0.47    spl2_7 <=> k6_yellow_1(k1_xboole_0,sK0) = g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_relat_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.20/0.47  fof(f76,plain,(
% 0.20/0.47    k6_yellow_1(k1_xboole_0,sK0) != g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_relat_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)))),
% 0.20/0.47    inference(definition_unfolding,[],[f44,f75,f51,f75])).
% 0.20/0.47  fof(f51,plain,(
% 0.20/0.47    ( ! [X0] : (k6_partfun1(X0) = k6_relat_1(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f17])).
% 0.20/0.47  fof(f17,axiom,(
% 0.20/0.47    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 0.20/0.47  fof(f75,plain,(
% 0.20/0.47    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 0.20/0.47    inference(definition_unfolding,[],[f52,f74])).
% 0.20/0.47  fof(f74,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.20/0.47    inference(definition_unfolding,[],[f59,f73])).
% 0.20/0.47  fof(f73,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.20/0.47    inference(definition_unfolding,[],[f64,f72])).
% 0.20/0.47  fof(f72,plain,(
% 0.20/0.47    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.20/0.47    inference(definition_unfolding,[],[f65,f71])).
% 0.20/0.47  fof(f71,plain,(
% 0.20/0.47    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.20/0.47    inference(definition_unfolding,[],[f66,f70])).
% 0.20/0.47  fof(f70,plain,(
% 0.20/0.47    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.20/0.47    inference(definition_unfolding,[],[f67,f68])).
% 0.20/0.47  fof(f68,plain,(
% 0.20/0.47    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f10])).
% 0.20/0.47  fof(f10,axiom,(
% 0.20/0.47    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 0.20/0.47  fof(f67,plain,(
% 0.20/0.47    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f9])).
% 0.20/0.47  fof(f9,axiom,(
% 0.20/0.47    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 0.20/0.47  % (22005)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.47  % (22004)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.48  % (22010)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.48  fof(f66,plain,(
% 0.20/0.48    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f8])).
% 0.20/0.48  % (22016)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.48  fof(f8,axiom,(
% 0.20/0.48    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 0.20/0.48  fof(f65,plain,(
% 0.20/0.48    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f7])).
% 0.20/0.48  fof(f7,axiom,(
% 0.20/0.48    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.20/0.48  fof(f64,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f6])).
% 0.20/0.48  fof(f6,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.48  fof(f59,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f5])).
% 0.20/0.48  fof(f5,axiom,(
% 0.20/0.48    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.48  fof(f52,plain,(
% 0.20/0.48    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f4])).
% 0.20/0.48  fof(f4,axiom,(
% 0.20/0.48    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.48  fof(f44,plain,(
% 0.20/0.48    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f39])).
% 0.20/0.48  fof(f137,plain,(
% 0.20/0.48    spl2_6),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f136])).
% 0.20/0.48  fof(f136,plain,(
% 0.20/0.48    $false | spl2_6),
% 0.20/0.48    inference(resolution,[],[f121,f80])).
% 0.20/0.48  fof(f80,plain,(
% 0.20/0.48    v1_partfun1(k1_xboole_0,k1_xboole_0)),
% 0.20/0.48    inference(superposition,[],[f77,f46])).
% 0.20/0.48  fof(f46,plain,(
% 0.20/0.48    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.20/0.48    inference(cnf_transformation,[],[f14])).
% 0.20/0.48  fof(f14,axiom,(
% 0.20/0.48    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).
% 0.20/0.48  fof(f77,plain,(
% 0.20/0.48    ( ! [X0] : (v1_partfun1(k6_relat_1(X0),X0)) )),
% 0.20/0.48    inference(definition_unfolding,[],[f53,f51])).
% 0.20/0.48  fof(f53,plain,(
% 0.20/0.48    ( ! [X0] : (v1_partfun1(k6_partfun1(X0),X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f28])).
% 0.20/0.48  fof(f28,plain,(
% 0.20/0.48    ! [X0] : v1_partfun1(k6_partfun1(X0),X0)),
% 0.20/0.48    inference(pure_predicate_removal,[],[f16])).
% 0.20/0.48  fof(f16,axiom,(
% 0.20/0.48    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 0.20/0.48  fof(f121,plain,(
% 0.20/0.48    ~v1_partfun1(k1_xboole_0,k1_xboole_0) | spl2_6),
% 0.20/0.48    inference(avatar_component_clause,[],[f119])).
% 0.20/0.48  fof(f119,plain,(
% 0.20/0.48    spl2_6 <=> v1_partfun1(k1_xboole_0,k1_xboole_0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.20/0.48  fof(f133,plain,(
% 0.20/0.48    spl2_5),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f132])).
% 0.20/0.48  fof(f132,plain,(
% 0.20/0.48    $false | spl2_5),
% 0.20/0.48    inference(resolution,[],[f131,f45])).
% 0.20/0.48  fof(f45,plain,(
% 0.20/0.48    v1_xboole_0(k1_xboole_0)),
% 0.20/0.48    inference(cnf_transformation,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    v1_xboole_0(k1_xboole_0)),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.48  fof(f131,plain,(
% 0.20/0.48    ~v1_xboole_0(k1_xboole_0) | spl2_5),
% 0.20/0.48    inference(resolution,[],[f117,f55])).
% 0.20/0.48  fof(f55,plain,(
% 0.20/0.48    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f31])).
% 0.20/0.48  fof(f31,plain,(
% 0.20/0.48    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f11])).
% 0.20/0.48  fof(f11,axiom,(
% 0.20/0.48    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).
% 0.20/0.48  fof(f117,plain,(
% 0.20/0.48    ~v1_relat_1(k1_xboole_0) | spl2_5),
% 0.20/0.48    inference(avatar_component_clause,[],[f115])).
% 0.20/0.48  fof(f115,plain,(
% 0.20/0.48    spl2_5 <=> v1_relat_1(k1_xboole_0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.20/0.48  fof(f130,plain,(
% 0.20/0.48    spl2_4),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f129])).
% 0.20/0.48  fof(f129,plain,(
% 0.20/0.48    $false | spl2_4),
% 0.20/0.48    inference(resolution,[],[f113,f45])).
% 0.20/0.48  fof(f113,plain,(
% 0.20/0.48    ~v1_xboole_0(k1_xboole_0) | spl2_4),
% 0.20/0.48    inference(avatar_component_clause,[],[f111])).
% 0.20/0.48  fof(f111,plain,(
% 0.20/0.48    spl2_4 <=> v1_xboole_0(k1_xboole_0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.20/0.48  fof(f128,plain,(
% 0.20/0.48    spl2_3),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f127])).
% 0.20/0.48  fof(f127,plain,(
% 0.20/0.48    $false | spl2_3),
% 0.20/0.48    inference(resolution,[],[f109,f49])).
% 0.20/0.48  fof(f49,plain,(
% 0.20/0.48    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f3])).
% 0.20/0.48  fof(f3,axiom,(
% 0.20/0.48    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.20/0.48  fof(f109,plain,(
% 0.20/0.48    ~r1_tarski(k1_xboole_0,k1_xboole_0) | spl2_3),
% 0.20/0.48    inference(avatar_component_clause,[],[f107])).
% 0.20/0.48  fof(f107,plain,(
% 0.20/0.48    spl2_3 <=> r1_tarski(k1_xboole_0,k1_xboole_0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.20/0.48  fof(f126,plain,(
% 0.20/0.48    ~spl2_3 | ~spl2_4 | ~spl2_5 | ~spl2_2 | ~spl2_6 | spl2_7),
% 0.20/0.48    inference(avatar_split_clause,[],[f105,f123,f119,f89,f115,f111,f107])).
% 0.20/0.48  fof(f89,plain,(
% 0.20/0.48    spl2_2 <=> v1_yellow_1(k1_xboole_0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.20/0.48  fof(f105,plain,(
% 0.20/0.48    k6_yellow_1(k1_xboole_0,sK0) = g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_relat_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) | ~v1_partfun1(k1_xboole_0,k1_xboole_0) | ~v1_yellow_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_xboole_0(k1_xboole_0) | ~r1_tarski(k1_xboole_0,k1_xboole_0)),
% 0.20/0.48    inference(forward_demodulation,[],[f104,f100])).
% 0.20/0.48  fof(f100,plain,(
% 0.20/0.48    k6_yellow_1(k1_xboole_0,sK0) = k5_yellow_1(k1_xboole_0,k1_xboole_0)),
% 0.20/0.48    inference(superposition,[],[f98,f82])).
% 0.20/0.48  fof(f82,plain,(
% 0.20/0.48    ( ! [X0] : (k1_xboole_0 = k2_funcop_1(k1_xboole_0,X0)) )),
% 0.20/0.48    inference(resolution,[],[f56,f50])).
% 0.20/0.48  fof(f50,plain,(
% 0.20/0.48    ( ! [X0] : (v1_xboole_0(k2_funcop_1(k1_xboole_0,X0))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f21])).
% 0.20/0.48  fof(f21,axiom,(
% 0.20/0.48    ! [X0] : v1_xboole_0(k2_funcop_1(k1_xboole_0,X0))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_funcop_1)).
% 0.20/0.48  fof(f56,plain,(
% 0.20/0.48    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.20/0.48    inference(cnf_transformation,[],[f32])).
% 0.20/0.48  fof(f32,plain,(
% 0.20/0.48    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f2])).
% 0.20/0.48  fof(f2,axiom,(
% 0.20/0.48    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.20/0.48  fof(f98,plain,(
% 0.20/0.48    ( ! [X0] : (k6_yellow_1(X0,sK0) = k5_yellow_1(X0,k2_funcop_1(X0,sK0))) )),
% 0.20/0.48    inference(resolution,[],[f79,f43])).
% 0.20/0.48  fof(f79,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~l1_orders_2(X1) | k6_yellow_1(X0,X1) = k5_yellow_1(X0,k2_funcop_1(X0,X1))) )),
% 0.20/0.48    inference(definition_unfolding,[],[f63,f58])).
% 0.20/0.48  fof(f58,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k7_funcop_1(X0,X1) = k2_funcop_1(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f22])).
% 0.20/0.48  fof(f22,axiom,(
% 0.20/0.48    ! [X0,X1] : k7_funcop_1(X0,X1) = k2_funcop_1(X0,X1)),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_funcop_1)).
% 0.20/0.48  fof(f63,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1)) | ~l1_orders_2(X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f37])).
% 0.20/0.48  fof(f37,plain,(
% 0.20/0.48    ! [X0,X1] : (k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1)) | ~l1_orders_2(X1))),
% 0.20/0.48    inference(ennf_transformation,[],[f19])).
% 0.20/0.48  fof(f19,axiom,(
% 0.20/0.48    ! [X0,X1] : (l1_orders_2(X1) => k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1)))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_yellow_1)).
% 0.20/0.48  fof(f104,plain,(
% 0.20/0.48    ~v1_partfun1(k1_xboole_0,k1_xboole_0) | g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_relat_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0) | ~v1_yellow_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_xboole_0(k1_xboole_0) | ~r1_tarski(k1_xboole_0,k1_xboole_0)),
% 0.20/0.48    inference(resolution,[],[f103,f95])).
% 0.20/0.48  fof(f95,plain,(
% 0.20/0.48    ( ! [X0] : (v4_relat_1(k1_xboole_0,X0) | ~r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.48    inference(forward_demodulation,[],[f94,f47])).
% 0.20/0.48  fof(f47,plain,(
% 0.20/0.48    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.48    inference(cnf_transformation,[],[f13])).
% 0.20/0.48  fof(f13,axiom,(
% 0.20/0.48    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.20/0.48  fof(f94,plain,(
% 0.20/0.48    ( ! [X0] : (v4_relat_1(k1_xboole_0,X0) | ~r1_tarski(k1_relat_1(k1_xboole_0),X0)) )),
% 0.20/0.48    inference(resolution,[],[f93,f45])).
% 0.20/0.48  fof(f93,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~v1_xboole_0(X0) | v4_relat_1(X0,X1) | ~r1_tarski(k1_relat_1(X0),X1)) )),
% 0.20/0.48    inference(resolution,[],[f61,f55])).
% 0.20/0.48  fof(f61,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k1_relat_1(X1),X0) | v4_relat_1(X1,X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f40])).
% 0.20/0.48  fof(f40,plain,(
% 0.20/0.48    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.20/0.48    inference(nnf_transformation,[],[f35])).
% 0.20/0.48  fof(f35,plain,(
% 0.20/0.48    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.48    inference(ennf_transformation,[],[f12])).
% 0.20/0.48  fof(f12,axiom,(
% 0.20/0.48    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 0.20/0.48  fof(f103,plain,(
% 0.20/0.48    ( ! [X0] : (~v4_relat_1(X0,k1_xboole_0) | ~v1_partfun1(X0,k1_xboole_0) | k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_relat_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) | ~v1_yellow_1(X0) | ~v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 0.20/0.48    inference(resolution,[],[f78,f54])).
% 0.20/0.48  fof(f54,plain,(
% 0.20/0.48    ( ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f30])).
% 0.20/0.48  fof(f30,plain,(
% 0.20/0.48    ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f15])).
% 0.20/0.48  fof(f15,axiom,(
% 0.20/0.48    ! [X0] : (v1_xboole_0(X0) => v1_funct_1(X0))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_1)).
% 0.20/0.48  fof(f78,plain,(
% 0.20/0.48    ( ! [X0] : (~v1_funct_1(X0) | ~v1_yellow_1(X0) | ~v1_partfun1(X0,k1_xboole_0) | k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_relat_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) )),
% 0.20/0.48    inference(definition_unfolding,[],[f57,f75,f51,f75])).
% 0.20/0.48  fof(f57,plain,(
% 0.20/0.48    ( ! [X0] : (k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) | ~v1_yellow_1(X0) | ~v1_partfun1(X0,k1_xboole_0) | ~v1_funct_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f34])).
% 0.20/0.48  fof(f34,plain,(
% 0.20/0.48    ! [X0] : (k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) | ~v1_yellow_1(X0) | ~v1_partfun1(X0,k1_xboole_0) | ~v1_funct_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 0.20/0.48    inference(flattening,[],[f33])).
% 0.20/0.48  fof(f33,plain,(
% 0.20/0.48    ! [X0] : (k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) | (~v1_yellow_1(X0) | ~v1_partfun1(X0,k1_xboole_0) | ~v1_funct_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f23])).
% 0.20/0.48  fof(f23,axiom,(
% 0.20/0.48    ! [X0] : ((v1_yellow_1(X0) & v1_partfun1(X0,k1_xboole_0) & v1_funct_1(X0) & v4_relat_1(X0,k1_xboole_0) & v1_relat_1(X0)) => k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_yellow_1)).
% 0.20/0.48  fof(f92,plain,(
% 0.20/0.48    spl2_1 | spl2_2),
% 0.20/0.48    inference(avatar_split_clause,[],[f84,f89,f86])).
% 0.20/0.48  fof(f84,plain,(
% 0.20/0.48    ( ! [X0] : (v1_yellow_1(k1_xboole_0) | ~l1_orders_2(X0)) )),
% 0.20/0.48    inference(superposition,[],[f62,f82])).
% 0.20/0.48  fof(f62,plain,(
% 0.20/0.48    ( ! [X0,X1] : (v1_yellow_1(k2_funcop_1(X0,X1)) | ~l1_orders_2(X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f36])).
% 0.20/0.48  fof(f36,plain,(
% 0.20/0.48    ! [X0,X1] : (v1_yellow_1(k2_funcop_1(X0,X1)) | ~l1_orders_2(X1))),
% 0.20/0.48    inference(ennf_transformation,[],[f20])).
% 0.20/0.48  fof(f20,axiom,(
% 0.20/0.48    ! [X0,X1] : (l1_orders_2(X1) => v1_yellow_1(k2_funcop_1(X0,X1)))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_yellow_1)).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (22003)------------------------------
% 0.20/0.48  % (22003)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (22003)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (22003)Memory used [KB]: 6140
% 0.20/0.48  % (22003)Time elapsed: 0.064 s
% 0.20/0.48  % (22003)------------------------------
% 0.20/0.48  % (22003)------------------------------
% 0.20/0.48  % (21999)Success in time 0.12 s
%------------------------------------------------------------------------------
