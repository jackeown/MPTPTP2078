%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0254+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:37 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   47 (  66 expanded)
%              Number of leaves         :   14 (  30 expanded)
%              Depth                    :    7
%              Number of atoms          :   80 ( 114 expanded)
%              Number of equality atoms :   28 (  43 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f71,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f28,f33,f43,f51,f58,f67,f70])).

fof(f70,plain,
    ( ~ spl2_2
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f69,f63,f30])).

fof(f30,plain,
    ( spl2_2
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f63,plain,
    ( spl2_6
  <=> o_0_0_xboole_0 = k1_tarski(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f69,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | ~ spl2_6 ),
    inference(superposition,[],[f17,f65])).

fof(f65,plain,
    ( o_0_0_xboole_0 = k1_tarski(sK0)
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f63])).

fof(f17,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).

% (29339)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% (29348)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% (29350)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% (29347)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% (29352)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
fof(f67,plain,
    ( spl2_6
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f60,f55,f63])).

fof(f55,plain,
    ( spl2_5
  <=> o_0_0_xboole_0 = k2_xboole_0(k1_tarski(sK0),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f60,plain,
    ( o_0_0_xboole_0 = k1_tarski(sK0)
    | ~ spl2_5 ),
    inference(superposition,[],[f22,f57])).

fof(f57,plain,
    ( o_0_0_xboole_0 = k2_xboole_0(k1_tarski(sK0),o_0_0_xboole_0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f55])).

fof(f22,plain,(
    ! [X0] : k2_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f18,f16])).

fof(f16,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_xboole_0)).

fof(f18,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f58,plain,
    ( spl2_5
    | ~ spl2_1
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f53,f47,f25,f55])).

fof(f25,plain,
    ( spl2_1
  <=> o_0_0_xboole_0 = k2_xboole_0(k1_tarski(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f47,plain,
    ( spl2_4
  <=> o_0_0_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f53,plain,
    ( o_0_0_xboole_0 = k2_xboole_0(k1_tarski(sK0),o_0_0_xboole_0)
    | ~ spl2_1
    | ~ spl2_4 ),
    inference(backward_demodulation,[],[f27,f49])).

fof(f49,plain,
    ( o_0_0_xboole_0 = sK1
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f47])).

fof(f27,plain,
    ( o_0_0_xboole_0 = k2_xboole_0(k1_tarski(sK0),sK1)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f25])).

fof(f51,plain,
    ( spl2_4
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f45,f40,f47])).

fof(f40,plain,
    ( spl2_3
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f45,plain,
    ( o_0_0_xboole_0 = sK1
    | ~ spl2_3 ),
    inference(resolution,[],[f42,f23])).

fof(f23,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f19,f16])).

fof(f19,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

fof(f42,plain,
    ( v1_xboole_0(sK1)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f40])).

fof(f43,plain,
    ( spl2_3
    | ~ spl2_2
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f37,f25,f30,f40])).

fof(f37,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | v1_xboole_0(sK1)
    | ~ spl2_1 ),
    inference(superposition,[],[f20,f27])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k2_xboole_0(X1,X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k2_xboole_0(X1,X0))
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
     => ~ v1_xboole_0(k2_xboole_0(X1,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_xboole_0)).

fof(f33,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f15,f30])).

fof(f15,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

fof(f28,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f21,f25])).

fof(f21,plain,(
    o_0_0_xboole_0 = k2_xboole_0(k1_tarski(sK0),sK1) ),
    inference(definition_unfolding,[],[f14,f16])).

fof(f14,plain,(
    k1_xboole_0 = k2_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    k1_xboole_0 = k2_xboole_0(k1_tarski(sK0),sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f12])).

fof(f12,plain,
    ( ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1)
   => k1_xboole_0 = k2_xboole_0(k1_tarski(sK0),sK1) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

%------------------------------------------------------------------------------
