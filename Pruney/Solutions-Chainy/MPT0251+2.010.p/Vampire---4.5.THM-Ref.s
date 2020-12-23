%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:38:36 EST 2020

% Result     : Theorem 1.57s
% Output     : Refutation 1.57s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 447 expanded)
%              Number of leaves         :   21 ( 158 expanded)
%              Depth                    :   14
%              Number of atoms          :  119 ( 507 expanded)
%              Number of equality atoms :   60 ( 417 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f950,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f76,f81,f143,f160,f214,f239,f921])).

fof(f921,plain,
    ( spl5_11
    | ~ spl5_8
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f920,f235,f157,f210])).

fof(f210,plain,
    ( spl5_11
  <=> sK1 = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f157,plain,
    ( spl5_8
  <=> k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f235,plain,
    ( spl5_14
  <=> k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f920,plain,
    ( sK1 = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))
    | ~ spl5_8
    | ~ spl5_14 ),
    inference(forward_demodulation,[],[f919,f63])).

fof(f63,plain,(
    ! [X0] : k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f32,f60])).

fof(f60,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f36,f59])).

fof(f59,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f37,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f56,f57])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f56,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f37,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f36,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f32,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f919,plain,
    ( k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k1_xboole_0))
    | ~ spl5_8
    | ~ spl5_14 ),
    inference(forward_demodulation,[],[f898,f486])).

fof(f486,plain,
    ( ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)
    | ~ spl5_14 ),
    inference(forward_demodulation,[],[f485,f237])).

fof(f237,plain,
    ( k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f235])).

fof(f485,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f189,f216])).

fof(f216,plain,(
    ! [X1] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X1) ),
    inference(resolution,[],[f186,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f186,plain,(
    ! [X3] : r1_tarski(k1_xboole_0,X3) ),
    inference(superposition,[],[f64,f161])).

fof(f161,plain,(
    ! [X0] : k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0 ),
    inference(superposition,[],[f65,f63])).

fof(f65,plain,(
    ! [X0,X1] : k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)) ),
    inference(definition_unfolding,[],[f35,f60,f60])).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f64,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f34,f60])).

fof(f34,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f189,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) ),
    inference(forward_demodulation,[],[f183,f92])).

fof(f92,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(resolution,[],[f46,f70])).

fof(f70,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f183,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[],[f66,f161])).

fof(f66,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X1)) ),
    inference(definition_unfolding,[],[f39,f38,f38,f60])).

fof(f38,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f39,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f898,plain,
    ( k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0))))
    | ~ spl5_8 ),
    inference(superposition,[],[f67,f159])).

fof(f159,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f157])).

fof(f67,plain,(
    ! [X0,X1] : k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f40,f60,f60,f38])).

fof(f40,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f239,plain,(
    spl5_14 ),
    inference(avatar_split_clause,[],[f231,f235])).

fof(f231,plain,(
    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f188,f216])).

fof(f188,plain,(
    ! [X3] : k5_xboole_0(X3,k3_xboole_0(X3,k1_xboole_0)) = X3 ),
    inference(forward_demodulation,[],[f182,f161])).

fof(f182,plain,(
    ! [X3] : k5_xboole_0(X3,k3_xboole_0(X3,k1_xboole_0)) = k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X3)) ),
    inference(superposition,[],[f161,f67])).

fof(f214,plain,
    ( ~ spl5_11
    | spl5_1 ),
    inference(avatar_split_clause,[],[f194,f73,f210])).

fof(f73,plain,
    ( spl5_1
  <=> sK1 = k3_tarski(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f194,plain,
    ( sK1 != k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))
    | spl5_1 ),
    inference(superposition,[],[f75,f65])).

fof(f75,plain,
    ( sK1 != k3_tarski(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f73])).

fof(f160,plain,
    ( spl5_8
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f146,f140,f157])).

fof(f140,plain,
    ( spl5_5
  <=> r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f146,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)
    | ~ spl5_5 ),
    inference(resolution,[],[f142,f46])).

fof(f142,plain,
    ( r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f140])).

fof(f143,plain,
    ( spl5_5
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f134,f78,f140])).

fof(f78,plain,
    ( spl5_2
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f134,plain,
    ( r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)
    | ~ spl5_2 ),
    inference(resolution,[],[f69,f80])).

fof(f80,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f78])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) ) ),
    inference(definition_unfolding,[],[f54,f61])).

fof(f61,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f33,f59])).

fof(f33,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f81,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f30,f78])).

fof(f30,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ? [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) != X1
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).

fof(f76,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f62,f73])).

fof(f62,plain,(
    sK1 != k3_tarski(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)) ),
    inference(definition_unfolding,[],[f31,f60,f61])).

fof(f31,plain,(
    sK1 != k2_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n012.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:24:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.53  % (25601)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (25593)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.53  % (25578)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (25583)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.55  % (25585)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.33/0.55  % (25579)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.33/0.55  % (25594)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.33/0.55  % (25586)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.33/0.55  % (25584)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.33/0.56  % (25582)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.33/0.56  % (25586)Refutation not found, incomplete strategy% (25586)------------------------------
% 1.33/0.56  % (25586)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.56  % (25586)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.56  
% 1.33/0.56  % (25586)Memory used [KB]: 10618
% 1.33/0.56  % (25586)Time elapsed: 0.134 s
% 1.33/0.56  % (25586)------------------------------
% 1.33/0.56  % (25586)------------------------------
% 1.33/0.56  % (25581)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.33/0.56  % (25580)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.57/0.56  % (25602)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.57/0.57  % (25580)Refutation not found, incomplete strategy% (25580)------------------------------
% 1.57/0.57  % (25580)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.57  % (25580)Termination reason: Refutation not found, incomplete strategy
% 1.57/0.57  
% 1.57/0.57  % (25580)Memory used [KB]: 10746
% 1.57/0.57  % (25580)Time elapsed: 0.146 s
% 1.57/0.57  % (25580)------------------------------
% 1.57/0.57  % (25580)------------------------------
% 1.57/0.57  % (25606)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.57/0.57  % (25591)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.57/0.57  % (25599)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.57/0.58  % (25600)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.57/0.58  % (25587)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.57/0.59  % (25592)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.57/0.59  % (25604)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.57/0.59  % (25603)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.57/0.60  % (25605)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.57/0.60  % (25596)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.57/0.60  % (25590)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.57/0.60  % (25595)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.57/0.60  % (25600)Refutation not found, incomplete strategy% (25600)------------------------------
% 1.57/0.60  % (25600)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.60  % (25600)Termination reason: Refutation not found, incomplete strategy
% 1.57/0.60  
% 1.57/0.60  % (25600)Memory used [KB]: 10746
% 1.57/0.60  % (25600)Time elapsed: 0.157 s
% 1.57/0.60  % (25600)------------------------------
% 1.57/0.60  % (25600)------------------------------
% 1.57/0.60  % (25607)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.57/0.60  % (25597)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.57/0.60  % (25598)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.57/0.61  % (25588)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.57/0.61  % (25588)Refutation not found, incomplete strategy% (25588)------------------------------
% 1.57/0.61  % (25588)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.61  % (25588)Termination reason: Refutation not found, incomplete strategy
% 1.57/0.61  
% 1.57/0.61  % (25588)Memory used [KB]: 10618
% 1.57/0.61  % (25588)Time elapsed: 0.182 s
% 1.57/0.61  % (25588)------------------------------
% 1.57/0.61  % (25588)------------------------------
% 1.57/0.61  % (25589)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.57/0.61  % (25589)Refutation not found, incomplete strategy% (25589)------------------------------
% 1.57/0.61  % (25589)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.61  % (25589)Termination reason: Refutation not found, incomplete strategy
% 1.57/0.61  
% 1.57/0.61  % (25589)Memory used [KB]: 10618
% 1.57/0.61  % (25589)Time elapsed: 0.184 s
% 1.57/0.61  % (25589)------------------------------
% 1.57/0.61  % (25589)------------------------------
% 1.57/0.63  % (25594)Refutation found. Thanks to Tanya!
% 1.57/0.63  % SZS status Theorem for theBenchmark
% 1.57/0.64  % SZS output start Proof for theBenchmark
% 1.57/0.64  fof(f950,plain,(
% 1.57/0.64    $false),
% 1.57/0.64    inference(avatar_sat_refutation,[],[f76,f81,f143,f160,f214,f239,f921])).
% 1.57/0.64  fof(f921,plain,(
% 1.57/0.64    spl5_11 | ~spl5_8 | ~spl5_14),
% 1.57/0.64    inference(avatar_split_clause,[],[f920,f235,f157,f210])).
% 1.57/0.64  fof(f210,plain,(
% 1.57/0.64    spl5_11 <=> sK1 = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),
% 1.57/0.64    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 1.57/0.64  fof(f157,plain,(
% 1.57/0.64    spl5_8 <=> k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)),
% 1.57/0.64    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 1.57/0.64  fof(f235,plain,(
% 1.57/0.64    spl5_14 <=> k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0)),
% 1.57/0.64    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 1.57/0.64  fof(f920,plain,(
% 1.57/0.64    sK1 = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) | (~spl5_8 | ~spl5_14)),
% 1.57/0.64    inference(forward_demodulation,[],[f919,f63])).
% 1.57/0.64  fof(f63,plain,(
% 1.57/0.64    ( ! [X0] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0) )),
% 1.57/0.64    inference(definition_unfolding,[],[f32,f60])).
% 1.57/0.64  fof(f60,plain,(
% 1.57/0.64    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 1.57/0.64    inference(definition_unfolding,[],[f36,f59])).
% 1.57/0.64  fof(f59,plain,(
% 1.57/0.64    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 1.57/0.64    inference(definition_unfolding,[],[f37,f58])).
% 1.57/0.64  fof(f58,plain,(
% 1.57/0.64    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 1.57/0.64    inference(definition_unfolding,[],[f56,f57])).
% 1.57/0.64  fof(f57,plain,(
% 1.57/0.64    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.57/0.64    inference(cnf_transformation,[],[f17])).
% 1.57/0.64  fof(f17,axiom,(
% 1.57/0.64    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.57/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.57/0.64  fof(f56,plain,(
% 1.57/0.64    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.57/0.64    inference(cnf_transformation,[],[f16])).
% 1.57/0.64  fof(f16,axiom,(
% 1.57/0.64    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.57/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.57/0.64  fof(f37,plain,(
% 1.57/0.64    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.57/0.64    inference(cnf_transformation,[],[f15])).
% 1.57/0.64  fof(f15,axiom,(
% 1.57/0.64    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.57/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.57/0.64  fof(f36,plain,(
% 1.57/0.64    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.57/0.64    inference(cnf_transformation,[],[f19])).
% 1.57/0.64  fof(f19,axiom,(
% 1.57/0.64    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.57/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.57/0.64  fof(f32,plain,(
% 1.57/0.64    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.57/0.64    inference(cnf_transformation,[],[f9])).
% 1.57/0.64  fof(f9,axiom,(
% 1.57/0.64    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.57/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 1.57/0.64  fof(f919,plain,(
% 1.57/0.64    k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k1_xboole_0)) | (~spl5_8 | ~spl5_14)),
% 1.57/0.64    inference(forward_demodulation,[],[f898,f486])).
% 1.57/0.64  fof(f486,plain,(
% 1.57/0.64    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) ) | ~spl5_14),
% 1.57/0.64    inference(forward_demodulation,[],[f485,f237])).
% 1.57/0.64  fof(f237,plain,(
% 1.57/0.64    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl5_14),
% 1.57/0.64    inference(avatar_component_clause,[],[f235])).
% 1.57/0.64  fof(f485,plain,(
% 1.57/0.64    ( ! [X0] : (k5_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,k1_xboole_0)) )),
% 1.57/0.64    inference(forward_demodulation,[],[f189,f216])).
% 1.57/0.64  fof(f216,plain,(
% 1.57/0.64    ( ! [X1] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X1)) )),
% 1.57/0.64    inference(resolution,[],[f186,f46])).
% 1.57/0.64  fof(f46,plain,(
% 1.57/0.64    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.57/0.64    inference(cnf_transformation,[],[f27])).
% 1.57/0.64  fof(f27,plain,(
% 1.57/0.64    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.57/0.64    inference(ennf_transformation,[],[f10])).
% 1.57/0.64  fof(f10,axiom,(
% 1.57/0.64    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.57/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.57/0.64  fof(f186,plain,(
% 1.57/0.64    ( ! [X3] : (r1_tarski(k1_xboole_0,X3)) )),
% 1.57/0.64    inference(superposition,[],[f64,f161])).
% 1.57/0.64  fof(f161,plain,(
% 1.57/0.64    ( ! [X0] : (k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0) )),
% 1.57/0.64    inference(superposition,[],[f65,f63])).
% 1.57/0.64  fof(f65,plain,(
% 1.57/0.64    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,X0))) )),
% 1.57/0.64    inference(definition_unfolding,[],[f35,f60,f60])).
% 1.57/0.64  fof(f35,plain,(
% 1.57/0.64    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.57/0.64    inference(cnf_transformation,[],[f2])).
% 1.57/0.64  fof(f2,axiom,(
% 1.57/0.64    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.57/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.57/0.64  fof(f64,plain,(
% 1.57/0.64    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))) )),
% 1.57/0.64    inference(definition_unfolding,[],[f34,f60])).
% 1.57/0.64  fof(f34,plain,(
% 1.57/0.64    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.57/0.64    inference(cnf_transformation,[],[f13])).
% 1.57/0.64  fof(f13,axiom,(
% 1.57/0.64    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.57/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.57/0.64  fof(f189,plain,(
% 1.57/0.64    ( ! [X0] : (k5_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) )),
% 1.57/0.64    inference(forward_demodulation,[],[f183,f92])).
% 1.57/0.64  fof(f92,plain,(
% 1.57/0.64    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.57/0.64    inference(resolution,[],[f46,f70])).
% 1.57/0.64  fof(f70,plain,(
% 1.57/0.64    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.57/0.64    inference(equality_resolution,[],[f49])).
% 1.57/0.64  fof(f49,plain,(
% 1.57/0.64    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.57/0.64    inference(cnf_transformation,[],[f7])).
% 1.57/0.64  fof(f7,axiom,(
% 1.57/0.64    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.57/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.57/0.64  fof(f183,plain,(
% 1.57/0.64    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) )),
% 1.57/0.64    inference(superposition,[],[f66,f161])).
% 1.57/0.64  fof(f66,plain,(
% 1.57/0.64    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X1))) )),
% 1.57/0.64    inference(definition_unfolding,[],[f39,f38,f38,f60])).
% 1.57/0.64  fof(f38,plain,(
% 1.57/0.64    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.57/0.64    inference(cnf_transformation,[],[f8])).
% 1.57/0.64  fof(f8,axiom,(
% 1.57/0.64    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.57/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.57/0.64  fof(f39,plain,(
% 1.57/0.64    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 1.57/0.64    inference(cnf_transformation,[],[f12])).
% 1.57/0.64  fof(f12,axiom,(
% 1.57/0.64    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 1.57/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).
% 1.57/0.64  fof(f898,plain,(
% 1.57/0.64    k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) | ~spl5_8),
% 1.57/0.64    inference(superposition,[],[f67,f159])).
% 1.57/0.64  fof(f159,plain,(
% 1.57/0.64    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) | ~spl5_8),
% 1.57/0.64    inference(avatar_component_clause,[],[f157])).
% 1.57/0.64  fof(f67,plain,(
% 1.57/0.64    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) )),
% 1.57/0.64    inference(definition_unfolding,[],[f40,f60,f60,f38])).
% 1.57/0.64  fof(f40,plain,(
% 1.57/0.64    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.57/0.64    inference(cnf_transformation,[],[f11])).
% 1.57/0.64  fof(f11,axiom,(
% 1.57/0.64    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.57/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 1.57/0.64  fof(f239,plain,(
% 1.57/0.64    spl5_14),
% 1.57/0.64    inference(avatar_split_clause,[],[f231,f235])).
% 1.57/0.64  fof(f231,plain,(
% 1.57/0.64    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0)),
% 1.57/0.64    inference(superposition,[],[f188,f216])).
% 1.57/0.64  fof(f188,plain,(
% 1.57/0.64    ( ! [X3] : (k5_xboole_0(X3,k3_xboole_0(X3,k1_xboole_0)) = X3) )),
% 1.57/0.64    inference(forward_demodulation,[],[f182,f161])).
% 1.57/0.64  fof(f182,plain,(
% 1.57/0.64    ( ! [X3] : (k5_xboole_0(X3,k3_xboole_0(X3,k1_xboole_0)) = k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X3))) )),
% 1.57/0.64    inference(superposition,[],[f161,f67])).
% 1.57/0.64  fof(f214,plain,(
% 1.57/0.64    ~spl5_11 | spl5_1),
% 1.57/0.64    inference(avatar_split_clause,[],[f194,f73,f210])).
% 1.57/0.64  fof(f73,plain,(
% 1.57/0.64    spl5_1 <=> sK1 = k3_tarski(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1))),
% 1.57/0.64    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.57/0.64  fof(f194,plain,(
% 1.57/0.64    sK1 != k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) | spl5_1),
% 1.57/0.64    inference(superposition,[],[f75,f65])).
% 1.57/0.64  fof(f75,plain,(
% 1.57/0.64    sK1 != k3_tarski(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)) | spl5_1),
% 1.57/0.64    inference(avatar_component_clause,[],[f73])).
% 1.57/0.64  fof(f160,plain,(
% 1.57/0.64    spl5_8 | ~spl5_5),
% 1.57/0.64    inference(avatar_split_clause,[],[f146,f140,f157])).
% 1.57/0.64  fof(f140,plain,(
% 1.57/0.64    spl5_5 <=> r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)),
% 1.57/0.64    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 1.57/0.64  fof(f146,plain,(
% 1.57/0.64    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) | ~spl5_5),
% 1.57/0.64    inference(resolution,[],[f142,f46])).
% 1.57/0.64  fof(f142,plain,(
% 1.57/0.64    r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) | ~spl5_5),
% 1.57/0.64    inference(avatar_component_clause,[],[f140])).
% 1.57/0.64  fof(f143,plain,(
% 1.57/0.64    spl5_5 | ~spl5_2),
% 1.57/0.64    inference(avatar_split_clause,[],[f134,f78,f140])).
% 1.57/0.64  fof(f78,plain,(
% 1.57/0.64    spl5_2 <=> r2_hidden(sK0,sK1)),
% 1.57/0.64    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.57/0.64  fof(f134,plain,(
% 1.57/0.64    r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) | ~spl5_2),
% 1.57/0.64    inference(resolution,[],[f69,f80])).
% 1.57/0.64  fof(f80,plain,(
% 1.57/0.64    r2_hidden(sK0,sK1) | ~spl5_2),
% 1.57/0.64    inference(avatar_component_clause,[],[f78])).
% 1.57/0.64  fof(f69,plain,(
% 1.57/0.64    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1)) )),
% 1.57/0.64    inference(definition_unfolding,[],[f54,f61])).
% 1.57/0.64  fof(f61,plain,(
% 1.57/0.64    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 1.57/0.64    inference(definition_unfolding,[],[f33,f59])).
% 1.57/0.64  fof(f33,plain,(
% 1.57/0.64    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.57/0.64    inference(cnf_transformation,[],[f14])).
% 1.57/0.64  fof(f14,axiom,(
% 1.57/0.64    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.57/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.57/0.64  fof(f54,plain,(
% 1.57/0.64    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1)) )),
% 1.57/0.64    inference(cnf_transformation,[],[f18])).
% 1.57/0.64  fof(f18,axiom,(
% 1.57/0.64    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.57/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 1.57/0.64  fof(f81,plain,(
% 1.57/0.64    spl5_2),
% 1.57/0.64    inference(avatar_split_clause,[],[f30,f78])).
% 1.57/0.64  fof(f30,plain,(
% 1.57/0.64    r2_hidden(sK0,sK1)),
% 1.57/0.64    inference(cnf_transformation,[],[f24])).
% 1.57/0.64  fof(f24,plain,(
% 1.57/0.64    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1))),
% 1.57/0.64    inference(ennf_transformation,[],[f21])).
% 1.57/0.64  fof(f21,negated_conjecture,(
% 1.57/0.64    ~! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 1.57/0.64    inference(negated_conjecture,[],[f20])).
% 1.57/0.64  fof(f20,conjecture,(
% 1.57/0.64    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 1.57/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).
% 1.57/0.64  fof(f76,plain,(
% 1.57/0.64    ~spl5_1),
% 1.57/0.64    inference(avatar_split_clause,[],[f62,f73])).
% 1.57/0.64  fof(f62,plain,(
% 1.57/0.64    sK1 != k3_tarski(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1))),
% 1.57/0.64    inference(definition_unfolding,[],[f31,f60,f61])).
% 1.57/0.64  fof(f31,plain,(
% 1.57/0.64    sK1 != k2_xboole_0(k1_tarski(sK0),sK1)),
% 1.57/0.64    inference(cnf_transformation,[],[f24])).
% 1.57/0.64  % SZS output end Proof for theBenchmark
% 1.57/0.64  % (25594)------------------------------
% 1.57/0.64  % (25594)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.64  % (25594)Termination reason: Refutation
% 1.57/0.64  
% 1.57/0.64  % (25594)Memory used [KB]: 11385
% 1.57/0.64  % (25594)Time elapsed: 0.206 s
% 1.57/0.64  % (25594)------------------------------
% 1.57/0.64  % (25594)------------------------------
% 1.57/0.64  % (25577)Success in time 0.275 s
%------------------------------------------------------------------------------
