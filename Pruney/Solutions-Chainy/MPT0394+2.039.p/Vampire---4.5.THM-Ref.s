%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:01 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 163 expanded)
%              Number of leaves         :   16 (  63 expanded)
%              Depth                    :   10
%              Number of atoms          :  116 ( 235 expanded)
%              Number of equality atoms :   70 ( 165 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f133,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f41,f59,f74,f89,f125,f129,f132])).

fof(f132,plain,
    ( spl2_4
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f100,f87,f72])).

fof(f72,plain,
    ( spl2_4
  <=> r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f87,plain,
    ( spl2_8
  <=> k1_xboole_0 = k3_xboole_0(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f100,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl2_8 ),
    inference(trivial_inequality_removal,[],[f99])).

fof(f99,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl2_8 ),
    inference(superposition,[],[f26,f88])).

fof(f88,plain,
    ( k1_xboole_0 = k3_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f87])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
     => r1_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f129,plain,
    ( ~ spl2_4
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f107,f54,f72])).

fof(f54,plain,
    ( spl2_2
  <=> k1_xboole_0 = k1_enumset1(sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f107,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl2_2 ),
    inference(superposition,[],[f37,f55])).

fof(f55,plain,
    ( k1_xboole_0 = k1_enumset1(sK0,sK0,sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f54])).

fof(f37,plain,(
    ! [X1] : ~ r1_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X1)) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r1_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f28,f29,f29])).

fof(f29,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f21,f22])).

fof(f22,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f21,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f28,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( X0 = X1
        & r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_zfmisc_1)).

fof(f125,plain,
    ( spl2_8
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f111,f54,f87])).

fof(f111,plain,
    ( k1_xboole_0 = k3_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl2_2 ),
    inference(superposition,[],[f33,f55])).

fof(f33,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X0) = k3_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f24,f29,f29,f22])).

fof(f24,plain,(
    ! [X0,X1] : k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_zfmisc_1)).

fof(f89,plain,
    ( spl2_8
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f68,f57,f87])).

fof(f57,plain,
    ( spl2_3
  <=> k1_xboole_0 = k1_enumset1(sK1,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f68,plain,
    ( k1_xboole_0 = k3_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl2_3 ),
    inference(superposition,[],[f33,f58])).

fof(f58,plain,
    ( k1_xboole_0 = k1_enumset1(sK1,sK1,sK1)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f57])).

fof(f74,plain,
    ( ~ spl2_4
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f64,f57,f72])).

fof(f64,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl2_3 ),
    inference(superposition,[],[f37,f58])).

fof(f59,plain,
    ( spl2_2
    | spl2_3
    | spl2_1 ),
    inference(avatar_split_clause,[],[f51,f39,f57,f54])).

fof(f39,plain,
    ( spl2_1
  <=> k3_xboole_0(sK0,sK1) = k1_setfam_1(k1_enumset1(sK0,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f51,plain,
    ( k1_xboole_0 = k1_enumset1(sK1,sK1,sK1)
    | k1_xboole_0 = k1_enumset1(sK0,sK0,sK0)
    | spl2_1 ),
    inference(trivial_inequality_removal,[],[f48])).

fof(f48,plain,
    ( k3_xboole_0(sK0,sK1) != k3_xboole_0(sK0,sK1)
    | k1_xboole_0 = k1_enumset1(sK1,sK1,sK1)
    | k1_xboole_0 = k1_enumset1(sK0,sK0,sK0)
    | spl2_1 ),
    inference(superposition,[],[f40,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))
      | k1_xboole_0 = k1_enumset1(X1,X1,X1)
      | k1_xboole_0 = k1_enumset1(X0,X0,X0) ) ),
    inference(forward_demodulation,[],[f45,f32])).

fof(f32,plain,(
    ! [X0] : k1_setfam_1(k1_enumset1(X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f20,f29])).

fof(f20,plain,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).

fof(f45,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = k3_xboole_0(k1_setfam_1(k1_enumset1(X0,X0,X0)),X1)
      | k1_xboole_0 = k1_enumset1(X1,X1,X1)
      | k1_xboole_0 = k1_enumset1(X0,X0,X0) ) ),
    inference(forward_demodulation,[],[f44,f32])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_setfam_1(k1_enumset1(X0,X0,X0)),k1_setfam_1(k1_enumset1(X1,X1,X1))) = k1_setfam_1(k1_enumset1(X0,X0,X1))
      | k1_xboole_0 = k1_enumset1(X1,X1,X1)
      | k1_xboole_0 = k1_enumset1(X0,X0,X0) ) ),
    inference(superposition,[],[f35,f34])).

fof(f34,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X1))) ),
    inference(definition_unfolding,[],[f25,f22,f30,f29,f29])).

fof(f30,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f23,f22])).

fof(f23,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f25,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

fof(f35,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) = k1_setfam_1(k3_tarski(k1_enumset1(X0,X0,X1)))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f27,f30])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_xboole_0(X0,X1)) = k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_xboole_0(X0,X1)) = k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ~ ( k1_setfam_1(k2_xboole_0(X0,X1)) != k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1))
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_setfam_1)).

fof(f40,plain,
    ( k3_xboole_0(sK0,sK1) != k1_setfam_1(k1_enumset1(sK0,sK0,sK1))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f39])).

fof(f41,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f31,f39])).

fof(f31,plain,(
    k3_xboole_0(sK0,sK1) != k1_setfam_1(k1_enumset1(sK0,sK0,sK1)) ),
    inference(definition_unfolding,[],[f19,f22])).

fof(f19,plain,(
    k3_xboole_0(sK0,sK1) != k1_setfam_1(k2_tarski(sK0,sK1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    k3_xboole_0(sK0,sK1) != k1_setfam_1(k2_tarski(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f17])).

fof(f17,plain,
    ( ? [X0,X1] : k3_xboole_0(X0,X1) != k1_setfam_1(k2_tarski(X0,X1))
   => k3_xboole_0(sK0,sK1) != k1_setfam_1(k2_tarski(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1] : k3_xboole_0(X0,X1) != k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 10:36:27 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.19/0.49  % (23966)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.19/0.50  % (23968)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.19/0.50  % (23966)Refutation not found, incomplete strategy% (23966)------------------------------
% 0.19/0.50  % (23966)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.50  % (23975)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.19/0.50  % (23975)Refutation not found, incomplete strategy% (23975)------------------------------
% 0.19/0.50  % (23975)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.50  % (23975)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.50  
% 0.19/0.50  % (23975)Memory used [KB]: 10618
% 0.19/0.50  % (23975)Time elapsed: 0.101 s
% 0.19/0.50  % (23975)------------------------------
% 0.19/0.50  % (23975)------------------------------
% 0.19/0.50  % (23966)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.50  
% 0.19/0.50  % (23966)Memory used [KB]: 10618
% 0.19/0.50  % (23966)Time elapsed: 0.090 s
% 0.19/0.50  % (23966)------------------------------
% 0.19/0.50  % (23966)------------------------------
% 0.19/0.51  % (23968)Refutation not found, incomplete strategy% (23968)------------------------------
% 0.19/0.51  % (23968)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.51  % (23987)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.19/0.51  % (23987)Refutation not found, incomplete strategy% (23987)------------------------------
% 0.19/0.51  % (23987)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.51  % (23987)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.51  
% 0.19/0.51  % (23987)Memory used [KB]: 1663
% 0.19/0.51  % (23987)Time elapsed: 0.073 s
% 0.19/0.51  % (23987)------------------------------
% 0.19/0.51  % (23987)------------------------------
% 0.19/0.51  % (23968)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.51  
% 0.19/0.51  % (23968)Memory used [KB]: 6140
% 0.19/0.51  % (23968)Time elapsed: 0.113 s
% 0.19/0.51  % (23968)------------------------------
% 0.19/0.51  % (23968)------------------------------
% 0.19/0.51  % (23980)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.19/0.51  % (23964)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.19/0.51  % (23976)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.51  % (23983)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.19/0.51  % (23965)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.19/0.51  % (23983)Refutation found. Thanks to Tanya!
% 0.19/0.51  % SZS status Theorem for theBenchmark
% 0.19/0.51  % SZS output start Proof for theBenchmark
% 0.19/0.51  fof(f133,plain,(
% 0.19/0.51    $false),
% 0.19/0.51    inference(avatar_sat_refutation,[],[f41,f59,f74,f89,f125,f129,f132])).
% 0.19/0.51  fof(f132,plain,(
% 0.19/0.51    spl2_4 | ~spl2_8),
% 0.19/0.51    inference(avatar_split_clause,[],[f100,f87,f72])).
% 0.19/0.51  fof(f72,plain,(
% 0.19/0.51    spl2_4 <=> r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.19/0.51  fof(f87,plain,(
% 0.19/0.51    spl2_8 <=> k1_xboole_0 = k3_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.19/0.51  fof(f100,plain,(
% 0.19/0.51    r1_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl2_8),
% 0.19/0.51    inference(trivial_inequality_removal,[],[f99])).
% 0.19/0.51  fof(f99,plain,(
% 0.19/0.51    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl2_8),
% 0.19/0.51    inference(superposition,[],[f26,f88])).
% 0.19/0.51  fof(f88,plain,(
% 0.19/0.51    k1_xboole_0 = k3_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl2_8),
% 0.19/0.51    inference(avatar_component_clause,[],[f87])).
% 0.19/0.51  fof(f26,plain,(
% 0.19/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f14])).
% 0.19/0.51  fof(f14,plain,(
% 0.19/0.51    ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0)),
% 0.19/0.51    inference(ennf_transformation,[],[f12])).
% 0.19/0.51  fof(f12,plain,(
% 0.19/0.51    ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 => r1_xboole_0(X0,X1))),
% 0.19/0.51    inference(unused_predicate_definition_removal,[],[f1])).
% 0.19/0.51  fof(f1,axiom,(
% 0.19/0.51    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.19/0.51  fof(f129,plain,(
% 0.19/0.51    ~spl2_4 | ~spl2_2),
% 0.19/0.51    inference(avatar_split_clause,[],[f107,f54,f72])).
% 0.19/0.51  fof(f54,plain,(
% 0.19/0.51    spl2_2 <=> k1_xboole_0 = k1_enumset1(sK0,sK0,sK0)),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.19/0.51  fof(f107,plain,(
% 0.19/0.51    ~r1_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl2_2),
% 0.19/0.51    inference(superposition,[],[f37,f55])).
% 0.19/0.51  fof(f55,plain,(
% 0.19/0.51    k1_xboole_0 = k1_enumset1(sK0,sK0,sK0) | ~spl2_2),
% 0.19/0.51    inference(avatar_component_clause,[],[f54])).
% 0.19/0.51  fof(f37,plain,(
% 0.19/0.51    ( ! [X1] : (~r1_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X1))) )),
% 0.19/0.51    inference(equality_resolution,[],[f36])).
% 0.19/0.51  fof(f36,plain,(
% 0.19/0.51    ( ! [X0,X1] : (X0 != X1 | ~r1_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X1))) )),
% 0.19/0.51    inference(definition_unfolding,[],[f28,f29,f29])).
% 0.19/0.51  fof(f29,plain,(
% 0.19/0.51    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.19/0.51    inference(definition_unfolding,[],[f21,f22])).
% 0.19/0.51  fof(f22,plain,(
% 0.19/0.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f4])).
% 0.19/0.51  fof(f4,axiom,(
% 0.19/0.51    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.19/0.51  fof(f21,plain,(
% 0.19/0.51    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f3])).
% 0.19/0.51  fof(f3,axiom,(
% 0.19/0.51    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.19/0.51  fof(f28,plain,(
% 0.19/0.51    ( ! [X0,X1] : (X0 != X1 | ~r1_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.19/0.51    inference(cnf_transformation,[],[f16])).
% 0.19/0.51  fof(f16,plain,(
% 0.19/0.51    ! [X0,X1] : (X0 != X1 | ~r1_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 0.19/0.51    inference(ennf_transformation,[],[f6])).
% 0.19/0.51  fof(f6,axiom,(
% 0.19/0.51    ! [X0,X1] : ~(X0 = X1 & r1_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_zfmisc_1)).
% 0.19/0.51  fof(f125,plain,(
% 0.19/0.51    spl2_8 | ~spl2_2),
% 0.19/0.51    inference(avatar_split_clause,[],[f111,f54,f87])).
% 0.19/0.51  fof(f111,plain,(
% 0.19/0.51    k1_xboole_0 = k3_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl2_2),
% 0.19/0.51    inference(superposition,[],[f33,f55])).
% 0.19/0.51  fof(f33,plain,(
% 0.19/0.51    ( ! [X0,X1] : (k1_enumset1(X0,X0,X0) = k3_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X1))) )),
% 0.19/0.51    inference(definition_unfolding,[],[f24,f29,f29,f22])).
% 0.19/0.51  fof(f24,plain,(
% 0.19/0.51    ( ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 0.19/0.51    inference(cnf_transformation,[],[f7])).
% 0.19/0.51  fof(f7,axiom,(
% 0.19/0.51    ! [X0,X1] : k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_zfmisc_1)).
% 0.19/0.51  fof(f89,plain,(
% 0.19/0.51    spl2_8 | ~spl2_3),
% 0.19/0.51    inference(avatar_split_clause,[],[f68,f57,f87])).
% 0.19/0.51  fof(f57,plain,(
% 0.19/0.51    spl2_3 <=> k1_xboole_0 = k1_enumset1(sK1,sK1,sK1)),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.19/0.51  fof(f68,plain,(
% 0.19/0.51    k1_xboole_0 = k3_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl2_3),
% 0.19/0.51    inference(superposition,[],[f33,f58])).
% 0.19/0.51  fof(f58,plain,(
% 0.19/0.51    k1_xboole_0 = k1_enumset1(sK1,sK1,sK1) | ~spl2_3),
% 0.19/0.51    inference(avatar_component_clause,[],[f57])).
% 0.19/0.51  fof(f74,plain,(
% 0.19/0.51    ~spl2_4 | ~spl2_3),
% 0.19/0.51    inference(avatar_split_clause,[],[f64,f57,f72])).
% 0.19/0.51  fof(f64,plain,(
% 0.19/0.51    ~r1_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl2_3),
% 0.19/0.51    inference(superposition,[],[f37,f58])).
% 0.19/0.51  fof(f59,plain,(
% 0.19/0.51    spl2_2 | spl2_3 | spl2_1),
% 0.19/0.51    inference(avatar_split_clause,[],[f51,f39,f57,f54])).
% 0.19/0.51  fof(f39,plain,(
% 0.19/0.51    spl2_1 <=> k3_xboole_0(sK0,sK1) = k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.19/0.51  fof(f51,plain,(
% 0.19/0.51    k1_xboole_0 = k1_enumset1(sK1,sK1,sK1) | k1_xboole_0 = k1_enumset1(sK0,sK0,sK0) | spl2_1),
% 0.19/0.51    inference(trivial_inequality_removal,[],[f48])).
% 0.19/0.51  fof(f48,plain,(
% 0.19/0.51    k3_xboole_0(sK0,sK1) != k3_xboole_0(sK0,sK1) | k1_xboole_0 = k1_enumset1(sK1,sK1,sK1) | k1_xboole_0 = k1_enumset1(sK0,sK0,sK0) | spl2_1),
% 0.19/0.51    inference(superposition,[],[f40,f46])).
% 0.19/0.51  fof(f46,plain,(
% 0.19/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) | k1_xboole_0 = k1_enumset1(X1,X1,X1) | k1_xboole_0 = k1_enumset1(X0,X0,X0)) )),
% 0.19/0.51    inference(forward_demodulation,[],[f45,f32])).
% 0.19/0.51  fof(f32,plain,(
% 0.19/0.51    ( ! [X0] : (k1_setfam_1(k1_enumset1(X0,X0,X0)) = X0) )),
% 0.19/0.51    inference(definition_unfolding,[],[f20,f29])).
% 0.19/0.51  fof(f20,plain,(
% 0.19/0.51    ( ! [X0] : (k1_setfam_1(k1_tarski(X0)) = X0) )),
% 0.19/0.51    inference(cnf_transformation,[],[f9])).
% 0.19/0.51  fof(f9,axiom,(
% 0.19/0.51    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).
% 0.19/0.51  fof(f45,plain,(
% 0.19/0.51    ( ! [X0,X1] : (k1_setfam_1(k1_enumset1(X0,X0,X1)) = k3_xboole_0(k1_setfam_1(k1_enumset1(X0,X0,X0)),X1) | k1_xboole_0 = k1_enumset1(X1,X1,X1) | k1_xboole_0 = k1_enumset1(X0,X0,X0)) )),
% 0.19/0.51    inference(forward_demodulation,[],[f44,f32])).
% 0.19/0.51  fof(f44,plain,(
% 0.19/0.51    ( ! [X0,X1] : (k3_xboole_0(k1_setfam_1(k1_enumset1(X0,X0,X0)),k1_setfam_1(k1_enumset1(X1,X1,X1))) = k1_setfam_1(k1_enumset1(X0,X0,X1)) | k1_xboole_0 = k1_enumset1(X1,X1,X1) | k1_xboole_0 = k1_enumset1(X0,X0,X0)) )),
% 0.19/0.51    inference(superposition,[],[f35,f34])).
% 0.19/0.51  fof(f34,plain,(
% 0.19/0.51    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X1)))) )),
% 0.19/0.51    inference(definition_unfolding,[],[f25,f22,f30,f29,f29])).
% 0.19/0.51  fof(f30,plain,(
% 0.19/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 0.19/0.51    inference(definition_unfolding,[],[f23,f22])).
% 0.19/0.51  fof(f23,plain,(
% 0.19/0.51    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f5])).
% 0.19/0.51  fof(f5,axiom,(
% 0.19/0.51    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.19/0.51  fof(f25,plain,(
% 0.19/0.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.19/0.51    inference(cnf_transformation,[],[f2])).
% 0.19/0.51  fof(f2,axiom,(
% 0.19/0.51    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).
% 0.19/0.51  fof(f35,plain,(
% 0.19/0.51    ( ! [X0,X1] : (k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) = k1_setfam_1(k3_tarski(k1_enumset1(X0,X0,X1))) | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.19/0.51    inference(definition_unfolding,[],[f27,f30])).
% 0.19/0.51  fof(f27,plain,(
% 0.19/0.51    ( ! [X0,X1] : (k1_setfam_1(k2_xboole_0(X0,X1)) = k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.19/0.51    inference(cnf_transformation,[],[f15])).
% 0.19/0.51  fof(f15,plain,(
% 0.19/0.51    ! [X0,X1] : (k1_setfam_1(k2_xboole_0(X0,X1)) = k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.19/0.51    inference(ennf_transformation,[],[f8])).
% 0.19/0.51  fof(f8,axiom,(
% 0.19/0.51    ! [X0,X1] : ~(k1_setfam_1(k2_xboole_0(X0,X1)) != k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_setfam_1)).
% 0.19/0.51  fof(f40,plain,(
% 0.19/0.51    k3_xboole_0(sK0,sK1) != k1_setfam_1(k1_enumset1(sK0,sK0,sK1)) | spl2_1),
% 0.19/0.51    inference(avatar_component_clause,[],[f39])).
% 0.19/0.51  fof(f41,plain,(
% 0.19/0.51    ~spl2_1),
% 0.19/0.51    inference(avatar_split_clause,[],[f31,f39])).
% 0.19/0.51  fof(f31,plain,(
% 0.19/0.51    k3_xboole_0(sK0,sK1) != k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),
% 0.19/0.51    inference(definition_unfolding,[],[f19,f22])).
% 0.19/0.51  fof(f19,plain,(
% 0.19/0.51    k3_xboole_0(sK0,sK1) != k1_setfam_1(k2_tarski(sK0,sK1))),
% 0.19/0.51    inference(cnf_transformation,[],[f18])).
% 0.19/0.51  fof(f18,plain,(
% 0.19/0.51    k3_xboole_0(sK0,sK1) != k1_setfam_1(k2_tarski(sK0,sK1))),
% 0.19/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f17])).
% 0.19/0.51  fof(f17,plain,(
% 0.19/0.51    ? [X0,X1] : k3_xboole_0(X0,X1) != k1_setfam_1(k2_tarski(X0,X1)) => k3_xboole_0(sK0,sK1) != k1_setfam_1(k2_tarski(sK0,sK1))),
% 0.19/0.51    introduced(choice_axiom,[])).
% 0.19/0.51  fof(f13,plain,(
% 0.19/0.51    ? [X0,X1] : k3_xboole_0(X0,X1) != k1_setfam_1(k2_tarski(X0,X1))),
% 0.19/0.51    inference(ennf_transformation,[],[f11])).
% 0.19/0.51  fof(f11,negated_conjecture,(
% 0.19/0.51    ~! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.19/0.51    inference(negated_conjecture,[],[f10])).
% 0.19/0.51  fof(f10,conjecture,(
% 0.19/0.51    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.19/0.51  % SZS output end Proof for theBenchmark
% 0.19/0.51  % (23983)------------------------------
% 0.19/0.51  % (23983)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.51  % (23983)Termination reason: Refutation
% 0.19/0.51  
% 0.19/0.51  % (23983)Memory used [KB]: 10746
% 0.19/0.51  % (23983)Time elapsed: 0.117 s
% 0.19/0.51  % (23983)------------------------------
% 0.19/0.51  % (23983)------------------------------
% 0.19/0.51  % (23984)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.19/0.51  % (23963)Success in time 0.165 s
%------------------------------------------------------------------------------
