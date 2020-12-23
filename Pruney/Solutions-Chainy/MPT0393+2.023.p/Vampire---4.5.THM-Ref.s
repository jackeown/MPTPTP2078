%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:54 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 237 expanded)
%              Number of leaves         :   18 (  80 expanded)
%              Depth                    :   13
%              Number of atoms          :  168 ( 422 expanded)
%              Number of equality atoms :   52 ( 204 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1986,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f84,f107,f733,f1365,f1624,f1627,f1936,f1945])).

fof(f1945,plain,
    ( ~ spl5_100
    | ~ spl5_35 ),
    inference(avatar_split_clause,[],[f1889,f730,f1933])).

fof(f1933,plain,
    ( spl5_100
  <=> r2_hidden(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_100])])).

fof(f730,plain,
    ( spl5_35
  <=> k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).

fof(f1889,plain,
    ( ~ r2_hidden(sK0,sK0)
    | ~ spl5_35 ),
    inference(backward_demodulation,[],[f1637,f1836])).

fof(f1836,plain,
    ( ! [X0] : sK0 = X0
    | ~ spl5_35 ),
    inference(resolution,[],[f1776,f69])).

fof(f69,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k2_enumset1(X0,X0,X0,X0))
      | X0 = X2 ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f32,f49])).

fof(f49,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f20,f48])).

fof(f48,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f21,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f21,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f20,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f1776,plain,
    ( ! [X2] : r2_hidden(sK0,k2_enumset1(X2,X2,X2,X2))
    | ~ spl5_35 ),
    inference(resolution,[],[f1639,f73])).

fof(f73,plain,(
    ! [X1] : r1_tarski(k1_xboole_0,k2_enumset1(X1,X1,X1,X1)) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | r1_tarski(X0,k2_enumset1(X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f36,f49])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f1639,plain,
    ( ! [X5] :
        ( ~ r1_tarski(k1_xboole_0,X5)
        | r2_hidden(sK0,X5) )
    | ~ spl5_35 ),
    inference(superposition,[],[f108,f732])).

fof(f732,plain,
    ( k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)
    | ~ spl5_35 ),
    inference(avatar_component_clause,[],[f730])).

fof(f108,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_enumset1(X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f28,f71])).

fof(f71,plain,(
    ! [X2] : r2_hidden(X2,k2_enumset1(X2,X2,X2,X2)) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X2,X1] :
      ( r2_hidden(X2,X1)
      | k2_enumset1(X2,X2,X2,X2) != X1 ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | r2_hidden(X2,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f31,f49])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f1637,plain,
    ( ! [X4] : ~ r2_hidden(sK0,k4_xboole_0(X4,k1_xboole_0))
    | ~ spl5_35 ),
    inference(superposition,[],[f79,f732])).

fof(f79,plain,(
    ! [X2,X1] : ~ r2_hidden(X2,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2))) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2))) ) ),
    inference(definition_unfolding,[],[f46,f49])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(f1936,plain,
    ( spl5_100
    | ~ spl5_35 ),
    inference(avatar_split_clause,[],[f1876,f730,f1933])).

fof(f1876,plain,
    ( r2_hidden(sK0,sK0)
    | ~ spl5_35 ),
    inference(backward_demodulation,[],[f1776,f1836])).

fof(f1627,plain,(
    spl5_77 ),
    inference(avatar_contradiction_clause,[],[f1626])).

fof(f1626,plain,
    ( $false
    | spl5_77 ),
    inference(resolution,[],[f1623,f67])).

fof(f67,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f1623,plain,
    ( ~ r1_tarski(sK0,sK0)
    | spl5_77 ),
    inference(avatar_component_clause,[],[f1621])).

fof(f1621,plain,
    ( spl5_77
  <=> r1_tarski(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_77])])).

fof(f1624,plain,
    ( spl5_3
    | spl5_35
    | ~ spl5_77
    | ~ spl5_34 ),
    inference(avatar_split_clause,[],[f1618,f726,f1621,f730,f101])).

fof(f101,plain,
    ( spl5_3
  <=> r1_tarski(sK0,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f726,plain,
    ( spl5_34
  <=> sK0 = sK1(k2_enumset1(sK0,sK0,sK0,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).

fof(f1618,plain,
    ( ~ r1_tarski(sK0,sK0)
    | k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)
    | r1_tarski(sK0,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0)))
    | ~ spl5_34 ),
    inference(superposition,[],[f24,f728])).

fof(f728,plain,
    ( sK0 = sK1(k2_enumset1(sK0,sK0,sK0,sK0),sK0)
    | ~ spl5_34 ),
    inference(avatar_component_clause,[],[f726])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,sK1(X0,X1))
      | k1_xboole_0 = X0
      | r1_tarski(X1,k1_setfam_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) ) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_tarski(X1,X2) )
     => ( r1_tarski(X1,k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_setfam_1)).

fof(f1365,plain,
    ( ~ spl5_3
    | ~ spl5_2
    | spl5_1 ),
    inference(avatar_split_clause,[],[f1363,f81,f97,f101])).

fof(f97,plain,
    ( spl5_2
  <=> r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f81,plain,
    ( spl5_1
  <=> sK0 = k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f1363,plain,
    ( ~ r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0)),sK0)
    | ~ r1_tarski(sK0,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0)))
    | spl5_1 ),
    inference(extensionality_resolution,[],[f27,f83])).

fof(f83,plain,
    ( sK0 != k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f81])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f733,plain,
    ( spl5_34
    | spl5_35
    | spl5_3 ),
    inference(avatar_split_clause,[],[f722,f101,f730,f726])).

fof(f722,plain,
    ( k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)
    | sK0 = sK1(k2_enumset1(sK0,sK0,sK0,sK0),sK0)
    | spl5_3 ),
    inference(resolution,[],[f135,f103])).

fof(f103,plain,
    ( ~ r1_tarski(sK0,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0)))
    | spl5_3 ),
    inference(avatar_component_clause,[],[f101])).

fof(f135,plain,(
    ! [X6,X5] :
      ( r1_tarski(X6,k1_setfam_1(k2_enumset1(X5,X5,X5,X5)))
      | k1_xboole_0 = k2_enumset1(X5,X5,X5,X5)
      | sK1(k2_enumset1(X5,X5,X5,X5),X6) = X5 ) ),
    inference(resolution,[],[f23,f69])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X0)
      | k1_xboole_0 = X0
      | r1_tarski(X1,k1_setfam_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f107,plain,(
    spl5_2 ),
    inference(avatar_contradiction_clause,[],[f106])).

fof(f106,plain,
    ( $false
    | spl5_2 ),
    inference(resolution,[],[f99,f85])).

fof(f85,plain,(
    ! [X0] : r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X0)),X0) ),
    inference(resolution,[],[f71,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k1_setfam_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(k1_setfam_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_setfam_1)).

fof(f99,plain,
    ( ~ r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0)),sK0)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f97])).

fof(f84,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f50,f81])).

fof(f50,plain,(
    sK0 != k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(definition_unfolding,[],[f19,f49])).

fof(f19,plain,(
    sK0 != k1_setfam_1(k1_tarski(sK0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0 ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:54:29 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.22/0.49  % (16628)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.49  % (16636)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.49  % (16620)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.49  % (16620)Refutation not found, incomplete strategy% (16620)------------------------------
% 0.22/0.49  % (16620)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (16619)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.49  % (16620)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (16620)Memory used [KB]: 10618
% 0.22/0.49  % (16620)Time elapsed: 0.080 s
% 0.22/0.49  % (16620)------------------------------
% 0.22/0.49  % (16620)------------------------------
% 0.22/0.49  % (16616)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.50  % (16624)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.51  % (16614)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.51  % (16618)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.51  % (16627)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.51  % (16640)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.51  % (16614)Refutation not found, incomplete strategy% (16614)------------------------------
% 0.22/0.51  % (16614)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (16614)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (16614)Memory used [KB]: 10618
% 0.22/0.51  % (16614)Time elapsed: 0.100 s
% 0.22/0.51  % (16614)------------------------------
% 0.22/0.51  % (16614)------------------------------
% 0.22/0.52  % (16634)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.52  % (16622)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.52  % (16631)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.52  % (16625)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.52  % (16617)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.52  % (16630)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.52  % (16615)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.52  % (16635)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.52  % (16635)Refutation not found, incomplete strategy% (16635)------------------------------
% 0.22/0.52  % (16635)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (16635)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (16635)Memory used [KB]: 1791
% 0.22/0.52  % (16635)Time elapsed: 0.120 s
% 0.22/0.52  % (16635)------------------------------
% 0.22/0.52  % (16635)------------------------------
% 0.22/0.52  % (16621)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.52  % (16639)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.53  % (16626)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.53  % (16637)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.53  % (16638)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.53  % (16641)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.53  % (16632)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.53  % (16629)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.53  % (16632)Refutation not found, incomplete strategy% (16632)------------------------------
% 0.22/0.53  % (16632)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (16632)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (16632)Memory used [KB]: 10746
% 0.22/0.53  % (16632)Time elapsed: 0.121 s
% 0.22/0.53  % (16632)------------------------------
% 0.22/0.53  % (16632)------------------------------
% 0.22/0.53  % (16623)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.53  % (16633)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.54  % (16633)Refutation not found, incomplete strategy% (16633)------------------------------
% 0.22/0.54  % (16633)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (16633)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (16633)Memory used [KB]: 1663
% 0.22/0.54  % (16633)Time elapsed: 0.133 s
% 0.22/0.54  % (16633)------------------------------
% 0.22/0.54  % (16633)------------------------------
% 0.22/0.54  % (16623)Refutation not found, incomplete strategy% (16623)------------------------------
% 0.22/0.54  % (16623)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (16623)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (16623)Memory used [KB]: 10746
% 0.22/0.54  % (16623)Time elapsed: 0.134 s
% 0.22/0.54  % (16623)------------------------------
% 0.22/0.54  % (16623)------------------------------
% 0.22/0.54  % (16612)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.54  % (16612)Refutation not found, incomplete strategy% (16612)------------------------------
% 0.22/0.54  % (16612)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (16612)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (16612)Memory used [KB]: 1663
% 0.22/0.54  % (16612)Time elapsed: 0.117 s
% 0.22/0.54  % (16612)------------------------------
% 0.22/0.54  % (16612)------------------------------
% 0.22/0.54  % (16622)Refutation not found, incomplete strategy% (16622)------------------------------
% 0.22/0.54  % (16622)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (16622)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (16622)Memory used [KB]: 10618
% 0.22/0.54  % (16622)Time elapsed: 0.132 s
% 0.22/0.54  % (16622)------------------------------
% 0.22/0.54  % (16622)------------------------------
% 0.22/0.54  % (16613)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.57  % (16628)Refutation found. Thanks to Tanya!
% 0.22/0.57  % SZS status Theorem for theBenchmark
% 0.22/0.57  % SZS output start Proof for theBenchmark
% 0.22/0.57  fof(f1986,plain,(
% 0.22/0.57    $false),
% 0.22/0.57    inference(avatar_sat_refutation,[],[f84,f107,f733,f1365,f1624,f1627,f1936,f1945])).
% 0.22/0.57  fof(f1945,plain,(
% 0.22/0.57    ~spl5_100 | ~spl5_35),
% 0.22/0.57    inference(avatar_split_clause,[],[f1889,f730,f1933])).
% 0.22/0.57  fof(f1933,plain,(
% 0.22/0.57    spl5_100 <=> r2_hidden(sK0,sK0)),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_100])])).
% 0.22/0.57  fof(f730,plain,(
% 0.22/0.57    spl5_35 <=> k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).
% 0.22/0.57  fof(f1889,plain,(
% 0.22/0.57    ~r2_hidden(sK0,sK0) | ~spl5_35),
% 0.22/0.57    inference(backward_demodulation,[],[f1637,f1836])).
% 0.22/0.57  fof(f1836,plain,(
% 0.22/0.57    ( ! [X0] : (sK0 = X0) ) | ~spl5_35),
% 0.22/0.57    inference(resolution,[],[f1776,f69])).
% 0.22/0.57  fof(f69,plain,(
% 0.22/0.57    ( ! [X2,X0] : (~r2_hidden(X2,k2_enumset1(X0,X0,X0,X0)) | X0 = X2) )),
% 0.22/0.57    inference(equality_resolution,[],[f53])).
% 0.22/0.57  fof(f53,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 0.22/0.57    inference(definition_unfolding,[],[f32,f49])).
% 0.22/0.57  fof(f49,plain,(
% 0.22/0.57    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.22/0.57    inference(definition_unfolding,[],[f20,f48])).
% 0.22/0.57  fof(f48,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.22/0.57    inference(definition_unfolding,[],[f21,f38])).
% 0.22/0.57  fof(f38,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f7])).
% 0.22/0.57  fof(f7,axiom,(
% 0.22/0.57    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.57  fof(f21,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f6])).
% 0.22/0.57  fof(f6,axiom,(
% 0.22/0.57    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.57  fof(f20,plain,(
% 0.22/0.57    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f5])).
% 0.22/0.57  fof(f5,axiom,(
% 0.22/0.57    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.57  fof(f32,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 0.22/0.57    inference(cnf_transformation,[],[f3])).
% 0.22/0.57  fof(f3,axiom,(
% 0.22/0.57    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 0.22/0.57  fof(f1776,plain,(
% 0.22/0.57    ( ! [X2] : (r2_hidden(sK0,k2_enumset1(X2,X2,X2,X2))) ) | ~spl5_35),
% 0.22/0.57    inference(resolution,[],[f1639,f73])).
% 0.22/0.57  fof(f73,plain,(
% 0.22/0.57    ( ! [X1] : (r1_tarski(k1_xboole_0,k2_enumset1(X1,X1,X1,X1))) )),
% 0.22/0.57    inference(equality_resolution,[],[f56])).
% 0.22/0.57  fof(f56,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k1_xboole_0 != X0 | r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))) )),
% 0.22/0.57    inference(definition_unfolding,[],[f36,f49])).
% 0.22/0.57  fof(f36,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k1_xboole_0 != X0 | r1_tarski(X0,k1_tarski(X1))) )),
% 0.22/0.57    inference(cnf_transformation,[],[f8])).
% 0.22/0.57  fof(f8,axiom,(
% 0.22/0.57    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 0.22/0.57  fof(f1639,plain,(
% 0.22/0.57    ( ! [X5] : (~r1_tarski(k1_xboole_0,X5) | r2_hidden(sK0,X5)) ) | ~spl5_35),
% 0.22/0.57    inference(superposition,[],[f108,f732])).
% 0.22/0.57  fof(f732,plain,(
% 0.22/0.57    k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) | ~spl5_35),
% 0.22/0.57    inference(avatar_component_clause,[],[f730])).
% 0.22/0.57  fof(f108,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~r1_tarski(k2_enumset1(X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 0.22/0.57    inference(resolution,[],[f28,f71])).
% 0.22/0.57  fof(f71,plain,(
% 0.22/0.57    ( ! [X2] : (r2_hidden(X2,k2_enumset1(X2,X2,X2,X2))) )),
% 0.22/0.57    inference(equality_resolution,[],[f70])).
% 0.22/0.57  fof(f70,plain,(
% 0.22/0.57    ( ! [X2,X1] : (r2_hidden(X2,X1) | k2_enumset1(X2,X2,X2,X2) != X1) )),
% 0.22/0.57    inference(equality_resolution,[],[f54])).
% 0.22/0.57  fof(f54,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (X0 != X2 | r2_hidden(X2,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 0.22/0.57    inference(definition_unfolding,[],[f31,f49])).
% 0.22/0.57  fof(f31,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (X0 != X2 | r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 0.22/0.57    inference(cnf_transformation,[],[f3])).
% 0.22/0.57  fof(f28,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f18])).
% 0.22/0.57  fof(f18,plain,(
% 0.22/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.22/0.57    inference(ennf_transformation,[],[f1])).
% 0.22/0.57  fof(f1,axiom,(
% 0.22/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.57  fof(f1637,plain,(
% 0.22/0.57    ( ! [X4] : (~r2_hidden(sK0,k4_xboole_0(X4,k1_xboole_0))) ) | ~spl5_35),
% 0.22/0.57    inference(superposition,[],[f79,f732])).
% 0.22/0.57  fof(f79,plain,(
% 0.22/0.57    ( ! [X2,X1] : (~r2_hidden(X2,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)))) )),
% 0.22/0.57    inference(equality_resolution,[],[f65])).
% 0.22/0.57  fof(f65,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)))) )),
% 0.22/0.57    inference(definition_unfolding,[],[f46,f49])).
% 0.22/0.57  fof(f46,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 0.22/0.57    inference(cnf_transformation,[],[f9])).
% 0.22/0.57  fof(f9,axiom,(
% 0.22/0.57    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).
% 0.22/0.57  fof(f1936,plain,(
% 0.22/0.57    spl5_100 | ~spl5_35),
% 0.22/0.57    inference(avatar_split_clause,[],[f1876,f730,f1933])).
% 0.22/0.57  fof(f1876,plain,(
% 0.22/0.57    r2_hidden(sK0,sK0) | ~spl5_35),
% 0.22/0.57    inference(backward_demodulation,[],[f1776,f1836])).
% 0.22/0.57  fof(f1627,plain,(
% 0.22/0.57    spl5_77),
% 0.22/0.57    inference(avatar_contradiction_clause,[],[f1626])).
% 0.22/0.57  fof(f1626,plain,(
% 0.22/0.57    $false | spl5_77),
% 0.22/0.57    inference(resolution,[],[f1623,f67])).
% 0.22/0.57  fof(f67,plain,(
% 0.22/0.57    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.22/0.57    inference(equality_resolution,[],[f26])).
% 0.22/0.57  fof(f26,plain,(
% 0.22/0.57    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.22/0.57    inference(cnf_transformation,[],[f2])).
% 0.22/0.57  fof(f2,axiom,(
% 0.22/0.57    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.57  fof(f1623,plain,(
% 0.22/0.57    ~r1_tarski(sK0,sK0) | spl5_77),
% 0.22/0.57    inference(avatar_component_clause,[],[f1621])).
% 0.22/0.57  fof(f1621,plain,(
% 0.22/0.57    spl5_77 <=> r1_tarski(sK0,sK0)),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_77])])).
% 0.22/0.57  fof(f1624,plain,(
% 0.22/0.57    spl5_3 | spl5_35 | ~spl5_77 | ~spl5_34),
% 0.22/0.57    inference(avatar_split_clause,[],[f1618,f726,f1621,f730,f101])).
% 0.22/0.57  fof(f101,plain,(
% 0.22/0.57    spl5_3 <=> r1_tarski(sK0,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0)))),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.22/0.57  fof(f726,plain,(
% 0.22/0.57    spl5_34 <=> sK0 = sK1(k2_enumset1(sK0,sK0,sK0,sK0),sK0)),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).
% 0.22/0.57  fof(f1618,plain,(
% 0.22/0.57    ~r1_tarski(sK0,sK0) | k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) | r1_tarski(sK0,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0))) | ~spl5_34),
% 0.22/0.57    inference(superposition,[],[f24,f728])).
% 0.22/0.57  fof(f728,plain,(
% 0.22/0.57    sK0 = sK1(k2_enumset1(sK0,sK0,sK0,sK0),sK0) | ~spl5_34),
% 0.22/0.57    inference(avatar_component_clause,[],[f726])).
% 0.22/0.57  fof(f24,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~r1_tarski(X1,sK1(X0,X1)) | k1_xboole_0 = X0 | r1_tarski(X1,k1_setfam_1(X0))) )),
% 0.22/0.57    inference(cnf_transformation,[],[f17])).
% 0.22/0.57  fof(f17,plain,(
% 0.22/0.57    ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | ? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)))),
% 0.22/0.57    inference(flattening,[],[f16])).
% 0.22/0.57  fof(f16,plain,(
% 0.22/0.57    ! [X0,X1] : ((r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0) | ? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)))),
% 0.22/0.57    inference(ennf_transformation,[],[f11])).
% 0.22/0.57  fof(f11,axiom,(
% 0.22/0.57    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r1_tarski(X1,X2)) => (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_setfam_1)).
% 0.22/0.57  fof(f1365,plain,(
% 0.22/0.57    ~spl5_3 | ~spl5_2 | spl5_1),
% 0.22/0.57    inference(avatar_split_clause,[],[f1363,f81,f97,f101])).
% 0.22/0.57  fof(f97,plain,(
% 0.22/0.57    spl5_2 <=> r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0)),sK0)),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.22/0.57  fof(f81,plain,(
% 0.22/0.57    spl5_1 <=> sK0 = k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0))),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.22/0.57  fof(f1363,plain,(
% 0.22/0.57    ~r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0)),sK0) | ~r1_tarski(sK0,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0))) | spl5_1),
% 0.22/0.57    inference(extensionality_resolution,[],[f27,f83])).
% 0.22/0.57  fof(f83,plain,(
% 0.22/0.57    sK0 != k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0)) | spl5_1),
% 0.22/0.57    inference(avatar_component_clause,[],[f81])).
% 0.22/0.57  fof(f27,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.22/0.57    inference(cnf_transformation,[],[f2])).
% 0.22/0.57  fof(f733,plain,(
% 0.22/0.57    spl5_34 | spl5_35 | spl5_3),
% 0.22/0.57    inference(avatar_split_clause,[],[f722,f101,f730,f726])).
% 0.22/0.57  fof(f722,plain,(
% 0.22/0.57    k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) | sK0 = sK1(k2_enumset1(sK0,sK0,sK0,sK0),sK0) | spl5_3),
% 0.22/0.57    inference(resolution,[],[f135,f103])).
% 0.22/0.57  fof(f103,plain,(
% 0.22/0.57    ~r1_tarski(sK0,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0))) | spl5_3),
% 0.22/0.57    inference(avatar_component_clause,[],[f101])).
% 0.22/0.57  fof(f135,plain,(
% 0.22/0.57    ( ! [X6,X5] : (r1_tarski(X6,k1_setfam_1(k2_enumset1(X5,X5,X5,X5))) | k1_xboole_0 = k2_enumset1(X5,X5,X5,X5) | sK1(k2_enumset1(X5,X5,X5,X5),X6) = X5) )),
% 0.22/0.57    inference(resolution,[],[f23,f69])).
% 0.22/0.57  fof(f23,plain,(
% 0.22/0.57    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X0) | k1_xboole_0 = X0 | r1_tarski(X1,k1_setfam_1(X0))) )),
% 0.22/0.57    inference(cnf_transformation,[],[f17])).
% 0.22/0.57  fof(f107,plain,(
% 0.22/0.57    spl5_2),
% 0.22/0.57    inference(avatar_contradiction_clause,[],[f106])).
% 0.22/0.57  fof(f106,plain,(
% 0.22/0.57    $false | spl5_2),
% 0.22/0.57    inference(resolution,[],[f99,f85])).
% 0.22/0.57  fof(f85,plain,(
% 0.22/0.57    ( ! [X0] : (r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X0)),X0)) )),
% 0.22/0.57    inference(resolution,[],[f71,f22])).
% 0.22/0.57  fof(f22,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k1_setfam_1(X1),X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f15])).
% 0.22/0.57  fof(f15,plain,(
% 0.22/0.57    ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),X0) | ~r2_hidden(X0,X1))),
% 0.22/0.57    inference(ennf_transformation,[],[f10])).
% 0.22/0.57  fof(f10,axiom,(
% 0.22/0.57    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(k1_setfam_1(X1),X0))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_setfam_1)).
% 0.22/0.57  fof(f99,plain,(
% 0.22/0.57    ~r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0)),sK0) | spl5_2),
% 0.22/0.57    inference(avatar_component_clause,[],[f97])).
% 0.22/0.57  fof(f84,plain,(
% 0.22/0.57    ~spl5_1),
% 0.22/0.57    inference(avatar_split_clause,[],[f50,f81])).
% 0.22/0.57  fof(f50,plain,(
% 0.22/0.57    sK0 != k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0))),
% 0.22/0.57    inference(definition_unfolding,[],[f19,f49])).
% 0.22/0.57  fof(f19,plain,(
% 0.22/0.57    sK0 != k1_setfam_1(k1_tarski(sK0))),
% 0.22/0.57    inference(cnf_transformation,[],[f14])).
% 0.22/0.57  fof(f14,plain,(
% 0.22/0.57    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0),
% 0.22/0.57    inference(ennf_transformation,[],[f13])).
% 0.22/0.57  fof(f13,negated_conjecture,(
% 0.22/0.57    ~! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 0.22/0.57    inference(negated_conjecture,[],[f12])).
% 0.22/0.57  fof(f12,conjecture,(
% 0.22/0.57    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).
% 0.22/0.57  % SZS output end Proof for theBenchmark
% 0.22/0.57  % (16628)------------------------------
% 0.22/0.57  % (16628)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (16628)Termination reason: Refutation
% 0.22/0.57  
% 0.22/0.57  % (16628)Memory used [KB]: 11769
% 0.22/0.57  % (16628)Time elapsed: 0.170 s
% 0.22/0.57  % (16628)------------------------------
% 0.22/0.57  % (16628)------------------------------
% 1.62/0.58  % (16611)Success in time 0.22 s
%------------------------------------------------------------------------------
