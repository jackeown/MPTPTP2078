%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:32 EST 2020

% Result     : Theorem 1.39s
% Output     : Refutation 1.39s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 160 expanded)
%              Number of leaves         :   14 (  65 expanded)
%              Depth                    :    8
%              Number of atoms          :  207 ( 405 expanded)
%              Number of equality atoms :   88 ( 227 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f189,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f39,f46,f59,f71,f75,f90,f104,f115,f146,f147,f153,f155,f156,f171,f188])).

fof(f188,plain,
    ( spl3_3
    | ~ spl3_5 ),
    inference(avatar_contradiction_clause,[],[f183])).

fof(f183,plain,
    ( $false
    | spl3_3
    | ~ spl3_5 ),
    inference(unit_resulting_resolution,[],[f45,f179])).

fof(f179,plain,
    ( ! [X2] : r1_tarski(sK0,k2_tarski(X2,sK2))
    | ~ spl3_5 ),
    inference(superposition,[],[f28,f54])).

fof(f54,plain,
    ( sK0 = k2_tarski(sK2,sK2)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f52])).

fof(f52,plain,
    ( spl3_5
  <=> sK0 = k2_tarski(sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f28,plain,(
    ! [X2,X1] : r1_tarski(k2_tarski(X2,X2),k2_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X2,X2) != X0
      | r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(definition_unfolding,[],[f19,f13])).

fof(f13,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X2) != X0
      | r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).

fof(f45,plain,
    ( ~ r1_tarski(sK0,k2_tarski(sK1,sK2))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f43])).

fof(f43,plain,
    ( spl3_3
  <=> r1_tarski(sK0,k2_tarski(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f171,plain,
    ( spl3_3
    | ~ spl3_6 ),
    inference(avatar_contradiction_clause,[],[f166])).

fof(f166,plain,
    ( $false
    | spl3_3
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f45,f163])).

fof(f163,plain,
    ( ! [X1] : r1_tarski(sK0,k2_tarski(sK1,X1))
    | ~ spl3_6 ),
    inference(superposition,[],[f29,f58])).

fof(f58,plain,
    ( sK0 = k2_tarski(sK1,sK1)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl3_6
  <=> sK0 = k2_tarski(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f29,plain,(
    ! [X2,X1] : r1_tarski(k2_tarski(X1,X1),k2_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X1,X1) != X0
      | r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(definition_unfolding,[],[f18,f13])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X1) != X0
      | r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f156,plain,
    ( ~ spl3_1
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f23,f56,f32])).

fof(f32,plain,
    ( spl3_1
  <=> k1_xboole_0 = k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f23,plain,
    ( sK0 != k2_tarski(sK1,sK1)
    | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ),
    inference(definition_unfolding,[],[f9,f13])).

fof(f9,plain,
    ( sK0 != k1_tarski(sK1)
    | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2))
    <~> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2))
      <=> ~ ( k2_tarski(X1,X2) != X0
            & k1_tarski(X2) != X0
            & k1_tarski(X1) != X0
            & k1_xboole_0 != X0 ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_zfmisc_1)).

fof(f155,plain,
    ( spl3_2
    | ~ spl3_3
    | spl3_4
    | spl3_5
    | spl3_6 ),
    inference(avatar_contradiction_clause,[],[f154])).

fof(f154,plain,
    ( $false
    | spl3_2
    | ~ spl3_3
    | spl3_4
    | spl3_5
    | spl3_6 ),
    inference(unit_resulting_resolution,[],[f38,f49,f44,f57,f53,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_tarski(X1,X2))
      | k2_tarski(X1,X1) = X0
      | k2_tarski(X2,X2) = X0
      | k2_tarski(X1,X2) = X0
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f16,f13,f13])).

fof(f16,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | k1_tarski(X1) = X0
      | k1_tarski(X2) = X0
      | k2_tarski(X1,X2) = X0
      | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f53,plain,
    ( sK0 != k2_tarski(sK2,sK2)
    | spl3_5 ),
    inference(avatar_component_clause,[],[f52])).

fof(f57,plain,
    ( sK0 != k2_tarski(sK1,sK1)
    | spl3_6 ),
    inference(avatar_component_clause,[],[f56])).

fof(f44,plain,
    ( r1_tarski(sK0,k2_tarski(sK1,sK2))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f43])).

fof(f49,plain,
    ( sK0 != k2_tarski(sK1,sK2)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f48])).

fof(f48,plain,
    ( spl3_4
  <=> sK0 = k2_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f38,plain,
    ( k1_xboole_0 != sK0
    | spl3_2 ),
    inference(avatar_component_clause,[],[f36])).

fof(f36,plain,
    ( spl3_2
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f153,plain,
    ( ~ spl3_1
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f22,f52,f32])).

fof(f22,plain,
    ( sK0 != k2_tarski(sK2,sK2)
    | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ),
    inference(definition_unfolding,[],[f10,f13])).

fof(f10,plain,
    ( sK0 != k1_tarski(sK2)
    | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f147,plain,
    ( spl3_3
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f102,f32,f43])).

fof(f102,plain,
    ( r1_tarski(sK0,k2_tarski(sK1,sK2))
    | ~ spl3_1 ),
    inference(trivial_inequality_removal,[],[f101])).

fof(f101,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK0,k2_tarski(sK1,sK2))
    | ~ spl3_1 ),
    inference(superposition,[],[f15,f33])).

fof(f33,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k2_tarski(sK1,sK2))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f32])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k1_xboole_0
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f146,plain,
    ( ~ spl3_11
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f145,f48,f112])).

fof(f112,plain,
    ( spl3_11
  <=> k1_xboole_0 = k4_xboole_0(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f145,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,sK0)
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f144,f50])).

fof(f50,plain,
    ( sK0 = k2_tarski(sK1,sK2)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f48])).

fof(f144,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2))
    | ~ spl3_4 ),
    inference(trivial_inequality_removal,[],[f143])).

fof(f143,plain,
    ( sK0 != sK0
    | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2))
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f11,f50])).

fof(f11,plain,
    ( sK0 != k2_tarski(sK1,sK2)
    | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f115,plain,
    ( spl3_11
    | ~ spl3_1
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f105,f48,f32,f112])).

fof(f105,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK0)
    | ~ spl3_1
    | ~ spl3_4 ),
    inference(backward_demodulation,[],[f33,f50])).

fof(f104,plain,
    ( sK0 != k2_tarski(sK1,sK2)
    | r1_tarski(sK0,k2_tarski(sK1,sK2))
    | ~ r1_tarski(sK0,sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f90,plain,
    ( spl3_10
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f80,f48,f87])).

fof(f87,plain,
    ( spl3_10
  <=> r1_tarski(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f80,plain,
    ( r1_tarski(sK0,sK0)
    | ~ spl3_4 ),
    inference(superposition,[],[f27,f50])).

fof(f27,plain,(
    ! [X2,X1] : r1_tarski(k2_tarski(X1,X2),k2_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f20])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X1,X2) != X0
      | r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f75,plain,(
    spl3_8 ),
    inference(avatar_contradiction_clause,[],[f72])).

fof(f72,plain,
    ( $false
    | spl3_8 ),
    inference(unit_resulting_resolution,[],[f30,f70])).

fof(f70,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_tarski(sK1,sK2))
    | spl3_8 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl3_8
  <=> r1_tarski(k1_xboole_0,k2_tarski(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f30,plain,(
    ! [X2,X1] : r1_tarski(k1_xboole_0,k2_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f17])).

fof(f17,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != X0
      | r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f71,plain,
    ( ~ spl3_8
    | ~ spl3_2
    | spl3_3 ),
    inference(avatar_split_clause,[],[f60,f43,f36,f68])).

fof(f60,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_tarski(sK1,sK2))
    | ~ spl3_2
    | spl3_3 ),
    inference(backward_demodulation,[],[f45,f37])).

fof(f37,plain,
    ( k1_xboole_0 = sK0
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f36])).

fof(f59,plain,
    ( spl3_1
    | spl3_4
    | spl3_5
    | spl3_6
    | spl3_2 ),
    inference(avatar_split_clause,[],[f21,f36,f56,f52,f48,f32])).

fof(f21,plain,
    ( k1_xboole_0 = sK0
    | sK0 = k2_tarski(sK1,sK1)
    | sK0 = k2_tarski(sK2,sK2)
    | sK0 = k2_tarski(sK1,sK2)
    | k1_xboole_0 = k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ),
    inference(definition_unfolding,[],[f12,f13,f13])).

fof(f12,plain,
    ( k1_xboole_0 = sK0
    | sK0 = k1_tarski(sK1)
    | sK0 = k1_tarski(sK2)
    | sK0 = k2_tarski(sK1,sK2)
    | k1_xboole_0 = k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f46,plain,
    ( ~ spl3_3
    | spl3_1 ),
    inference(avatar_split_clause,[],[f41,f32,f43])).

fof(f41,plain,
    ( ~ r1_tarski(sK0,k2_tarski(sK1,sK2))
    | spl3_1 ),
    inference(trivial_inequality_removal,[],[f40])).

fof(f40,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r1_tarski(sK0,k2_tarski(sK1,sK2))
    | spl3_1 ),
    inference(superposition,[],[f34,f14])).

% (29905)Termination reason: Refutation not found, incomplete strategy

% (29905)Memory used [KB]: 10618
% (29905)Time elapsed: 0.124 s
% (29905)------------------------------
% (29905)------------------------------
% (29913)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% (29907)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% (29908)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% (29896)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% (29888)Refutation not found, incomplete strategy% (29888)------------------------------
% (29888)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (29888)Termination reason: Refutation not found, incomplete strategy

% (29888)Memory used [KB]: 10746
% (29888)Time elapsed: 0.132 s
% (29888)------------------------------
% (29888)------------------------------
% (29908)Refutation not found, incomplete strategy% (29908)------------------------------
% (29908)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (29908)Termination reason: Refutation not found, incomplete strategy

% (29908)Memory used [KB]: 10746
% (29908)Time elapsed: 0.140 s
% (29908)------------------------------
% (29908)------------------------------
% (29903)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% (29887)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% (29903)Refutation not found, incomplete strategy% (29903)------------------------------
% (29903)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (29903)Termination reason: Refutation not found, incomplete strategy

% (29903)Memory used [KB]: 6140
% (29903)Time elapsed: 0.001 s
% (29903)------------------------------
% (29903)------------------------------
% (29909)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% (29906)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% (29898)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% (29899)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% (29909)Refutation not found, incomplete strategy% (29909)------------------------------
% (29909)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (29909)Termination reason: Refutation not found, incomplete strategy

% (29909)Memory used [KB]: 1663
% (29909)Time elapsed: 0.135 s
% (29909)------------------------------
% (29909)------------------------------
fof(f14,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f34,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f32])).

fof(f39,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f8,f36,f32])).

fof(f8,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f6])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n004.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:14:53 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.52  % (29893)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.26/0.53  % (29888)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.26/0.53  % (29910)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.26/0.53  % (29905)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.26/0.53  % (29894)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.26/0.53  % (29902)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.26/0.53  % (29891)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.26/0.54  % (29897)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.26/0.54  % (29892)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.39/0.54  % (29890)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.39/0.54  % (29886)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.39/0.54  % (29889)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.39/0.54  % (29905)Refutation not found, incomplete strategy% (29905)------------------------------
% 1.39/0.54  % (29905)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.54  % (29894)Refutation not found, incomplete strategy% (29894)------------------------------
% 1.39/0.54  % (29894)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.54  % (29894)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.54  
% 1.39/0.54  % (29894)Memory used [KB]: 10746
% 1.39/0.54  % (29894)Time elapsed: 0.115 s
% 1.39/0.54  % (29894)------------------------------
% 1.39/0.54  % (29894)------------------------------
% 1.39/0.54  % (29917)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.39/0.54  % (29897)Refutation not found, incomplete strategy% (29897)------------------------------
% 1.39/0.54  % (29897)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.54  % (29897)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.54  
% 1.39/0.54  % (29897)Memory used [KB]: 10618
% 1.39/0.54  % (29897)Time elapsed: 0.137 s
% 1.39/0.54  % (29897)------------------------------
% 1.39/0.54  % (29897)------------------------------
% 1.39/0.54  % (29901)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.39/0.54  % (29910)Refutation found. Thanks to Tanya!
% 1.39/0.54  % SZS status Theorem for theBenchmark
% 1.39/0.54  % SZS output start Proof for theBenchmark
% 1.39/0.54  fof(f189,plain,(
% 1.39/0.54    $false),
% 1.39/0.54    inference(avatar_sat_refutation,[],[f39,f46,f59,f71,f75,f90,f104,f115,f146,f147,f153,f155,f156,f171,f188])).
% 1.39/0.54  fof(f188,plain,(
% 1.39/0.54    spl3_3 | ~spl3_5),
% 1.39/0.54    inference(avatar_contradiction_clause,[],[f183])).
% 1.39/0.54  fof(f183,plain,(
% 1.39/0.54    $false | (spl3_3 | ~spl3_5)),
% 1.39/0.54    inference(unit_resulting_resolution,[],[f45,f179])).
% 1.39/0.54  fof(f179,plain,(
% 1.39/0.54    ( ! [X2] : (r1_tarski(sK0,k2_tarski(X2,sK2))) ) | ~spl3_5),
% 1.39/0.54    inference(superposition,[],[f28,f54])).
% 1.39/0.54  fof(f54,plain,(
% 1.39/0.54    sK0 = k2_tarski(sK2,sK2) | ~spl3_5),
% 1.39/0.54    inference(avatar_component_clause,[],[f52])).
% 1.39/0.54  fof(f52,plain,(
% 1.39/0.54    spl3_5 <=> sK0 = k2_tarski(sK2,sK2)),
% 1.39/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 1.39/0.54  fof(f28,plain,(
% 1.39/0.54    ( ! [X2,X1] : (r1_tarski(k2_tarski(X2,X2),k2_tarski(X1,X2))) )),
% 1.39/0.54    inference(equality_resolution,[],[f24])).
% 1.39/0.54  fof(f24,plain,(
% 1.39/0.54    ( ! [X2,X0,X1] : (k2_tarski(X2,X2) != X0 | r1_tarski(X0,k2_tarski(X1,X2))) )),
% 1.39/0.54    inference(definition_unfolding,[],[f19,f13])).
% 1.39/0.54  fof(f13,plain,(
% 1.39/0.54    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.39/0.54    inference(cnf_transformation,[],[f2])).
% 1.39/0.54  fof(f2,axiom,(
% 1.39/0.54    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.39/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.39/0.54  fof(f19,plain,(
% 1.39/0.54    ( ! [X2,X0,X1] : (k1_tarski(X2) != X0 | r1_tarski(X0,k2_tarski(X1,X2))) )),
% 1.39/0.54    inference(cnf_transformation,[],[f7])).
% 1.39/0.54  fof(f7,plain,(
% 1.39/0.54    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.39/0.54    inference(ennf_transformation,[],[f3])).
% 1.39/0.54  fof(f3,axiom,(
% 1.39/0.54    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 1.39/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).
% 1.39/0.54  fof(f45,plain,(
% 1.39/0.54    ~r1_tarski(sK0,k2_tarski(sK1,sK2)) | spl3_3),
% 1.39/0.54    inference(avatar_component_clause,[],[f43])).
% 1.39/0.54  fof(f43,plain,(
% 1.39/0.54    spl3_3 <=> r1_tarski(sK0,k2_tarski(sK1,sK2))),
% 1.39/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.39/0.54  fof(f171,plain,(
% 1.39/0.54    spl3_3 | ~spl3_6),
% 1.39/0.54    inference(avatar_contradiction_clause,[],[f166])).
% 1.39/0.54  fof(f166,plain,(
% 1.39/0.54    $false | (spl3_3 | ~spl3_6)),
% 1.39/0.54    inference(unit_resulting_resolution,[],[f45,f163])).
% 1.39/0.54  fof(f163,plain,(
% 1.39/0.54    ( ! [X1] : (r1_tarski(sK0,k2_tarski(sK1,X1))) ) | ~spl3_6),
% 1.39/0.54    inference(superposition,[],[f29,f58])).
% 1.39/0.54  fof(f58,plain,(
% 1.39/0.54    sK0 = k2_tarski(sK1,sK1) | ~spl3_6),
% 1.39/0.54    inference(avatar_component_clause,[],[f56])).
% 1.39/0.54  fof(f56,plain,(
% 1.39/0.54    spl3_6 <=> sK0 = k2_tarski(sK1,sK1)),
% 1.39/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 1.39/0.54  fof(f29,plain,(
% 1.39/0.54    ( ! [X2,X1] : (r1_tarski(k2_tarski(X1,X1),k2_tarski(X1,X2))) )),
% 1.39/0.54    inference(equality_resolution,[],[f25])).
% 1.39/0.54  fof(f25,plain,(
% 1.39/0.54    ( ! [X2,X0,X1] : (k2_tarski(X1,X1) != X0 | r1_tarski(X0,k2_tarski(X1,X2))) )),
% 1.39/0.54    inference(definition_unfolding,[],[f18,f13])).
% 1.39/0.54  fof(f18,plain,(
% 1.39/0.54    ( ! [X2,X0,X1] : (k1_tarski(X1) != X0 | r1_tarski(X0,k2_tarski(X1,X2))) )),
% 1.39/0.54    inference(cnf_transformation,[],[f7])).
% 1.39/0.54  fof(f156,plain,(
% 1.39/0.54    ~spl3_1 | ~spl3_6),
% 1.39/0.54    inference(avatar_split_clause,[],[f23,f56,f32])).
% 1.39/0.54  fof(f32,plain,(
% 1.39/0.54    spl3_1 <=> k1_xboole_0 = k4_xboole_0(sK0,k2_tarski(sK1,sK2))),
% 1.39/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.39/0.54  fof(f23,plain,(
% 1.39/0.54    sK0 != k2_tarski(sK1,sK1) | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2))),
% 1.39/0.54    inference(definition_unfolding,[],[f9,f13])).
% 1.39/0.54  fof(f9,plain,(
% 1.39/0.54    sK0 != k1_tarski(sK1) | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2))),
% 1.39/0.54    inference(cnf_transformation,[],[f6])).
% 1.39/0.54  fof(f6,plain,(
% 1.39/0.54    ? [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2)) <~> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.39/0.54    inference(ennf_transformation,[],[f5])).
% 1.39/0.54  fof(f5,negated_conjecture,(
% 1.39/0.54    ~! [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 1.39/0.54    inference(negated_conjecture,[],[f4])).
% 1.39/0.54  fof(f4,conjecture,(
% 1.39/0.54    ! [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 1.39/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_zfmisc_1)).
% 1.39/0.54  fof(f155,plain,(
% 1.39/0.54    spl3_2 | ~spl3_3 | spl3_4 | spl3_5 | spl3_6),
% 1.39/0.54    inference(avatar_contradiction_clause,[],[f154])).
% 1.39/0.54  fof(f154,plain,(
% 1.39/0.54    $false | (spl3_2 | ~spl3_3 | spl3_4 | spl3_5 | spl3_6)),
% 1.39/0.54    inference(unit_resulting_resolution,[],[f38,f49,f44,f57,f53,f26])).
% 1.39/0.54  fof(f26,plain,(
% 1.39/0.54    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_tarski(X1,X2)) | k2_tarski(X1,X1) = X0 | k2_tarski(X2,X2) = X0 | k2_tarski(X1,X2) = X0 | k1_xboole_0 = X0) )),
% 1.39/0.54    inference(definition_unfolding,[],[f16,f13,f13])).
% 1.39/0.54  fof(f16,plain,(
% 1.39/0.54    ( ! [X2,X0,X1] : (k1_xboole_0 = X0 | k1_tarski(X1) = X0 | k1_tarski(X2) = X0 | k2_tarski(X1,X2) = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))) )),
% 1.39/0.54    inference(cnf_transformation,[],[f7])).
% 1.39/0.54  fof(f53,plain,(
% 1.39/0.54    sK0 != k2_tarski(sK2,sK2) | spl3_5),
% 1.39/0.54    inference(avatar_component_clause,[],[f52])).
% 1.39/0.54  fof(f57,plain,(
% 1.39/0.54    sK0 != k2_tarski(sK1,sK1) | spl3_6),
% 1.39/0.54    inference(avatar_component_clause,[],[f56])).
% 1.39/0.54  fof(f44,plain,(
% 1.39/0.54    r1_tarski(sK0,k2_tarski(sK1,sK2)) | ~spl3_3),
% 1.39/0.54    inference(avatar_component_clause,[],[f43])).
% 1.39/0.54  fof(f49,plain,(
% 1.39/0.54    sK0 != k2_tarski(sK1,sK2) | spl3_4),
% 1.39/0.54    inference(avatar_component_clause,[],[f48])).
% 1.39/0.54  fof(f48,plain,(
% 1.39/0.54    spl3_4 <=> sK0 = k2_tarski(sK1,sK2)),
% 1.39/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.39/0.54  fof(f38,plain,(
% 1.39/0.54    k1_xboole_0 != sK0 | spl3_2),
% 1.39/0.54    inference(avatar_component_clause,[],[f36])).
% 1.39/0.54  fof(f36,plain,(
% 1.39/0.54    spl3_2 <=> k1_xboole_0 = sK0),
% 1.39/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.39/0.54  fof(f153,plain,(
% 1.39/0.54    ~spl3_1 | ~spl3_5),
% 1.39/0.54    inference(avatar_split_clause,[],[f22,f52,f32])).
% 1.39/0.54  fof(f22,plain,(
% 1.39/0.54    sK0 != k2_tarski(sK2,sK2) | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2))),
% 1.39/0.54    inference(definition_unfolding,[],[f10,f13])).
% 1.39/0.54  fof(f10,plain,(
% 1.39/0.54    sK0 != k1_tarski(sK2) | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2))),
% 1.39/0.54    inference(cnf_transformation,[],[f6])).
% 1.39/0.54  fof(f147,plain,(
% 1.39/0.54    spl3_3 | ~spl3_1),
% 1.39/0.54    inference(avatar_split_clause,[],[f102,f32,f43])).
% 1.39/0.54  fof(f102,plain,(
% 1.39/0.54    r1_tarski(sK0,k2_tarski(sK1,sK2)) | ~spl3_1),
% 1.39/0.54    inference(trivial_inequality_removal,[],[f101])).
% 1.39/0.54  fof(f101,plain,(
% 1.39/0.54    k1_xboole_0 != k1_xboole_0 | r1_tarski(sK0,k2_tarski(sK1,sK2)) | ~spl3_1),
% 1.39/0.54    inference(superposition,[],[f15,f33])).
% 1.39/0.54  fof(f33,plain,(
% 1.39/0.54    k1_xboole_0 = k4_xboole_0(sK0,k2_tarski(sK1,sK2)) | ~spl3_1),
% 1.39/0.54    inference(avatar_component_clause,[],[f32])).
% 1.39/0.54  fof(f15,plain,(
% 1.39/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)) )),
% 1.39/0.54    inference(cnf_transformation,[],[f1])).
% 1.39/0.54  fof(f1,axiom,(
% 1.39/0.54    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.39/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.39/0.54  fof(f146,plain,(
% 1.39/0.54    ~spl3_11 | ~spl3_4),
% 1.39/0.54    inference(avatar_split_clause,[],[f145,f48,f112])).
% 1.39/0.54  fof(f112,plain,(
% 1.39/0.54    spl3_11 <=> k1_xboole_0 = k4_xboole_0(sK0,sK0)),
% 1.39/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 1.39/0.54  fof(f145,plain,(
% 1.39/0.54    k1_xboole_0 != k4_xboole_0(sK0,sK0) | ~spl3_4),
% 1.39/0.54    inference(forward_demodulation,[],[f144,f50])).
% 1.39/0.54  fof(f50,plain,(
% 1.39/0.54    sK0 = k2_tarski(sK1,sK2) | ~spl3_4),
% 1.39/0.54    inference(avatar_component_clause,[],[f48])).
% 1.39/0.54  fof(f144,plain,(
% 1.39/0.54    k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2)) | ~spl3_4),
% 1.39/0.54    inference(trivial_inequality_removal,[],[f143])).
% 1.39/0.54  fof(f143,plain,(
% 1.39/0.54    sK0 != sK0 | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2)) | ~spl3_4),
% 1.39/0.54    inference(forward_demodulation,[],[f11,f50])).
% 1.39/0.54  fof(f11,plain,(
% 1.39/0.54    sK0 != k2_tarski(sK1,sK2) | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2))),
% 1.39/0.54    inference(cnf_transformation,[],[f6])).
% 1.39/0.54  fof(f115,plain,(
% 1.39/0.54    spl3_11 | ~spl3_1 | ~spl3_4),
% 1.39/0.54    inference(avatar_split_clause,[],[f105,f48,f32,f112])).
% 1.39/0.54  fof(f105,plain,(
% 1.39/0.54    k1_xboole_0 = k4_xboole_0(sK0,sK0) | (~spl3_1 | ~spl3_4)),
% 1.39/0.54    inference(backward_demodulation,[],[f33,f50])).
% 1.39/0.54  fof(f104,plain,(
% 1.39/0.54    sK0 != k2_tarski(sK1,sK2) | r1_tarski(sK0,k2_tarski(sK1,sK2)) | ~r1_tarski(sK0,sK0)),
% 1.39/0.54    introduced(theory_tautology_sat_conflict,[])).
% 1.39/0.54  fof(f90,plain,(
% 1.39/0.54    spl3_10 | ~spl3_4),
% 1.39/0.54    inference(avatar_split_clause,[],[f80,f48,f87])).
% 1.39/0.54  fof(f87,plain,(
% 1.39/0.54    spl3_10 <=> r1_tarski(sK0,sK0)),
% 1.39/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 1.39/0.54  fof(f80,plain,(
% 1.39/0.54    r1_tarski(sK0,sK0) | ~spl3_4),
% 1.39/0.54    inference(superposition,[],[f27,f50])).
% 1.39/0.54  fof(f27,plain,(
% 1.39/0.54    ( ! [X2,X1] : (r1_tarski(k2_tarski(X1,X2),k2_tarski(X1,X2))) )),
% 1.39/0.54    inference(equality_resolution,[],[f20])).
% 1.39/0.54  fof(f20,plain,(
% 1.39/0.54    ( ! [X2,X0,X1] : (k2_tarski(X1,X2) != X0 | r1_tarski(X0,k2_tarski(X1,X2))) )),
% 1.39/0.54    inference(cnf_transformation,[],[f7])).
% 1.39/0.54  fof(f75,plain,(
% 1.39/0.54    spl3_8),
% 1.39/0.54    inference(avatar_contradiction_clause,[],[f72])).
% 1.39/0.54  fof(f72,plain,(
% 1.39/0.54    $false | spl3_8),
% 1.39/0.54    inference(unit_resulting_resolution,[],[f30,f70])).
% 1.39/0.54  fof(f70,plain,(
% 1.39/0.54    ~r1_tarski(k1_xboole_0,k2_tarski(sK1,sK2)) | spl3_8),
% 1.39/0.54    inference(avatar_component_clause,[],[f68])).
% 1.39/0.54  fof(f68,plain,(
% 1.39/0.54    spl3_8 <=> r1_tarski(k1_xboole_0,k2_tarski(sK1,sK2))),
% 1.39/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 1.39/0.54  fof(f30,plain,(
% 1.39/0.54    ( ! [X2,X1] : (r1_tarski(k1_xboole_0,k2_tarski(X1,X2))) )),
% 1.39/0.54    inference(equality_resolution,[],[f17])).
% 1.39/0.54  fof(f17,plain,(
% 1.39/0.54    ( ! [X2,X0,X1] : (k1_xboole_0 != X0 | r1_tarski(X0,k2_tarski(X1,X2))) )),
% 1.39/0.54    inference(cnf_transformation,[],[f7])).
% 1.39/0.54  fof(f71,plain,(
% 1.39/0.54    ~spl3_8 | ~spl3_2 | spl3_3),
% 1.39/0.54    inference(avatar_split_clause,[],[f60,f43,f36,f68])).
% 1.39/0.54  fof(f60,plain,(
% 1.39/0.54    ~r1_tarski(k1_xboole_0,k2_tarski(sK1,sK2)) | (~spl3_2 | spl3_3)),
% 1.39/0.54    inference(backward_demodulation,[],[f45,f37])).
% 1.39/0.54  fof(f37,plain,(
% 1.39/0.54    k1_xboole_0 = sK0 | ~spl3_2),
% 1.39/0.54    inference(avatar_component_clause,[],[f36])).
% 1.39/0.54  fof(f59,plain,(
% 1.39/0.54    spl3_1 | spl3_4 | spl3_5 | spl3_6 | spl3_2),
% 1.39/0.54    inference(avatar_split_clause,[],[f21,f36,f56,f52,f48,f32])).
% 1.39/0.54  fof(f21,plain,(
% 1.39/0.54    k1_xboole_0 = sK0 | sK0 = k2_tarski(sK1,sK1) | sK0 = k2_tarski(sK2,sK2) | sK0 = k2_tarski(sK1,sK2) | k1_xboole_0 = k4_xboole_0(sK0,k2_tarski(sK1,sK2))),
% 1.39/0.54    inference(definition_unfolding,[],[f12,f13,f13])).
% 1.39/0.54  fof(f12,plain,(
% 1.39/0.54    k1_xboole_0 = sK0 | sK0 = k1_tarski(sK1) | sK0 = k1_tarski(sK2) | sK0 = k2_tarski(sK1,sK2) | k1_xboole_0 = k4_xboole_0(sK0,k2_tarski(sK1,sK2))),
% 1.39/0.54    inference(cnf_transformation,[],[f6])).
% 1.39/0.54  fof(f46,plain,(
% 1.39/0.54    ~spl3_3 | spl3_1),
% 1.39/0.54    inference(avatar_split_clause,[],[f41,f32,f43])).
% 1.39/0.54  fof(f41,plain,(
% 1.39/0.54    ~r1_tarski(sK0,k2_tarski(sK1,sK2)) | spl3_1),
% 1.39/0.54    inference(trivial_inequality_removal,[],[f40])).
% 1.39/0.54  fof(f40,plain,(
% 1.39/0.54    k1_xboole_0 != k1_xboole_0 | ~r1_tarski(sK0,k2_tarski(sK1,sK2)) | spl3_1),
% 1.39/0.54    inference(superposition,[],[f34,f14])).
% 1.39/0.54  % (29905)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.54  
% 1.39/0.54  % (29905)Memory used [KB]: 10618
% 1.39/0.54  % (29905)Time elapsed: 0.124 s
% 1.39/0.54  % (29905)------------------------------
% 1.39/0.54  % (29905)------------------------------
% 1.39/0.55  % (29913)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.39/0.55  % (29907)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.39/0.55  % (29908)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.39/0.55  % (29896)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.39/0.55  % (29888)Refutation not found, incomplete strategy% (29888)------------------------------
% 1.39/0.55  % (29888)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.55  % (29888)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.55  
% 1.39/0.55  % (29888)Memory used [KB]: 10746
% 1.39/0.55  % (29888)Time elapsed: 0.132 s
% 1.39/0.55  % (29888)------------------------------
% 1.39/0.55  % (29888)------------------------------
% 1.39/0.55  % (29908)Refutation not found, incomplete strategy% (29908)------------------------------
% 1.39/0.55  % (29908)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.55  % (29908)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.55  
% 1.39/0.55  % (29908)Memory used [KB]: 10746
% 1.39/0.55  % (29908)Time elapsed: 0.140 s
% 1.39/0.55  % (29908)------------------------------
% 1.39/0.55  % (29908)------------------------------
% 1.39/0.55  % (29903)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.39/0.55  % (29887)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.39/0.55  % (29903)Refutation not found, incomplete strategy% (29903)------------------------------
% 1.39/0.55  % (29903)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.55  % (29903)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.55  
% 1.39/0.55  % (29903)Memory used [KB]: 6140
% 1.39/0.55  % (29903)Time elapsed: 0.001 s
% 1.39/0.55  % (29903)------------------------------
% 1.39/0.55  % (29903)------------------------------
% 1.39/0.55  % (29909)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.39/0.55  % (29906)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.39/0.55  % (29898)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.39/0.55  % (29899)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.39/0.55  % (29909)Refutation not found, incomplete strategy% (29909)------------------------------
% 1.39/0.55  % (29909)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.55  % (29909)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.55  
% 1.39/0.55  % (29909)Memory used [KB]: 1663
% 1.39/0.55  % (29909)Time elapsed: 0.135 s
% 1.39/0.55  % (29909)------------------------------
% 1.39/0.55  % (29909)------------------------------
% 1.39/0.55  fof(f14,plain,(
% 1.39/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f1])).
% 1.39/0.55  fof(f34,plain,(
% 1.39/0.55    k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2)) | spl3_1),
% 1.39/0.55    inference(avatar_component_clause,[],[f32])).
% 1.39/0.55  fof(f39,plain,(
% 1.39/0.55    ~spl3_1 | ~spl3_2),
% 1.39/0.55    inference(avatar_split_clause,[],[f8,f36,f32])).
% 1.39/0.55  fof(f8,plain,(
% 1.39/0.55    k1_xboole_0 != sK0 | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2))),
% 1.39/0.55    inference(cnf_transformation,[],[f6])).
% 1.39/0.55  % SZS output end Proof for theBenchmark
% 1.39/0.55  % (29910)------------------------------
% 1.39/0.55  % (29910)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.55  % (29910)Termination reason: Refutation
% 1.39/0.55  
% 1.39/0.55  % (29910)Memory used [KB]: 10746
% 1.39/0.55  % (29910)Time elapsed: 0.091 s
% 1.39/0.55  % (29910)------------------------------
% 1.39/0.55  % (29910)------------------------------
% 1.39/0.55  % (29911)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.39/0.56  % (29883)Success in time 0.189 s
%------------------------------------------------------------------------------
