%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:40:22 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.37s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 187 expanded)
%              Number of leaves         :   20 (  70 expanded)
%              Depth                    :    9
%              Number of atoms          :  180 ( 329 expanded)
%              Number of equality atoms :   66 ( 174 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f450,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f110,f115,f120,f155,f199,f216,f390,f398,f440,f449])).

fof(f449,plain,
    ( spl4_2
    | ~ spl4_21 ),
    inference(avatar_contradiction_clause,[],[f441])).

fof(f441,plain,
    ( $false
    | spl4_2
    | ~ spl4_21 ),
    inference(unit_resulting_resolution,[],[f114,f114,f114,f439,f105])).

fof(f105,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,k3_enumset1(X0,X0,X0,X1,X2))
      | X1 = X4
      | X2 = X4
      | X0 = X4 ) ),
    inference(equality_resolution,[],[f91])).

fof(f91,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 = X4
      | X1 = X4
      | X2 = X4
      | ~ r2_hidden(X4,X3)
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f64,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f44,f59])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f44,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

% (2611)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% (2613)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% (2601)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% (2612)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% (2600)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% (2604)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% (2617)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% (2616)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% (2620)Refutation not found, incomplete strategy% (2620)------------------------------
% (2620)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (2620)Termination reason: Refutation not found, incomplete strategy

% (2620)Memory used [KB]: 1663
% (2620)Time elapsed: 0.152 s
% (2620)------------------------------
% (2620)------------------------------
% (2607)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
fof(f64,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 = X4
      | X1 = X4
      | X2 = X4
      | ~ r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(f439,plain,
    ( r2_hidden(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f437])).

fof(f437,plain,
    ( spl4_21
  <=> r2_hidden(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f114,plain,
    ( sK0 != sK1
    | spl4_2 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl4_2
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f440,plain,
    ( spl4_21
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f429,f387,f437])).

fof(f387,plain,
    ( spl4_20
  <=> k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_enumset1(sK0,sK0,sK0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f429,plain,
    ( r2_hidden(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | ~ spl4_20 ),
    inference(superposition,[],[f100,f389])).

fof(f389,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_enumset1(sK0,sK0,sK0,sK0,sK1)
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f387])).

fof(f100,plain,(
    ! [X4,X0,X1] : r2_hidden(X4,k3_enumset1(X0,X0,X0,X1,X4)) ),
    inference(equality_resolution,[],[f99])).

fof(f99,plain,(
    ! [X4,X0,X3,X1] :
      ( r2_hidden(X4,X3)
      | k3_enumset1(X0,X0,X0,X1,X4) != X3 ) ),
    inference(equality_resolution,[],[f88])).

% (2607)Refutation not found, incomplete strategy% (2607)------------------------------
% (2607)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (2607)Termination reason: Refutation not found, incomplete strategy

% (2607)Memory used [KB]: 10618
% (2607)Time elapsed: 0.150 s
% (2607)------------------------------
% (2607)------------------------------
fof(f88,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X2 != X4
      | r2_hidden(X4,X3)
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f67,f68])).

fof(f67,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X2 != X4
      | r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f398,plain,
    ( ~ spl4_1
    | ~ spl4_7
    | spl4_19 ),
    inference(avatar_contradiction_clause,[],[f391])).

fof(f391,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_7
    | spl4_19 ),
    inference(unit_resulting_resolution,[],[f194,f109,f385,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f54,f69])).

fof(f69,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f36,f68])).

fof(f36,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X1,X2)
      | r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f385,plain,
    ( ~ r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2)
    | spl4_19 ),
    inference(avatar_component_clause,[],[f383])).

fof(f383,plain,
    ( spl4_19
  <=> r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f109,plain,
    ( r2_hidden(sK1,sK2)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl4_1
  <=> r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f194,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f192])).

fof(f192,plain,
    ( spl4_7
  <=> r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f390,plain,
    ( ~ spl4_19
    | spl4_20
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f126,f117,f387,f383])).

fof(f117,plain,
    ( spl4_3
  <=> k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

% (2602)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
fof(f126,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_enumset1(sK0,sK0,sK0,sK0,sK1)
    | ~ r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2)
    | ~ spl4_3 ),
    inference(superposition,[],[f119,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f40,f39])).

fof(f39,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f119,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f117])).

fof(f216,plain,(
    spl4_8 ),
    inference(avatar_contradiction_clause,[],[f202])).

fof(f202,plain,
    ( $false
    | spl4_8 ),
    inference(unit_resulting_resolution,[],[f97,f198,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2)
      | r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f52,f69])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f198,plain,
    ( ~ r2_hidden(sK0,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | spl4_8 ),
    inference(avatar_component_clause,[],[f196])).

fof(f196,plain,
    ( spl4_8
  <=> r2_hidden(sK0,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f97,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f199,plain,
    ( spl4_7
    | ~ spl4_1
    | ~ spl4_8
    | spl4_4 ),
    inference(avatar_split_clause,[],[f160,f152,f196,f107,f192])).

fof(f152,plain,
    ( spl4_4
  <=> r2_hidden(sK0,k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f160,plain,
    ( ~ r2_hidden(sK0,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | ~ r2_hidden(sK1,sK2)
    | r2_hidden(sK0,sK2)
    | spl4_4 ),
    inference(superposition,[],[f154,f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( k3_enumset1(X0,X0,X0,X0,X0) = k4_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f55,f70,f69])).

fof(f70,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f31,f69])).

fof(f31,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(X1,X2)
      | k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( ( X0 = X1
          | r2_hidden(X1,X2) )
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l38_zfmisc_1)).

fof(f154,plain,
    ( ~ r2_hidden(sK0,k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2))
    | spl4_4 ),
    inference(avatar_component_clause,[],[f152])).

fof(f155,plain,
    ( ~ spl4_4
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f148,f117,f152])).

fof(f148,plain,
    ( ~ r2_hidden(sK0,k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2))
    | ~ spl4_3 ),
    inference(trivial_inequality_removal,[],[f130])).

fof(f130,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k3_enumset1(sK0,sK0,sK0,sK0,sK0)
    | ~ r2_hidden(sK0,k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2))
    | ~ spl4_3 ),
    inference(superposition,[],[f84,f119])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( k3_enumset1(X0,X0,X0,X0,X0) != k4_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f58,f70,f69])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f120,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f72,f117])).

fof(f72,plain,(
    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f28,f70,f39,f69])).

fof(f28,plain,(
    k1_tarski(sK0) = k3_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( X0 != X1
      & r2_hidden(X1,X2)
      & k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( X0 != X1
          & r2_hidden(X1,X2)
          & k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0,X1,X2] :
      ~ ( X0 != X1
        & r2_hidden(X1,X2)
        & k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_zfmisc_1)).

fof(f115,plain,(
    ~ spl4_2 ),
    inference(avatar_split_clause,[],[f30,f112])).

fof(f30,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f24])).

fof(f110,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f29,f107])).

fof(f29,plain,(
    r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:23:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (2599)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.52  % (2614)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.52  % (2597)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (2615)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.53  % (2620)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.53  % (2619)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.53  % (2603)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.53  % (2591)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.53  % (2593)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.53  % (2595)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.53  % (2605)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.54  % (2594)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.54  % (2592)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.54  % (2608)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.54  % (2606)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.54  % (2596)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.54  % (2598)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.55  % (2609)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.55  % (2619)Refutation found. Thanks to Tanya!
% 0.21/0.55  % SZS status Theorem for theBenchmark
% 0.21/0.55  % SZS output start Proof for theBenchmark
% 0.21/0.55  fof(f450,plain,(
% 0.21/0.55    $false),
% 0.21/0.55    inference(avatar_sat_refutation,[],[f110,f115,f120,f155,f199,f216,f390,f398,f440,f449])).
% 0.21/0.55  fof(f449,plain,(
% 0.21/0.55    spl4_2 | ~spl4_21),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f441])).
% 0.21/0.55  fof(f441,plain,(
% 0.21/0.55    $false | (spl4_2 | ~spl4_21)),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f114,f114,f114,f439,f105])).
% 0.21/0.55  fof(f105,plain,(
% 0.21/0.55    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,k3_enumset1(X0,X0,X0,X1,X2)) | X1 = X4 | X2 = X4 | X0 = X4) )),
% 0.21/0.55    inference(equality_resolution,[],[f91])).
% 0.21/0.55  fof(f91,plain,(
% 0.21/0.55    ( ! [X4,X2,X0,X3,X1] : (X0 = X4 | X1 = X4 | X2 = X4 | ~r2_hidden(X4,X3) | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 0.21/0.55    inference(definition_unfolding,[],[f64,f68])).
% 0.21/0.55  fof(f68,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 0.21/0.55    inference(definition_unfolding,[],[f44,f59])).
% 0.21/0.55  fof(f59,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f18])).
% 0.21/0.55  fof(f18,axiom,(
% 0.21/0.55    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.21/0.55  fof(f44,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f17])).
% 0.21/0.55  fof(f17,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.55  % (2611)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.55  % (2613)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.55  % (2601)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.55  % (2612)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.55  % (2600)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.56  % (2604)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.56  % (2617)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.56  % (2616)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.56  % (2620)Refutation not found, incomplete strategy% (2620)------------------------------
% 0.21/0.56  % (2620)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (2620)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (2620)Memory used [KB]: 1663
% 0.21/0.56  % (2620)Time elapsed: 0.152 s
% 0.21/0.56  % (2620)------------------------------
% 0.21/0.56  % (2620)------------------------------
% 0.21/0.56  % (2607)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.56  fof(f64,plain,(
% 0.21/0.56    ( ! [X4,X2,X0,X3,X1] : (X0 = X4 | X1 = X4 | X2 = X4 | ~r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 0.21/0.56    inference(cnf_transformation,[],[f27])).
% 0.21/0.56  fof(f27,plain,(
% 0.21/0.56    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 0.21/0.56    inference(ennf_transformation,[],[f14])).
% 0.21/0.56  fof(f14,axiom,(
% 0.21/0.56    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 0.21/0.56  fof(f439,plain,(
% 0.21/0.56    r2_hidden(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | ~spl4_21),
% 0.21/0.56    inference(avatar_component_clause,[],[f437])).
% 0.21/0.56  fof(f437,plain,(
% 0.21/0.56    spl4_21 <=> r2_hidden(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 0.21/0.56  fof(f114,plain,(
% 0.21/0.56    sK0 != sK1 | spl4_2),
% 0.21/0.56    inference(avatar_component_clause,[],[f112])).
% 0.21/0.56  fof(f112,plain,(
% 0.21/0.56    spl4_2 <=> sK0 = sK1),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.56  fof(f440,plain,(
% 0.21/0.56    spl4_21 | ~spl4_20),
% 0.21/0.56    inference(avatar_split_clause,[],[f429,f387,f437])).
% 0.21/0.56  fof(f387,plain,(
% 0.21/0.56    spl4_20 <=> k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_enumset1(sK0,sK0,sK0,sK0,sK1)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 0.21/0.56  fof(f429,plain,(
% 0.21/0.56    r2_hidden(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | ~spl4_20),
% 0.21/0.56    inference(superposition,[],[f100,f389])).
% 0.21/0.56  fof(f389,plain,(
% 0.21/0.56    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_enumset1(sK0,sK0,sK0,sK0,sK1) | ~spl4_20),
% 0.21/0.56    inference(avatar_component_clause,[],[f387])).
% 0.21/0.56  fof(f100,plain,(
% 0.21/0.56    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_enumset1(X0,X0,X0,X1,X4))) )),
% 0.21/0.56    inference(equality_resolution,[],[f99])).
% 0.21/0.56  fof(f99,plain,(
% 0.21/0.56    ( ! [X4,X0,X3,X1] : (r2_hidden(X4,X3) | k3_enumset1(X0,X0,X0,X1,X4) != X3) )),
% 0.21/0.56    inference(equality_resolution,[],[f88])).
% 0.21/0.56  % (2607)Refutation not found, incomplete strategy% (2607)------------------------------
% 0.21/0.56  % (2607)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (2607)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (2607)Memory used [KB]: 10618
% 0.21/0.56  % (2607)Time elapsed: 0.150 s
% 0.21/0.56  % (2607)------------------------------
% 0.21/0.56  % (2607)------------------------------
% 0.21/0.56  fof(f88,plain,(
% 0.21/0.56    ( ! [X4,X2,X0,X3,X1] : (X2 != X4 | r2_hidden(X4,X3) | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 0.21/0.56    inference(definition_unfolding,[],[f67,f68])).
% 0.21/0.56  fof(f67,plain,(
% 0.21/0.56    ( ! [X4,X2,X0,X3,X1] : (X2 != X4 | r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 0.21/0.56    inference(cnf_transformation,[],[f27])).
% 0.21/0.56  fof(f398,plain,(
% 0.21/0.56    ~spl4_1 | ~spl4_7 | spl4_19),
% 0.21/0.56    inference(avatar_contradiction_clause,[],[f391])).
% 0.21/0.56  fof(f391,plain,(
% 0.21/0.56    $false | (~spl4_1 | ~spl4_7 | spl4_19)),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f194,f109,f385,f81])).
% 0.21/0.56  fof(f81,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 0.21/0.56    inference(definition_unfolding,[],[f54,f69])).
% 0.21/0.56  fof(f69,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 0.21/0.56    inference(definition_unfolding,[],[f36,f68])).
% 0.21/0.56  fof(f36,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f16])).
% 0.21/0.56  fof(f16,axiom,(
% 0.21/0.56    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.56  fof(f54,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r2_hidden(X1,X2) | r1_tarski(k2_tarski(X0,X1),X2)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f20])).
% 0.21/0.56  fof(f20,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 0.21/0.56  fof(f385,plain,(
% 0.21/0.56    ~r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2) | spl4_19),
% 0.21/0.56    inference(avatar_component_clause,[],[f383])).
% 0.21/0.56  fof(f383,plain,(
% 0.21/0.56    spl4_19 <=> r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.21/0.56  fof(f109,plain,(
% 0.21/0.56    r2_hidden(sK1,sK2) | ~spl4_1),
% 0.21/0.56    inference(avatar_component_clause,[],[f107])).
% 0.21/0.56  fof(f107,plain,(
% 0.21/0.56    spl4_1 <=> r2_hidden(sK1,sK2)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.56  fof(f194,plain,(
% 0.21/0.56    r2_hidden(sK0,sK2) | ~spl4_7),
% 0.21/0.56    inference(avatar_component_clause,[],[f192])).
% 0.21/0.56  fof(f192,plain,(
% 0.21/0.56    spl4_7 <=> r2_hidden(sK0,sK2)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.56  fof(f390,plain,(
% 0.21/0.56    ~spl4_19 | spl4_20 | ~spl4_3),
% 0.21/0.56    inference(avatar_split_clause,[],[f126,f117,f387,f383])).
% 0.21/0.56  fof(f117,plain,(
% 0.21/0.56    spl4_3 <=> k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.37/0.56  % (2602)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.37/0.56  fof(f126,plain,(
% 1.37/0.56    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_enumset1(sK0,sK0,sK0,sK0,sK1) | ~r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2) | ~spl4_3),
% 1.37/0.56    inference(superposition,[],[f119,f77])).
% 1.37/0.56  fof(f77,plain,(
% 1.37/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 1.37/0.56    inference(definition_unfolding,[],[f40,f39])).
% 1.37/0.56  fof(f39,plain,(
% 1.37/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.37/0.56    inference(cnf_transformation,[],[f11])).
% 1.37/0.56  fof(f11,axiom,(
% 1.37/0.56    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.37/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.37/0.56  fof(f40,plain,(
% 1.37/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.37/0.56    inference(cnf_transformation,[],[f25])).
% 1.37/0.56  fof(f25,plain,(
% 1.37/0.56    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.37/0.56    inference(ennf_transformation,[],[f10])).
% 1.37/0.56  fof(f10,axiom,(
% 1.37/0.56    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.37/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.37/0.56  fof(f119,plain,(
% 1.37/0.56    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2)) | ~spl4_3),
% 1.37/0.56    inference(avatar_component_clause,[],[f117])).
% 1.37/0.56  fof(f216,plain,(
% 1.37/0.56    spl4_8),
% 1.37/0.56    inference(avatar_contradiction_clause,[],[f202])).
% 1.37/0.56  fof(f202,plain,(
% 1.37/0.56    $false | spl4_8),
% 1.37/0.56    inference(unit_resulting_resolution,[],[f97,f198,f83])).
% 1.37/0.56  fof(f83,plain,(
% 1.37/0.56    ( ! [X2,X0,X1] : (~r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2) | r2_hidden(X0,X2)) )),
% 1.37/0.56    inference(definition_unfolding,[],[f52,f69])).
% 1.37/0.56  fof(f52,plain,(
% 1.37/0.56    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 1.37/0.56    inference(cnf_transformation,[],[f20])).
% 1.37/0.56  fof(f198,plain,(
% 1.37/0.56    ~r2_hidden(sK0,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | spl4_8),
% 1.37/0.56    inference(avatar_component_clause,[],[f196])).
% 1.37/0.56  fof(f196,plain,(
% 1.37/0.56    spl4_8 <=> r2_hidden(sK0,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),
% 1.37/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 1.37/0.56  fof(f97,plain,(
% 1.37/0.56    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.37/0.56    inference(equality_resolution,[],[f41])).
% 1.37/0.56  fof(f41,plain,(
% 1.37/0.56    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.37/0.56    inference(cnf_transformation,[],[f4])).
% 1.37/0.56  fof(f4,axiom,(
% 1.37/0.56    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.37/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.37/0.56  fof(f199,plain,(
% 1.37/0.56    spl4_7 | ~spl4_1 | ~spl4_8 | spl4_4),
% 1.37/0.56    inference(avatar_split_clause,[],[f160,f152,f196,f107,f192])).
% 1.37/0.56  fof(f152,plain,(
% 1.37/0.56    spl4_4 <=> r2_hidden(sK0,k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2))),
% 1.37/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.37/0.56  fof(f160,plain,(
% 1.37/0.56    ~r2_hidden(sK0,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | ~r2_hidden(sK1,sK2) | r2_hidden(sK0,sK2) | spl4_4),
% 1.37/0.56    inference(superposition,[],[f154,f87])).
% 1.37/0.56  fof(f87,plain,(
% 1.37/0.56    ( ! [X2,X0,X1] : (k3_enumset1(X0,X0,X0,X0,X0) = k4_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),X2) | ~r2_hidden(X1,X2) | r2_hidden(X0,X2)) )),
% 1.37/0.56    inference(definition_unfolding,[],[f55,f70,f69])).
% 1.37/0.56  fof(f70,plain,(
% 1.37/0.56    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 1.37/0.56    inference(definition_unfolding,[],[f31,f69])).
% 1.37/0.56  fof(f31,plain,(
% 1.37/0.56    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.37/0.56    inference(cnf_transformation,[],[f15])).
% 1.37/0.56  fof(f15,axiom,(
% 1.37/0.56    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.37/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.37/0.56  fof(f55,plain,(
% 1.37/0.56    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r2_hidden(X1,X2) | k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)) )),
% 1.37/0.56    inference(cnf_transformation,[],[f19])).
% 1.37/0.56  fof(f19,axiom,(
% 1.37/0.56    ! [X0,X1,X2] : (k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> ((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)))),
% 1.37/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l38_zfmisc_1)).
% 1.37/0.56  fof(f154,plain,(
% 1.37/0.56    ~r2_hidden(sK0,k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2)) | spl4_4),
% 1.37/0.56    inference(avatar_component_clause,[],[f152])).
% 1.37/0.56  fof(f155,plain,(
% 1.37/0.56    ~spl4_4 | ~spl4_3),
% 1.37/0.56    inference(avatar_split_clause,[],[f148,f117,f152])).
% 1.37/0.56  fof(f148,plain,(
% 1.37/0.56    ~r2_hidden(sK0,k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2)) | ~spl4_3),
% 1.37/0.56    inference(trivial_inequality_removal,[],[f130])).
% 1.37/0.56  fof(f130,plain,(
% 1.37/0.56    k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k3_enumset1(sK0,sK0,sK0,sK0,sK0) | ~r2_hidden(sK0,k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2)) | ~spl4_3),
% 1.37/0.56    inference(superposition,[],[f84,f119])).
% 1.37/0.56  fof(f84,plain,(
% 1.37/0.56    ( ! [X2,X0,X1] : (k3_enumset1(X0,X0,X0,X0,X0) != k4_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),X2) | ~r2_hidden(X0,X2)) )),
% 1.37/0.56    inference(definition_unfolding,[],[f58,f70,f69])).
% 1.37/0.56  fof(f58,plain,(
% 1.37/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2)) )),
% 1.37/0.56    inference(cnf_transformation,[],[f19])).
% 1.37/0.56  fof(f120,plain,(
% 1.37/0.56    spl4_3),
% 1.37/0.56    inference(avatar_split_clause,[],[f72,f117])).
% 1.37/0.56  fof(f72,plain,(
% 1.37/0.56    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2))),
% 1.37/0.56    inference(definition_unfolding,[],[f28,f70,f39,f69])).
% 1.37/0.56  fof(f28,plain,(
% 1.37/0.56    k1_tarski(sK0) = k3_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 1.37/0.56    inference(cnf_transformation,[],[f24])).
% 1.37/0.56  fof(f24,plain,(
% 1.37/0.56    ? [X0,X1,X2] : (X0 != X1 & r2_hidden(X1,X2) & k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X1),X2))),
% 1.37/0.56    inference(ennf_transformation,[],[f22])).
% 1.37/0.56  fof(f22,negated_conjecture,(
% 1.37/0.56    ~! [X0,X1,X2] : ~(X0 != X1 & r2_hidden(X1,X2) & k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X1),X2))),
% 1.37/0.56    inference(negated_conjecture,[],[f21])).
% 1.37/0.56  fof(f21,conjecture,(
% 1.37/0.56    ! [X0,X1,X2] : ~(X0 != X1 & r2_hidden(X1,X2) & k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X1),X2))),
% 1.37/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_zfmisc_1)).
% 1.37/0.57  fof(f115,plain,(
% 1.37/0.57    ~spl4_2),
% 1.37/0.57    inference(avatar_split_clause,[],[f30,f112])).
% 1.37/0.57  fof(f30,plain,(
% 1.37/0.57    sK0 != sK1),
% 1.37/0.57    inference(cnf_transformation,[],[f24])).
% 1.37/0.57  fof(f110,plain,(
% 1.37/0.57    spl4_1),
% 1.37/0.57    inference(avatar_split_clause,[],[f29,f107])).
% 1.37/0.57  fof(f29,plain,(
% 1.37/0.57    r2_hidden(sK1,sK2)),
% 1.37/0.57    inference(cnf_transformation,[],[f24])).
% 1.37/0.57  % SZS output end Proof for theBenchmark
% 1.37/0.57  % (2619)------------------------------
% 1.37/0.57  % (2619)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.57  % (2619)Termination reason: Refutation
% 1.37/0.57  
% 1.37/0.57  % (2619)Memory used [KB]: 11001
% 1.37/0.57  % (2619)Time elapsed: 0.141 s
% 1.37/0.57  % (2619)------------------------------
% 1.37/0.57  % (2619)------------------------------
% 1.37/0.57  % (2590)Success in time 0.202 s
%------------------------------------------------------------------------------
