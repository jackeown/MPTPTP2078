%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:52 EST 2020

% Result     : Theorem 1.38s
% Output     : Refutation 1.38s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 197 expanded)
%              Number of leaves         :   16 (  70 expanded)
%              Depth                    :   10
%              Number of atoms          :  240 ( 584 expanded)
%              Number of equality atoms :  109 ( 342 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f276,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f47,f57,f67,f93,f110,f118,f137,f172,f188,f220,f275])).

fof(f275,plain,
    ( ~ spl3_2
    | ~ spl3_5 ),
    inference(avatar_contradiction_clause,[],[f274])).

fof(f274,plain,
    ( $false
    | ~ spl3_2
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f273,f259])).

fof(f259,plain,
    ( sK1 != sK2
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f258,f51])).

fof(f51,plain,
    ( sK1 = k2_tarski(sK0,sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl3_2
  <=> sK1 = k2_tarski(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f258,plain,
    ( sK2 != k2_tarski(sK0,sK0)
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f34,f51])).

fof(f34,plain,
    ( sK2 != k2_tarski(sK0,sK0)
    | sK1 != k2_tarski(sK0,sK0) ),
    inference(definition_unfolding,[],[f19,f22,f22])).

fof(f22,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

% (11675)Refutation not found, incomplete strategy% (11675)------------------------------
% (11675)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (11675)Termination reason: Refutation not found, incomplete strategy

% (11675)Memory used [KB]: 1663
% (11675)Time elapsed: 0.138 s
% (11675)------------------------------
% (11675)------------------------------
% (11653)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% (11667)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% (11670)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% (11661)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% (11663)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% (11663)Refutation not found, incomplete strategy% (11663)------------------------------
% (11663)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (11663)Termination reason: Refutation not found, incomplete strategy

% (11663)Memory used [KB]: 1663
% (11663)Time elapsed: 0.139 s
% (11663)------------------------------
% (11663)------------------------------
% (11662)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% (11658)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% (11654)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% (11662)Refutation not found, incomplete strategy% (11662)------------------------------
% (11662)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (11662)Termination reason: Refutation not found, incomplete strategy

% (11662)Memory used [KB]: 10618
% (11662)Time elapsed: 0.154 s
% (11662)------------------------------
% (11662)------------------------------
% (11657)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% (11657)Refutation not found, incomplete strategy% (11657)------------------------------
% (11657)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (11657)Termination reason: Refutation not found, incomplete strategy

% (11657)Memory used [KB]: 6140
% (11657)Time elapsed: 0.150 s
% (11657)------------------------------
% (11657)------------------------------
% (11674)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% (11660)Refutation not found, incomplete strategy% (11660)------------------------------
% (11660)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (11660)Termination reason: Refutation not found, incomplete strategy

% (11660)Memory used [KB]: 1663
% (11660)Time elapsed: 0.132 s
% (11660)------------------------------
% (11660)------------------------------
% (11674)Refutation not found, incomplete strategy% (11674)------------------------------
% (11674)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (11674)Termination reason: Refutation not found, incomplete strategy

% (11674)Memory used [KB]: 10746
% (11674)Time elapsed: 0.152 s
% (11674)------------------------------
% (11674)------------------------------
fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f19,plain,
    ( sK2 != k1_tarski(sK0)
    | sK1 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ( k1_xboole_0 != sK2
      | sK1 != k1_tarski(sK0) )
    & ( sK2 != k1_tarski(sK0)
      | k1_xboole_0 != sK1 )
    & ( sK2 != k1_tarski(sK0)
      | sK1 != k1_tarski(sK0) )
    & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f12])).

fof(f12,plain,
    ( ? [X0,X1,X2] :
        ( ( k1_xboole_0 != X2
          | k1_tarski(X0) != X1 )
        & ( k1_tarski(X0) != X2
          | k1_xboole_0 != X1 )
        & ( k1_tarski(X0) != X2
          | k1_tarski(X0) != X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) )
   => ( ( k1_xboole_0 != sK2
        | sK1 != k1_tarski(sK0) )
      & ( sK2 != k1_tarski(sK0)
        | k1_xboole_0 != sK1 )
      & ( sK2 != k1_tarski(sK0)
        | sK1 != k1_tarski(sK0) )
      & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(f273,plain,
    ( sK1 = sK2
    | ~ spl3_2
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f65,f51])).

fof(f65,plain,
    ( sK2 = k2_tarski(sK0,sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl3_5
  <=> sK2 = k2_tarski(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f220,plain,
    ( ~ spl3_1
    | spl3_3
    | spl3_5 ),
    inference(avatar_contradiction_clause,[],[f219])).

fof(f219,plain,
    ( $false
    | ~ spl3_1
    | spl3_3
    | spl3_5 ),
    inference(subsumption_resolution,[],[f90,f154])).

fof(f154,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X1,X0)) ),
    inference(superposition,[],[f78,f23])).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f78,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(unit_resulting_resolution,[],[f39,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f39,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f90,plain,
    ( ~ r1_tarski(sK2,k2_xboole_0(sK1,sK2))
    | ~ spl3_1
    | spl3_3
    | spl3_5 ),
    inference(forward_demodulation,[],[f86,f46])).

fof(f46,plain,
    ( k2_xboole_0(sK1,sK2) = k2_tarski(sK0,sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl3_1
  <=> k2_xboole_0(sK1,sK2) = k2_tarski(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f86,plain,
    ( ~ r1_tarski(sK2,k2_tarski(sK0,sK0))
    | spl3_3
    | spl3_5 ),
    inference(unit_resulting_resolution,[],[f56,f66,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_tarski(X1,X1))
      | k1_xboole_0 = X0
      | k2_tarski(X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f28,f22,f22])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f66,plain,
    ( sK2 != k2_tarski(sK0,sK0)
    | spl3_5 ),
    inference(avatar_component_clause,[],[f64])).

fof(f56,plain,
    ( k1_xboole_0 != sK2
    | spl3_3 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl3_3
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f188,plain,
    ( ~ spl3_3
    | ~ spl3_7
    | spl3_8 ),
    inference(avatar_contradiction_clause,[],[f187])).

fof(f187,plain,
    ( $false
    | ~ spl3_3
    | ~ spl3_7
    | spl3_8 ),
    inference(subsumption_resolution,[],[f186,f109])).

fof(f109,plain,
    ( k1_xboole_0 != k2_tarski(sK0,sK0)
    | spl3_8 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl3_8
  <=> k1_xboole_0 = k2_tarski(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f186,plain,
    ( k1_xboole_0 = k2_tarski(sK0,sK0)
    | ~ spl3_3
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f178,f74])).

fof(f74,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(unit_resulting_resolution,[],[f39,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f178,plain,
    ( k2_tarski(sK0,sK0) = k2_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl3_3
    | ~ spl3_7 ),
    inference(backward_demodulation,[],[f97,f55])).

fof(f55,plain,
    ( k1_xboole_0 = sK2
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f54])).

fof(f97,plain,
    ( k2_tarski(sK0,sK0) = k2_xboole_0(k1_xboole_0,sK2)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl3_7
  <=> k2_tarski(sK0,sK0) = k2_xboole_0(k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f172,plain,(
    spl3_11 ),
    inference(avatar_contradiction_clause,[],[f165])).

fof(f165,plain,
    ( $false
    | spl3_11 ),
    inference(unit_resulting_resolution,[],[f136,f39,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X1,X0),X2)
      | r1_tarski(X0,X2) ) ),
    inference(superposition,[],[f31,f23])).

fof(f136,plain,
    ( ~ r1_tarski(sK2,k2_xboole_0(k1_xboole_0,sK2))
    | spl3_11 ),
    inference(avatar_component_clause,[],[f134])).

fof(f134,plain,
    ( spl3_11
  <=> r1_tarski(sK2,k2_xboole_0(k1_xboole_0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f137,plain,
    ( ~ spl3_11
    | ~ spl3_1
    | spl3_3
    | ~ spl3_4
    | spl3_5 ),
    inference(avatar_split_clause,[],[f104,f64,f60,f54,f44,f134])).

fof(f60,plain,
    ( spl3_4
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f104,plain,
    ( ~ r1_tarski(sK2,k2_xboole_0(k1_xboole_0,sK2))
    | ~ spl3_1
    | spl3_3
    | ~ spl3_4
    | spl3_5 ),
    inference(backward_demodulation,[],[f90,f61])).

fof(f61,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f60])).

fof(f118,plain,
    ( spl3_7
    | ~ spl3_1
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f98,f60,f44,f95])).

fof(f98,plain,
    ( k2_tarski(sK0,sK0) = k2_xboole_0(k1_xboole_0,sK2)
    | ~ spl3_1
    | ~ spl3_4 ),
    inference(backward_demodulation,[],[f46,f61])).

fof(f110,plain,
    ( ~ spl3_8
    | spl3_2
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f99,f60,f50,f107])).

fof(f99,plain,
    ( k1_xboole_0 != k2_tarski(sK0,sK0)
    | spl3_2
    | ~ spl3_4 ),
    inference(backward_demodulation,[],[f52,f61])).

fof(f52,plain,
    ( sK1 != k2_tarski(sK0,sK0)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f50])).

fof(f93,plain,
    ( ~ spl3_1
    | spl3_2
    | spl3_4 ),
    inference(avatar_contradiction_clause,[],[f92])).

fof(f92,plain,
    ( $false
    | ~ spl3_1
    | spl3_2
    | spl3_4 ),
    inference(subsumption_resolution,[],[f91,f78])).

fof(f91,plain,
    ( ~ r1_tarski(sK1,k2_xboole_0(sK1,sK2))
    | ~ spl3_1
    | spl3_2
    | spl3_4 ),
    inference(forward_demodulation,[],[f85,f46])).

fof(f85,plain,
    ( ~ r1_tarski(sK1,k2_tarski(sK0,sK0))
    | spl3_2
    | spl3_4 ),
    inference(unit_resulting_resolution,[],[f62,f52,f38])).

fof(f62,plain,
    ( k1_xboole_0 != sK1
    | spl3_4 ),
    inference(avatar_component_clause,[],[f60])).

fof(f67,plain,
    ( ~ spl3_4
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f33,f64,f60])).

fof(f33,plain,
    ( sK2 != k2_tarski(sK0,sK0)
    | k1_xboole_0 != sK1 ),
    inference(definition_unfolding,[],[f20,f22])).

fof(f20,plain,
    ( sK2 != k1_tarski(sK0)
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f13])).

fof(f57,plain,
    ( ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f32,f54,f50])).

fof(f32,plain,
    ( k1_xboole_0 != sK2
    | sK1 != k2_tarski(sK0,sK0) ),
    inference(definition_unfolding,[],[f21,f22])).

fof(f21,plain,
    ( k1_xboole_0 != sK2
    | sK1 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f47,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f35,f44])).

fof(f35,plain,(
    k2_xboole_0(sK1,sK2) = k2_tarski(sK0,sK0) ),
    inference(definition_unfolding,[],[f18,f22])).

fof(f18,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:09:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (11647)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.51  % (11647)Refutation not found, incomplete strategy% (11647)------------------------------
% 0.21/0.51  % (11647)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (11668)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.51  % (11647)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (11647)Memory used [KB]: 1663
% 0.21/0.51  % (11647)Time elapsed: 0.092 s
% 0.21/0.51  % (11647)------------------------------
% 0.21/0.51  % (11647)------------------------------
% 0.21/0.52  % (11651)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.52  % (11669)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.52  % (11650)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.52  % (11659)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.53  % (11660)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.53  % (11664)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.53  % (11664)Refutation not found, incomplete strategy% (11664)------------------------------
% 0.21/0.53  % (11664)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (11664)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (11664)Memory used [KB]: 1663
% 0.21/0.53  % (11664)Time elapsed: 0.119 s
% 0.21/0.53  % (11664)------------------------------
% 0.21/0.53  % (11664)------------------------------
% 0.21/0.53  % (11648)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.53  % (11672)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (11672)Refutation not found, incomplete strategy% (11672)------------------------------
% 0.21/0.53  % (11672)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (11672)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (11672)Memory used [KB]: 6268
% 0.21/0.53  % (11672)Time elapsed: 0.118 s
% 0.21/0.53  % (11672)------------------------------
% 0.21/0.53  % (11672)------------------------------
% 0.21/0.54  % (11655)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.54  % (11649)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.54  % (11646)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.54  % (11652)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (11666)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.38/0.54  % (11671)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.38/0.55  % (11675)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.38/0.55  % (11666)Refutation found. Thanks to Tanya!
% 1.38/0.55  % SZS status Theorem for theBenchmark
% 1.38/0.55  % SZS output start Proof for theBenchmark
% 1.38/0.55  fof(f276,plain,(
% 1.38/0.55    $false),
% 1.38/0.55    inference(avatar_sat_refutation,[],[f47,f57,f67,f93,f110,f118,f137,f172,f188,f220,f275])).
% 1.38/0.55  fof(f275,plain,(
% 1.38/0.55    ~spl3_2 | ~spl3_5),
% 1.38/0.55    inference(avatar_contradiction_clause,[],[f274])).
% 1.38/0.55  fof(f274,plain,(
% 1.38/0.55    $false | (~spl3_2 | ~spl3_5)),
% 1.38/0.55    inference(subsumption_resolution,[],[f273,f259])).
% 1.38/0.55  fof(f259,plain,(
% 1.38/0.55    sK1 != sK2 | ~spl3_2),
% 1.38/0.55    inference(forward_demodulation,[],[f258,f51])).
% 1.38/0.55  fof(f51,plain,(
% 1.38/0.55    sK1 = k2_tarski(sK0,sK0) | ~spl3_2),
% 1.38/0.55    inference(avatar_component_clause,[],[f50])).
% 1.38/0.55  fof(f50,plain,(
% 1.38/0.55    spl3_2 <=> sK1 = k2_tarski(sK0,sK0)),
% 1.38/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.38/0.55  fof(f258,plain,(
% 1.38/0.55    sK2 != k2_tarski(sK0,sK0) | ~spl3_2),
% 1.38/0.55    inference(subsumption_resolution,[],[f34,f51])).
% 1.38/0.55  fof(f34,plain,(
% 1.38/0.55    sK2 != k2_tarski(sK0,sK0) | sK1 != k2_tarski(sK0,sK0)),
% 1.38/0.55    inference(definition_unfolding,[],[f19,f22,f22])).
% 1.38/0.55  fof(f22,plain,(
% 1.38/0.55    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.38/0.55    inference(cnf_transformation,[],[f5])).
% 1.38/0.55  % (11675)Refutation not found, incomplete strategy% (11675)------------------------------
% 1.38/0.55  % (11675)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.55  % (11675)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.55  
% 1.38/0.55  % (11675)Memory used [KB]: 1663
% 1.38/0.55  % (11675)Time elapsed: 0.138 s
% 1.38/0.55  % (11675)------------------------------
% 1.38/0.55  % (11675)------------------------------
% 1.38/0.55  % (11653)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.38/0.55  % (11667)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.38/0.55  % (11670)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.38/0.55  % (11661)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.38/0.55  % (11663)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.38/0.55  % (11663)Refutation not found, incomplete strategy% (11663)------------------------------
% 1.38/0.55  % (11663)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.55  % (11663)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.55  
% 1.38/0.55  % (11663)Memory used [KB]: 1663
% 1.38/0.55  % (11663)Time elapsed: 0.139 s
% 1.38/0.55  % (11663)------------------------------
% 1.38/0.55  % (11663)------------------------------
% 1.38/0.55  % (11662)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.38/0.55  % (11658)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.38/0.56  % (11654)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.38/0.56  % (11662)Refutation not found, incomplete strategy% (11662)------------------------------
% 1.38/0.56  % (11662)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.56  % (11662)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.56  
% 1.38/0.56  % (11662)Memory used [KB]: 10618
% 1.38/0.56  % (11662)Time elapsed: 0.154 s
% 1.38/0.56  % (11662)------------------------------
% 1.38/0.56  % (11662)------------------------------
% 1.38/0.56  % (11657)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.38/0.56  % (11657)Refutation not found, incomplete strategy% (11657)------------------------------
% 1.38/0.56  % (11657)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.56  % (11657)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.56  
% 1.38/0.56  % (11657)Memory used [KB]: 6140
% 1.38/0.56  % (11657)Time elapsed: 0.150 s
% 1.38/0.56  % (11657)------------------------------
% 1.38/0.56  % (11657)------------------------------
% 1.38/0.56  % (11674)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.38/0.56  % (11660)Refutation not found, incomplete strategy% (11660)------------------------------
% 1.38/0.56  % (11660)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.56  % (11660)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.56  
% 1.38/0.56  % (11660)Memory used [KB]: 1663
% 1.38/0.56  % (11660)Time elapsed: 0.132 s
% 1.38/0.56  % (11660)------------------------------
% 1.38/0.56  % (11660)------------------------------
% 1.38/0.56  % (11674)Refutation not found, incomplete strategy% (11674)------------------------------
% 1.38/0.56  % (11674)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.56  % (11674)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.56  
% 1.38/0.56  % (11674)Memory used [KB]: 10746
% 1.38/0.56  % (11674)Time elapsed: 0.152 s
% 1.38/0.56  % (11674)------------------------------
% 1.38/0.56  % (11674)------------------------------
% 1.38/0.56  fof(f5,axiom,(
% 1.38/0.56    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.38/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.38/0.56  fof(f19,plain,(
% 1.38/0.56    sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)),
% 1.38/0.56    inference(cnf_transformation,[],[f13])).
% 1.38/0.56  fof(f13,plain,(
% 1.38/0.56    (k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)) & (sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1) & (sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)) & k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 1.38/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f12])).
% 1.38/0.56  fof(f12,plain,(
% 1.38/0.56    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2)) => ((k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)) & (sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1) & (sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)) & k1_tarski(sK0) = k2_xboole_0(sK1,sK2))),
% 1.38/0.56    introduced(choice_axiom,[])).
% 1.38/0.56  fof(f9,plain,(
% 1.38/0.56    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.38/0.56    inference(ennf_transformation,[],[f8])).
% 1.38/0.56  fof(f8,negated_conjecture,(
% 1.38/0.56    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.38/0.56    inference(negated_conjecture,[],[f7])).
% 1.38/0.56  fof(f7,conjecture,(
% 1.38/0.56    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.38/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).
% 1.38/0.56  fof(f273,plain,(
% 1.38/0.56    sK1 = sK2 | (~spl3_2 | ~spl3_5)),
% 1.38/0.56    inference(forward_demodulation,[],[f65,f51])).
% 1.38/0.56  fof(f65,plain,(
% 1.38/0.56    sK2 = k2_tarski(sK0,sK0) | ~spl3_5),
% 1.38/0.56    inference(avatar_component_clause,[],[f64])).
% 1.38/0.56  fof(f64,plain,(
% 1.38/0.56    spl3_5 <=> sK2 = k2_tarski(sK0,sK0)),
% 1.38/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 1.38/0.56  fof(f220,plain,(
% 1.38/0.56    ~spl3_1 | spl3_3 | spl3_5),
% 1.38/0.56    inference(avatar_contradiction_clause,[],[f219])).
% 1.38/0.56  fof(f219,plain,(
% 1.38/0.56    $false | (~spl3_1 | spl3_3 | spl3_5)),
% 1.38/0.56    inference(subsumption_resolution,[],[f90,f154])).
% 1.38/0.56  fof(f154,plain,(
% 1.38/0.56    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X0))) )),
% 1.38/0.56    inference(superposition,[],[f78,f23])).
% 1.38/0.56  fof(f23,plain,(
% 1.38/0.56    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.38/0.56    inference(cnf_transformation,[],[f1])).
% 1.38/0.56  fof(f1,axiom,(
% 1.38/0.56    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.38/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.38/0.56  fof(f78,plain,(
% 1.38/0.56    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.38/0.56    inference(unit_resulting_resolution,[],[f39,f31])).
% 1.38/0.56  fof(f31,plain,(
% 1.38/0.56    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 1.38/0.56    inference(cnf_transformation,[],[f11])).
% 1.38/0.56  fof(f11,plain,(
% 1.38/0.56    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 1.38/0.56    inference(ennf_transformation,[],[f3])).
% 1.38/0.56  fof(f3,axiom,(
% 1.38/0.56    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 1.38/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).
% 1.38/0.56  fof(f39,plain,(
% 1.38/0.56    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.38/0.56    inference(equality_resolution,[],[f26])).
% 1.38/0.56  fof(f26,plain,(
% 1.38/0.56    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.38/0.56    inference(cnf_transformation,[],[f15])).
% 1.38/0.56  fof(f15,plain,(
% 1.38/0.56    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.38/0.56    inference(flattening,[],[f14])).
% 1.38/0.56  fof(f14,plain,(
% 1.38/0.56    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.38/0.56    inference(nnf_transformation,[],[f2])).
% 1.38/0.56  fof(f2,axiom,(
% 1.38/0.56    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.38/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.38/0.56  fof(f90,plain,(
% 1.38/0.56    ~r1_tarski(sK2,k2_xboole_0(sK1,sK2)) | (~spl3_1 | spl3_3 | spl3_5)),
% 1.38/0.56    inference(forward_demodulation,[],[f86,f46])).
% 1.38/0.56  fof(f46,plain,(
% 1.38/0.56    k2_xboole_0(sK1,sK2) = k2_tarski(sK0,sK0) | ~spl3_1),
% 1.38/0.56    inference(avatar_component_clause,[],[f44])).
% 1.38/0.56  fof(f44,plain,(
% 1.38/0.56    spl3_1 <=> k2_xboole_0(sK1,sK2) = k2_tarski(sK0,sK0)),
% 1.38/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.38/0.56  fof(f86,plain,(
% 1.38/0.56    ~r1_tarski(sK2,k2_tarski(sK0,sK0)) | (spl3_3 | spl3_5)),
% 1.38/0.56    inference(unit_resulting_resolution,[],[f56,f66,f38])).
% 1.38/0.56  fof(f38,plain,(
% 1.38/0.56    ( ! [X0,X1] : (~r1_tarski(X0,k2_tarski(X1,X1)) | k1_xboole_0 = X0 | k2_tarski(X1,X1) = X0) )),
% 1.38/0.56    inference(definition_unfolding,[],[f28,f22,f22])).
% 1.38/0.56  fof(f28,plain,(
% 1.38/0.56    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 1.38/0.56    inference(cnf_transformation,[],[f17])).
% 1.38/0.56  fof(f17,plain,(
% 1.38/0.56    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.38/0.56    inference(flattening,[],[f16])).
% 1.38/0.56  fof(f16,plain,(
% 1.38/0.56    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.38/0.56    inference(nnf_transformation,[],[f6])).
% 1.38/0.56  fof(f6,axiom,(
% 1.38/0.56    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.38/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 1.38/0.56  fof(f66,plain,(
% 1.38/0.56    sK2 != k2_tarski(sK0,sK0) | spl3_5),
% 1.38/0.56    inference(avatar_component_clause,[],[f64])).
% 1.38/0.56  fof(f56,plain,(
% 1.38/0.56    k1_xboole_0 != sK2 | spl3_3),
% 1.38/0.56    inference(avatar_component_clause,[],[f54])).
% 1.38/0.56  fof(f54,plain,(
% 1.38/0.56    spl3_3 <=> k1_xboole_0 = sK2),
% 1.38/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.38/0.56  fof(f188,plain,(
% 1.38/0.56    ~spl3_3 | ~spl3_7 | spl3_8),
% 1.38/0.56    inference(avatar_contradiction_clause,[],[f187])).
% 1.38/0.56  fof(f187,plain,(
% 1.38/0.56    $false | (~spl3_3 | ~spl3_7 | spl3_8)),
% 1.38/0.56    inference(subsumption_resolution,[],[f186,f109])).
% 1.38/0.56  fof(f109,plain,(
% 1.38/0.56    k1_xboole_0 != k2_tarski(sK0,sK0) | spl3_8),
% 1.38/0.56    inference(avatar_component_clause,[],[f107])).
% 1.38/0.56  fof(f107,plain,(
% 1.38/0.56    spl3_8 <=> k1_xboole_0 = k2_tarski(sK0,sK0)),
% 1.38/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 1.38/0.56  fof(f186,plain,(
% 1.38/0.56    k1_xboole_0 = k2_tarski(sK0,sK0) | (~spl3_3 | ~spl3_7)),
% 1.38/0.56    inference(forward_demodulation,[],[f178,f74])).
% 1.38/0.56  fof(f74,plain,(
% 1.38/0.56    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 1.38/0.56    inference(unit_resulting_resolution,[],[f39,f24])).
% 1.38/0.56  fof(f24,plain,(
% 1.38/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 1.38/0.56    inference(cnf_transformation,[],[f10])).
% 1.38/0.56  fof(f10,plain,(
% 1.38/0.56    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.38/0.56    inference(ennf_transformation,[],[f4])).
% 1.38/0.56  fof(f4,axiom,(
% 1.38/0.56    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.38/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.38/0.56  fof(f178,plain,(
% 1.38/0.56    k2_tarski(sK0,sK0) = k2_xboole_0(k1_xboole_0,k1_xboole_0) | (~spl3_3 | ~spl3_7)),
% 1.38/0.56    inference(backward_demodulation,[],[f97,f55])).
% 1.38/0.56  fof(f55,plain,(
% 1.38/0.56    k1_xboole_0 = sK2 | ~spl3_3),
% 1.38/0.56    inference(avatar_component_clause,[],[f54])).
% 1.38/0.56  fof(f97,plain,(
% 1.38/0.56    k2_tarski(sK0,sK0) = k2_xboole_0(k1_xboole_0,sK2) | ~spl3_7),
% 1.38/0.56    inference(avatar_component_clause,[],[f95])).
% 1.38/0.56  fof(f95,plain,(
% 1.38/0.56    spl3_7 <=> k2_tarski(sK0,sK0) = k2_xboole_0(k1_xboole_0,sK2)),
% 1.38/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 1.38/0.56  fof(f172,plain,(
% 1.38/0.56    spl3_11),
% 1.38/0.56    inference(avatar_contradiction_clause,[],[f165])).
% 1.38/0.56  fof(f165,plain,(
% 1.38/0.56    $false | spl3_11),
% 1.38/0.56    inference(unit_resulting_resolution,[],[f136,f39,f80])).
% 1.38/0.56  fof(f80,plain,(
% 1.38/0.56    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X1,X0),X2) | r1_tarski(X0,X2)) )),
% 1.38/0.56    inference(superposition,[],[f31,f23])).
% 1.38/0.56  fof(f136,plain,(
% 1.38/0.56    ~r1_tarski(sK2,k2_xboole_0(k1_xboole_0,sK2)) | spl3_11),
% 1.38/0.56    inference(avatar_component_clause,[],[f134])).
% 1.38/0.56  fof(f134,plain,(
% 1.38/0.56    spl3_11 <=> r1_tarski(sK2,k2_xboole_0(k1_xboole_0,sK2))),
% 1.38/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 1.38/0.56  fof(f137,plain,(
% 1.38/0.56    ~spl3_11 | ~spl3_1 | spl3_3 | ~spl3_4 | spl3_5),
% 1.38/0.56    inference(avatar_split_clause,[],[f104,f64,f60,f54,f44,f134])).
% 1.38/0.56  fof(f60,plain,(
% 1.38/0.56    spl3_4 <=> k1_xboole_0 = sK1),
% 1.38/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.38/0.56  fof(f104,plain,(
% 1.38/0.56    ~r1_tarski(sK2,k2_xboole_0(k1_xboole_0,sK2)) | (~spl3_1 | spl3_3 | ~spl3_4 | spl3_5)),
% 1.38/0.56    inference(backward_demodulation,[],[f90,f61])).
% 1.38/0.56  fof(f61,plain,(
% 1.38/0.56    k1_xboole_0 = sK1 | ~spl3_4),
% 1.38/0.56    inference(avatar_component_clause,[],[f60])).
% 1.38/0.56  fof(f118,plain,(
% 1.38/0.56    spl3_7 | ~spl3_1 | ~spl3_4),
% 1.38/0.56    inference(avatar_split_clause,[],[f98,f60,f44,f95])).
% 1.38/0.56  fof(f98,plain,(
% 1.38/0.56    k2_tarski(sK0,sK0) = k2_xboole_0(k1_xboole_0,sK2) | (~spl3_1 | ~spl3_4)),
% 1.38/0.56    inference(backward_demodulation,[],[f46,f61])).
% 1.38/0.56  fof(f110,plain,(
% 1.38/0.56    ~spl3_8 | spl3_2 | ~spl3_4),
% 1.38/0.56    inference(avatar_split_clause,[],[f99,f60,f50,f107])).
% 1.38/0.56  fof(f99,plain,(
% 1.38/0.56    k1_xboole_0 != k2_tarski(sK0,sK0) | (spl3_2 | ~spl3_4)),
% 1.38/0.56    inference(backward_demodulation,[],[f52,f61])).
% 1.38/0.56  fof(f52,plain,(
% 1.38/0.56    sK1 != k2_tarski(sK0,sK0) | spl3_2),
% 1.38/0.56    inference(avatar_component_clause,[],[f50])).
% 1.38/0.56  fof(f93,plain,(
% 1.38/0.56    ~spl3_1 | spl3_2 | spl3_4),
% 1.38/0.56    inference(avatar_contradiction_clause,[],[f92])).
% 1.38/0.56  fof(f92,plain,(
% 1.38/0.56    $false | (~spl3_1 | spl3_2 | spl3_4)),
% 1.38/0.56    inference(subsumption_resolution,[],[f91,f78])).
% 1.38/0.56  fof(f91,plain,(
% 1.38/0.56    ~r1_tarski(sK1,k2_xboole_0(sK1,sK2)) | (~spl3_1 | spl3_2 | spl3_4)),
% 1.38/0.56    inference(forward_demodulation,[],[f85,f46])).
% 1.38/0.56  fof(f85,plain,(
% 1.38/0.56    ~r1_tarski(sK1,k2_tarski(sK0,sK0)) | (spl3_2 | spl3_4)),
% 1.38/0.56    inference(unit_resulting_resolution,[],[f62,f52,f38])).
% 1.38/0.56  fof(f62,plain,(
% 1.38/0.56    k1_xboole_0 != sK1 | spl3_4),
% 1.38/0.56    inference(avatar_component_clause,[],[f60])).
% 1.38/0.56  fof(f67,plain,(
% 1.38/0.56    ~spl3_4 | ~spl3_5),
% 1.38/0.56    inference(avatar_split_clause,[],[f33,f64,f60])).
% 1.38/0.56  fof(f33,plain,(
% 1.38/0.56    sK2 != k2_tarski(sK0,sK0) | k1_xboole_0 != sK1),
% 1.38/0.56    inference(definition_unfolding,[],[f20,f22])).
% 1.38/0.56  fof(f20,plain,(
% 1.38/0.56    sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1),
% 1.38/0.56    inference(cnf_transformation,[],[f13])).
% 1.38/0.56  fof(f57,plain,(
% 1.38/0.56    ~spl3_2 | ~spl3_3),
% 1.38/0.56    inference(avatar_split_clause,[],[f32,f54,f50])).
% 1.38/0.56  fof(f32,plain,(
% 1.38/0.56    k1_xboole_0 != sK2 | sK1 != k2_tarski(sK0,sK0)),
% 1.38/0.56    inference(definition_unfolding,[],[f21,f22])).
% 1.38/0.56  fof(f21,plain,(
% 1.38/0.56    k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)),
% 1.38/0.56    inference(cnf_transformation,[],[f13])).
% 1.38/0.56  fof(f47,plain,(
% 1.38/0.56    spl3_1),
% 1.38/0.56    inference(avatar_split_clause,[],[f35,f44])).
% 1.38/0.56  fof(f35,plain,(
% 1.38/0.56    k2_xboole_0(sK1,sK2) = k2_tarski(sK0,sK0)),
% 1.38/0.56    inference(definition_unfolding,[],[f18,f22])).
% 1.38/0.56  fof(f18,plain,(
% 1.38/0.56    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 1.38/0.56    inference(cnf_transformation,[],[f13])).
% 1.38/0.56  % SZS output end Proof for theBenchmark
% 1.38/0.56  % (11666)------------------------------
% 1.38/0.56  % (11666)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.56  % (11666)Termination reason: Refutation
% 1.38/0.56  
% 1.38/0.56  % (11666)Memory used [KB]: 10746
% 1.38/0.56  % (11666)Time elapsed: 0.144 s
% 1.38/0.56  % (11666)------------------------------
% 1.38/0.56  % (11666)------------------------------
% 1.58/0.57  % (11645)Success in time 0.195 s
%------------------------------------------------------------------------------
